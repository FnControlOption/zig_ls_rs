#![allow(unused)]

use std::borrow::Cow;
use std::fmt::Write;
use std::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Duration;

use async_lsp::client_monitor::ClientProcessMonitorLayer;
use async_lsp::concurrency::ConcurrencyLayer;
use async_lsp::panic::CatchUnwindLayer;
use async_lsp::router::Router;
use async_lsp::server::LifecycleLayer;
use async_lsp::tracing::TracingLayer;
use async_lsp::{ClientSocket, ErrorCode, ResponseError};
use lsp_types::DidChangeTextDocumentParams;
use lsp_types::DidCloseTextDocumentParams;
use lsp_types::DidOpenTextDocumentParams;
use lsp_types::TextDocumentContentChangeEvent;
use lsp_types::TextDocumentSyncCapability;
use lsp_types::TextDocumentSyncKind;
use lsp_types::{
    Hover, HoverContents, HoverParams, HoverProviderCapability, InitializeResult, MarkedString,
    MessageType, OneOf, Position, ServerCapabilities, ShowMessageParams, Url, notification,
    request,
};
use tower::ServiceBuilder;
use tracing::{Level, info};
use zig_analyzer::*;
use zig_ast::*;

struct Server {
    client: ClientSocket,
    ip: InternPool,
    cache: AnalyzerCache,
    documents: DocumentStore,
    env: Env,
}

impl Server {
    fn analyzer(&mut self, this: Node) -> Analyzer<'_, '_, '_, '_> {
        Analyzer {
            ip: &mut self.ip,
            cache: &mut self.cache,
            documents: &mut self.documents,
            std_dir: Some(&self.env.std_dir),
            this,
        }
    }

    fn open(&mut self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let Ok(path) = uri.to_file_path() else {
            return;
        };
        let path = Rc::from(path);
        let source = params.text_document.text.into_bytes();
        self.documents.parse(path, Some(source));
        self.cache.clear();
    }

    fn change(&mut self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let Ok(path) = uri.to_file_path() else {
            return;
        };
        let path = Rc::from(path);
        let event = params.content_changes.into_iter().next().unwrap();
        assert!(event.range.is_none());
        let source = event.text.into_bytes();
        self.documents.parse(path, Some(source));
        self.cache.clear();
    }

    fn hover(&mut self, params: HoverParams) -> Result<Option<String>, ResponseError> {
        let uri = params.text_document_position_params.text_document.uri;
        let Ok(path) = uri.to_file_path() else {
            let msg = format!("invalid file path: {uri}");
            return Err(ResponseError::new(ErrorCode::REQUEST_FAILED, msg));
        };

        let path = Rc::<Path>::from(path);
        let Some(document) = self.documents.get_or_parse(path.clone()) else {
            let msg = format!("failed to parse file: {}", path.display());
            return Err(ResponseError::new(ErrorCode::REQUEST_FAILED, msg));
        };

        let tree = document.tree().clone();
        let Position { line, character } = params.text_document_position_params.position;
        let token_index = document.position_to_token_index(line, character);
        let Some(container) = document.enclosing_container(token_index) else {
            let msg = format!("failed to find enclosing container at ({line}, {character})");
            return Err(ResponseError::new(ErrorCode::REQUEST_FAILED, msg));
        };
        let doc_node = document.enclosing_nodes(token_index).last().unwrap();

        let handle = Handle(path.clone(), tree.clone());
        let this = Node(handle.clone(), container.index);
        let node = Node(handle.clone(), doc_node.index);

        let (mut def, expr) = match tree.node_tag(node.index()) {
            NodeTag::Identifier => {
                let name_token = tree.node_main_token(node.index());
                if token_index != name_token {
                    return Ok(None);
                }
                let mut analyzer = self.analyzer(this);
                let mut member = None;
                let binding = analyzer.resolve_identifier(&node, Some(&mut member));
                let def = match member {
                    Some(member) => member.def_slice(&tree),
                    None => tree.token_slice(token_index),
                };
                (Cow::Borrowed(def), binding.expr())
            }
            NodeTag::GlobalVarDecl
            | NodeTag::LocalVarDecl
            | NodeTag::SimpleVarDecl
            | NodeTag::AlignedVarDecl => {
                let mut_token = tree.node_main_token(node.index());
                let name_token = TokenIndex(mut_token.0 + 1);
                if token_index != name_token {
                    return Ok(None);
                }
                let member = Member::Variable(node.index());
                let def = member.def_slice(&tree);
                let mut analyzer = self.analyzer(this);
                let binding = analyzer.resolve_decl_access_this(member);
                (Cow::Borrowed(def), binding.expr())
            }
            NodeTag::FnProtoSimple
            | NodeTag::FnProtoMulti
            | NodeTag::FnProtoOne
            | NodeTag::FnProto
            | NodeTag::FnDecl => 'blk: {
                let fn_token = tree.node_main_token(node.index());
                let name_token = TokenIndex(fn_token.0 + 1);
                if token_index == name_token {
                    let member = Member::Function(node.index());
                    let def = member.def_slice(&tree);
                    let mut analyzer = self.analyzer(this);
                    let binding = analyzer.resolve_decl_access_this(member);
                    break 'blk (Cow::Borrowed(def), binding.expr());
                }
                let colon_token = TokenIndex(token_index.0 + 1);
                let param_token = TokenIndex(token_index.0 + 2);
                if tree.token_count() >= param_token.0
                    && tree.token_tag(token_index) == TokenTag::Identifier
                    && tree.token_tag(colon_token) == TokenTag::Colon
                {
                    let mut opt_param = None;
                    for sub_node in doc_node.enclosing_nodes(&tree, param_token) {
                        if tree.first_token(sub_node.index) == param_token {
                            opt_param = Some(sub_node.index);
                            break;
                        }
                    }
                    let Some(param) = opt_param else {
                        let def = tree.token_slice(token_index);
                        let expr = Expr(Type::Unknown, Value::Unknown);
                        break 'blk (Cow::Borrowed(def), expr);
                    };
                    let member = Member::FunctionParameter(param);
                    let def = member.def_slice(&tree);
                    let mut analyzer = self.analyzer(this);
                    let binding = analyzer.resolve_decl_access_this(member);
                    break 'blk (Cow::Borrowed(def), binding.expr());
                }
                return Ok(None);
            }
            NodeTag::ContainerFieldInit
            | NodeTag::ContainerFieldAlign
            | NodeTag::ContainerField => {
                let name_token = tree.node_main_token(node.index());
                if token_index != name_token {
                    return Ok(None);
                }
                let member = Member::Field(node.index());
                let def = member.def_slice(&tree);
                let mut analyzer = self.analyzer(this);
                let expr = analyzer.resolve_field_access_this(Value::Unknown, node.index());
                (Cow::Borrowed(def), expr)
            }
            NodeTag::FieldAccess => {
                let NodeAndToken(lhs, rhs) = unsafe { tree.node_data_unchecked(node.index()) };
                if token_index != rhs {
                    return Ok(None);
                }
                let mut analyzer = self.analyzer(this);
                let mut member_info = None;
                let binding = analyzer.resolve_member_access(&node, Some(&mut member_info));
                match member_info {
                    Some((tree, member)) => {
                        let def = Vec::from(member.def_slice(&tree));
                        (Cow::Owned(def), binding.expr())
                    }
                    None => {
                        let def = tree.token_slice(token_index);
                        (Cow::Borrowed(def), binding.expr())
                    }
                }
            }
            _ => return Ok(None),
        };

        if let Expr(Type::Type, Value::Type(Type::Interned(index))) = expr
            && let Some(InternedType::Container(container_type)) = self.ip.get_type(index)
        {
            def = Cow::Borrowed(container_type.source());
        }

        let mut s = String::new();
        let def = String::from_utf8_lossy(&def);
        let _ = write!(s, "```zig\n{def}\n```\n");
        match expr {
            Expr(Type::Type, _) => {
                s.push_str("```zig\n(type)\n```\n");
            }
            Expr(ty, Value::Runtime | Value::Unknown | Value::Type(Type::Unknown)) => {
                let ty = ty.display(&self.ip);
                let _ = write!(s, "```zig\n({ty})\n```\n");
            }
            Expr(ty, val) => {
                let ty = ty.display(&self.ip);
                let val = val.display(&self.ip);
                let _ = write!(s, "```zig\n({ty} = {val})\n```\n",);
            }
        }
        Ok(Some(s))
    }
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.len() > 1 && &args[1..] == ["--version"] {
        println!("0.15.2");
        return;
    }

    let (server, _) = async_lsp::MainLoop::new_server(|client| {
        let mut router = Router::new(Server {
            client: client.clone(),
            ip: InternPool::new(),
            cache: AnalyzerCache::new(),
            documents: DocumentStore::new(),
            env: Env::find().unwrap(),
        });
        router
            .request::<request::Initialize, _>(|_, params| async move {
                Ok(InitializeResult {
                    capabilities: ServerCapabilities {
                        hover_provider: Some(HoverProviderCapability::Simple(true)),
                        // definition_provider: Some(OneOf::Left(true)),
                        text_document_sync: Some(TextDocumentSyncCapability::Kind(
                            TextDocumentSyncKind::FULL,
                        )),
                        ..ServerCapabilities::default()
                    },
                    server_info: None,
                })
            })
            .request::<request::HoverRequest, _>(|server, params| {
                let result = server.hover(params);
                async move {
                    let Some(s) = result? else {
                        return Ok(None);
                    };
                    let contents = HoverContents::Scalar(MarkedString::String(s));
                    let range = None;
                    Ok(Some(Hover { contents, range }))
                }
            })
            .request::<request::GotoDefinition, _>(|_, _| async {
                let msg = "Not yet implemented!";
                Err(ResponseError::new(ErrorCode::REQUEST_FAILED, msg))
            })
            .request::<request::Shutdown, _>(|_, _| async { Ok(()) })
            .notification::<notification::Initialized>(|_, _| ControlFlow::Continue(()))
            .notification::<notification::DidChangeConfiguration>(|_, _| ControlFlow::Continue(()))
            .notification::<notification::DidOpenTextDocument>(|server, params| {
                server.open(params);
                ControlFlow::Continue(())
            })
            .notification::<notification::DidChangeTextDocument>(|server, params| {
                server.change(params);
                ControlFlow::Continue(())
            })
            .notification::<notification::DidCloseTextDocument>(|_, _| ControlFlow::Continue(()))
            .notification::<notification::DidSaveTextDocument>(|_, _| ControlFlow::Continue(()))
            .notification::<notification::WillSaveTextDocument>(|_, _| ControlFlow::Continue(()))
            .notification::<notification::Exit>(|_, _| ControlFlow::Continue(()));

        ServiceBuilder::new()
            .layer(TracingLayer::default())
            .layer(LifecycleLayer::default())
            .layer(CatchUnwindLayer::default())
            .layer(ConcurrencyLayer::default())
            .layer(ClientProcessMonitorLayer::new(client))
            .service(router)
    });

    tracing_subscriber::fmt()
        .with_max_level(Level::INFO)
        .with_ansi(false)
        .with_writer(std::io::stderr)
        .init();

    // Prefer truly asynchronous piped stdin/stdout without blocking tasks.
    #[cfg(unix)]
    let (stdin, stdout) = (
        async_lsp::stdio::PipeStdin::lock_tokio().unwrap(),
        async_lsp::stdio::PipeStdout::lock_tokio().unwrap(),
    );
    // Fallback to spawn blocking read/write otherwise.
    #[cfg(not(unix))]
    let (stdin, stdout) = (
        tokio_util::compat::TokioAsyncReadCompatExt::compat(tokio::io::stdin()),
        tokio_util::compat::TokioAsyncWriteCompatExt::compat_write(tokio::io::stdout()),
    );

    server.run_buffered(stdin, stdout).await.unwrap();
}
