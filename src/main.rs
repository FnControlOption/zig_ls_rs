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
use lsp_types::GotoDefinitionParams;
use lsp_types::Location;
use lsp_types::Range;
use lsp_types::TextDocumentContentChangeEvent;
use lsp_types::TextDocumentPositionParams;
use lsp_types::TextDocumentSyncCapability;
use lsp_types::TextDocumentSyncKind;
use lsp_types::request::GotoTypeDefinitionResponse;
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
    fn analyzer(&mut self) -> Analyzer<'_, '_, '_, '_> {
        Analyzer {
            ip: &mut self.ip,
            cache: &mut self.cache,
            documents: &mut self.documents,
            std_dir: Some(&self.env.std_dir),
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

    fn get_enclosing(
        &mut self,
        params: TextDocumentPositionParams,
    ) -> Result<(Node, TokenIndex), ResponseError> {
        let uri = params.text_document.uri;
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
        let Position { line, character } = params.position;
        const PREFERRED_TOKENS: &[TokenTag] =
            &[TokenTag::Identifier, TokenTag::Builtin, TokenTag::Period];
        let token_index = document.position_to_token(line, character, PREFERRED_TOKENS);
        let Some(container) = document.enclosing_container(token_index) else {
            let msg = format!("failed to find enclosing container at ({line}, {character})");
            return Err(ResponseError::new(ErrorCode::REQUEST_FAILED, msg));
        };
        let Some(doc_node) = container.enclosing_nodes(&tree, token_index).last() else {
            let msg = format!("failed to find enclosing node at ({line}, {character})");
            return Err(ResponseError::new(ErrorCode::REQUEST_FAILED, msg));
        };

        let handle = Handle(path.clone(), tree.clone());
        let node = Node(handle.clone(), doc_node.index);

        Ok((node, token_index))
    }

    fn hover(&mut self, params: HoverParams) -> Result<Option<String>, ResponseError> {
        let (node, token_index) = self.get_enclosing(params.text_document_position_params)?;

        let mut analyzer = self.analyzer();
        let mut member_info = None;
        let opt_expr = analyzer.resolve_from_token(&node, token_index, Some(&mut member_info));
        let Some(expr) = opt_expr else {
            return Ok(None);
        };

        let mut handle = node.handle().clone();
        let def = 'blk: {
            if let Expr(Type::Type, Value::Type(Type::Interned(index))) = expr
                && let Some(InternedType::Container(container_type)) = self.ip.get_type(index)
            {
                let node = container_type.this();
                handle = node.handle().clone();
                let tree = handle.tree();
                break 'blk tree.node_source(node.index());
            }

            match member_info {
                Some((member_handle, member)) => {
                    handle = member_handle;
                    let tree = handle.tree();
                    member.def_slice(tree)
                }
                None => {
                    let tree = handle.tree();
                    tree.token_slice(token_index)
                }
            }
        };

        let mut s = String::new();
        let def = String::from_utf8_lossy(def);
        let _ = write!(s, "```zig\n{def}\n```\n");
        match expr {
            Expr(Type::Type, _) => {
                s.push_str("```zig\n(type)\n```\n");
            }
            Expr(ty, Value::Runtime | Value::Unknown | Value::Type(Type::Unknown)) => {
                let _ = write!(s, "```zig\n({})\n```\n", ty.display(&self.ip));
            }
            Expr(ty, Value::Interned(index))
                if let Some(InternedValue::Function(_)) = self.ip.get_value(index) =>
            {
                let _ = write!(s, "```zig\n({})\n```\n", ty.display(&self.ip));
            }
            Expr(ty, val) => {
                let ty = ty.display(&self.ip);
                let val = val.display(&self.ip);
                let _ = write!(s, "```zig\n({ty} = {val})\n```\n");
            }
        }
        Ok(Some(s))
    }

    fn goto_definition(
        &mut self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoTypeDefinitionResponse>, ResponseError> {
        let (node, token_index) = self.get_enclosing(params.text_document_position_params)?;

        let mut analyzer = self.analyzer();
        let mut member_info = None;
        let opt_expr = analyzer.resolve_from_token(&node, token_index, Some(&mut member_info));
        let Some(expr) = opt_expr else {
            return Ok(None);
        };

        let (handle, token) = 'blk: {
            if let Expr(Type::Type, Value::Type(Type::Interned(index))) = expr
                && let Some(InternedType::Container(container_type)) = self.ip.get_type(index)
            {
                let node = container_type.this();
                let handle = node.handle().clone();
                let tree = handle.tree();
                let token = tree.first_token(node.index());
                break 'blk (handle, token);
            }

            let Some((handle, member)) = member_info else {
                return Ok(None);
            };

            let tree = handle.tree();
            let token = member.name_token(tree);
            (handle, token)
        };

        let Handle(path, tree) = handle;
        let Ok(uri) = Url::from_file_path(&path) else {
            let msg = format!("invalid file path: {}", path.display());
            return Err(ResponseError::new(ErrorCode::REQUEST_FAILED, msg));
        };
        let location = tree.token_location(token);
        let line = u32::try_from(location.line).unwrap();
        let character = u32::try_from(location.column).unwrap();
        let start = Position::new(line, character);
        let end = start; // TODO
        let range = Range::new(start, end);
        let location = Location::new(uri, range);
        Ok(Some(GotoTypeDefinitionResponse::Scalar(location)))
    }
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.len() > 1 && &args[1..] == ["--version"] {
        println!("0.16.0");
        return;
    }

    let (server, _) = async_lsp::MainLoop::new_server(|client| {
        let mut router = Router::new(Server {
            client: client.clone(),
            ip: InternPool::new(),
            cache: AnalyzerCache::new(),
            documents: DocumentStore::new(),
            env: Env::find().expect("unable to find Zig"),
        });
        router
            .request::<request::Initialize, _>(|_, params| async {
                Ok(InitializeResult {
                    capabilities: ServerCapabilities {
                        hover_provider: Some(HoverProviderCapability::Simple(true)),
                        definition_provider: Some(OneOf::Left(true)),
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
                async {
                    let Some(s) = result? else {
                        return Ok(None);
                    };
                    let contents = HoverContents::Scalar(MarkedString::String(s));
                    let range = None;
                    Ok(Some(Hover { contents, range }))
                }
            })
            .request::<request::GotoDefinition, _>(|server, params| {
                let result = server.goto_definition(params);
                async { result }
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
