//! Hash Compiler module resolving logic
//!
//! All rights reserved 2021 (c) The Hash Language authors

use crate::{
    error::ParseResult,
    fs::resolve_path,
    location::SourceLocation,
    module::ModuleIdx,
    parse::{ParserBackend, ParsingContext},
};
use derive_more::Constructor;
use hash_utils::timed;
use log::Level;
use rayon::Scope;
use std::{fs, path::Path};

pub trait ModuleResolver {
    fn module_source(&self) -> Option<&str>;
    fn module_index(&self) -> Option<ModuleIdx>;
    fn add_module(
        &mut self,
        import_path: impl AsRef<Path>,
        location: Option<SourceLocation>,
    ) -> ParseResult<ModuleIdx>;
}

#[derive(Debug, Copy, Clone, Constructor)]
pub(crate) struct ModuleParsingContext<'mod_ctx> {
    source: Option<&'mod_ctx str>,
    root_dir: &'mod_ctx Path,
    index: Option<ModuleIdx>,
}

#[derive(Debug)]
pub struct ParModuleResolver<'ctx, 'mod_ctx, 'scope, 'scope_ref, B> {
    ctx: ParsingContext<'ctx, B>,
    module_ctx: ModuleParsingContext<'mod_ctx>,
    scope: &'scope_ref Scope<'scope>,
}

impl<'ctx, 'mod_ctx, 'scope, 'scope_ref, B>
    ParModuleResolver<'ctx, 'mod_ctx, 'scope, 'scope_ref, B>
{
    pub(crate) fn new(
        ctx: ParsingContext<'ctx, B>,
        module_ctx: ModuleParsingContext<'mod_ctx>,
        scope: &'scope_ref Scope<'scope>,
    ) -> Self {
        Self {
            ctx,
            module_ctx,
            scope,
        }
    }
}

impl<'ctx, 'mod_ctx, 'scope, 'scope_ref, B> ModuleResolver
    for ParModuleResolver<'ctx, 'mod_ctx, 'scope, 'scope_ref, B>
where
    B: ParserBackend,
    'ctx: 'scope,
    'scope: 'scope_ref,
{
    fn module_source(&self) -> Option<&str> {
        self.module_ctx.source
    }

    fn module_index(&self) -> Option<ModuleIdx> {
        self.module_ctx.index
    }

    fn add_module(
        &mut self,
        import_path: impl AsRef<Path>,
        location: Option<SourceLocation>,
    ) -> ParseResult<ModuleIdx> {
        let resolved_import_path = resolve_path(import_path, &self.module_ctx.root_dir, location)?;
        let import_index = self.ctx.module_builder.reserve_index();

        // Copy ctx so that it can be moved into the closure independent of self.
        let ctx = self.ctx;

        self.scope.spawn(move |scope| {
            ctx.error_handler.handle_error(move || {
                // Get source and root directory of import
                let import_source = fs::read_to_string(&resolved_import_path)
                    .map_err(|e| (e, resolved_import_path.to_owned()))?;
                let import_root_dir = resolved_import_path.parent().unwrap().to_owned();

                // Create a module parsing context and resolver for the import
                let import_module_ctx = ModuleParsingContext::new(
                    Some(&import_source),
                    &import_root_dir,
                    Some(import_index),
                );
                let mut import_resolver = ParModuleResolver::new(ctx, import_module_ctx, scope);

                // Parse the import
                let import_node = timed(
                    || {
                        ctx.backend.parse_module(
                            &mut import_resolver,
                            &resolved_import_path,
                            &import_source,
                        )
                    },
                    Level::Debug,
                    |elapsed| println!("ast: {:.2?}", elapsed),
                )?;

                // Add the import to modules
                ctx.module_builder.add_module_at(
                    import_index,
                    resolved_import_path,
                    import_source,
                    import_node,
                );

                Ok(())
            });
        });

        Ok(import_index)
    }
}
