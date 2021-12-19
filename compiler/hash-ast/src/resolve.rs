//! Hash Compiler module resolving logic
//!
//! All rights reserved 2021 (c) The Hash Language authors

use crate::{
    error::ImportError,
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

pub trait ModuleResolver: Clone {
    fn module_source(&self) -> Option<&str>;
    fn module_index(&self) -> Option<ModuleIdx>;
    fn add_module(
        &self,
        import_path: impl AsRef<Path>,
        location: Option<SourceLocation>,
    ) -> Result<ModuleIdx, ImportError>;
}

#[derive(Debug, Copy, Clone, Constructor)]
pub(crate) struct ModuleParsingContext<'mod_ctx> {
    source: Option<&'mod_ctx str>,
    root_dir: &'mod_ctx Path,
    index: Option<ModuleIdx>,
}

#[derive(Debug)]
pub struct ParModuleResolver<'c, 'ctx, 'mod_ctx, 'scope, 'scope_ref, B> {
    ctx: ParsingContext<'c, 'ctx, B>,
    module_ctx: ModuleParsingContext<'mod_ctx>,
    scope: &'scope_ref Scope<'scope>,
}

impl<B> Clone for ParModuleResolver<'_, '_, '_, '_, '_, B> {
    fn clone(&self) -> Self {
        Self {
            ctx: self.ctx,
            module_ctx: self.module_ctx,
            scope: self.scope,
        }
    }
}

impl<'c, 'ctx, 'mod_ctx, 'scope, 'scope_ref, B>
    ParModuleResolver<'c, 'ctx, 'mod_ctx, 'scope, 'scope_ref, B>
{
    pub(crate) fn new(
        ctx: ParsingContext<'c, 'ctx, B>,
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

impl<'c, 'ctx, 'mod_ctx, 'scope, 'scope_ref, B> ModuleResolver
    for ParModuleResolver<'c, 'ctx, 'mod_ctx, 'scope, 'scope_ref, B>
where
    B: ParserBackend<'c>,
    'c: 'ctx,
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
        &self,
        import_path: impl AsRef<Path>,
        location: Option<SourceLocation>,
    ) -> Result<ModuleIdx, ImportError> {
        let resolved_import_path = resolve_path(import_path, &self.module_ctx.root_dir, location)?;
        let import_index = self.ctx.module_builder.reserve_index();

        // Copy ctx so that it can be moved into the closure independent of self.
        let ctx = self.ctx;

        self.scope.spawn(move |scope| {
            ctx.error_handler.handle_error(move || {
                // Get source and root directory of import
                let import_source = fs::read_to_string(&resolved_import_path)
                    .map_err(|e| (e, resolved_import_path.to_owned()));

                if let Err((err, path)) = import_source {
                    let import_err: ImportError = (err, path).into();

                    return Err(import_err.into());
                }

                let import_source = import_source.unwrap();
                let import_root_dir = resolved_import_path.parent().unwrap().to_owned();

                // Create a module parsing context and resolver for the import
                let import_module_ctx = ModuleParsingContext::new(
                    Some(&import_source),
                    &import_root_dir,
                    Some(import_index),
                );

                let import_resolver = ParModuleResolver::new(ctx, import_module_ctx, scope);

                // Parse the import
                let import_node = timed(
                    || {
                        ctx.backend.parse_module(
                            import_resolver,
                            &resolved_import_path,
                            &import_source,
                        )
                    },
                    Level::Debug,
                    |elapsed| println!("ast: {:.2?}", elapsed),
                );

                // @@Cleanup:
                // @@Hack: we still need to add the contents of the file into the file map whilst the parser
                //         is parsing. If we don't do this, the reporting crate won't be able to access the
                //         contents of the file for reporting purposes.
                ctx.module_builder
                    .add_contents(import_index, resolved_import_path, import_source);

                match import_node {
                    Ok(module) => {
                        ctx.module_builder.add_module_at(import_index, module); // Add the import to modules
                        Ok(())
                    }
                    Err(err) => Err(err),
                }
            });
        });

        Ok(import_index)
    }
}
