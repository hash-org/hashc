//! Module that implements the [AstVisitor] pattern for the
//! [Builder]. Most of these functions aren't used since the
//! vast majority of the code is working to simplify a particular
//! constant declaration or a function body.

use hash_ast::visitor::AstVisitor;

use crate::builder::Builder;
