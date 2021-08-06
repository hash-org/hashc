use crate::ast::*;

pub trait NodeCount {
    fn children_count(&self) -> usize;
    fn node_count(&self) -> usize {
        1 + self.children_count()
    }
}

impl<T: NodeCount> NodeCount for Option<T> {
    fn children_count(&self) -> usize {
        match self {
            None => 0,
            Some(ref node) => node.children_count(),
        }
    }

    fn node_count(&self) -> usize {
        match self {
            None => 0,
            Some(ref node) => node.node_count(),
        }
    }
}

impl<T: NodeCount> NodeCount for AstNode<'_, T> {
    fn children_count(&self) -> usize {
        self.body().children_count()
    }
}

impl NodeCount for Statement<'_> {
    fn children_count(&self) -> usize {
        match &self {
            Statement::Expr(k) => k.node_count(),
            Statement::Return(k) => k.node_count(),
            Statement::Block(block) => block.node_count(),
            Statement::Break => 0,
            Statement::Continue => 0,
            Statement::Let(ref statement) => {
                statement.pattern.node_count()
                    + statement.ty.node_count()
                    + statement.bound.node_count()
                    + statement.value.node_count()
            }
            Statement::Assign(assign) => assign.lhs.node_count() + assign.rhs.node_count(),
            Statement::StructDef(defn) => {
                let entries: usize = defn.entries.iter().map(|entry| entry.node_count()).sum();

                1 + defn.bound.node_count() + entries
            }
            Statement::EnumDef(defn) => {
                let entries: usize = defn.entries.iter().map(|entry| entry.node_count()).sum();

                1 + defn.bound.node_count() + entries
            }
            Statement::TraitDef(defn) => 1 + defn.bound.node_count() + defn.trait_type.node_count(),
        }
    }
}

impl NodeCount for BodyBlock<'_> {
    fn children_count(&self) -> usize {
        let arg_count: usize = self.statements.iter().map(|s| s.node_count()).sum();
        arg_count + self.expr.node_count()
    }
}

impl NodeCount for Block<'_> {
    fn children_count(&self) -> usize {
        match &self {
            Block::Match(match_block) => {
                let cases: usize = match_block.cases.iter().map(|c| c.node_count()).sum();
                match_block.subject.node_count() + cases
            }
            Block::Loop(loop_block) => loop_block.node_count(),
            Block::Body(body_block) => body_block.node_count(),
        }
    }
}

impl NodeCount for Expression<'_> {
    fn children_count(&self) -> usize {
        match self.kind() {
            ExpressionKind::FunctionCall(e) => {
                let fn_args: usize = e.args.entries.iter().map(|a| a.node_count()).sum();
                e.subject.node_count() + fn_args
            }
            ExpressionKind::Intrinsic(_) => 0,
            ExpressionKind::Variable(e) => {
                let ty_args: usize = e.type_args.iter().map(|t| t.node_count()).sum();

                e.name.node_count() + ty_args
            }
            ExpressionKind::PropertyAccess(e) => e.subject.node_count() + 1,
            ExpressionKind::LiteralExpr(e) => e.node_count(),
            ExpressionKind::Typed(e) => e.ty.node_count() + e.expr.node_count(),
            ExpressionKind::Block(e) => e.node_count(),
            ExpressionKind::Deref(e) => e.node_count(),
            ExpressionKind::Ref(e) => e.node_count(),
            ExpressionKind::Import(_) => 0,
        }
    }
}

impl NodeCount for Literal<'_> {
    fn children_count(&self) -> usize {
        match &self {
            // count string, number, char literals as zero since they are wrapped in AstNode and should count
            // as only a single node instead of 2.
            Literal::Str(_) => 0,
            Literal::Char(_) => 0,
            Literal::Int(_) => 0,
            Literal::Float(_) => 0,
            Literal::Set(l) => l.elements.iter().map(|e| e.node_count()).sum(),
            Literal::Map(l) => l
                .elements
                .iter()
                .map(|(lhs, rhs)| lhs.node_count() + rhs.node_count())
                .sum(),
            Literal::List(l) => l.elements.iter().map(|e| e.node_count()).sum(),
            Literal::Tuple(l) => l.elements.iter().map(|e| e.node_count()).sum(),
            Literal::Struct(l) => {
                let type_args: usize = l.type_args.iter().map(|e| e.node_count()).sum();

                // map over StructLiteral entries which are made of a Name (1 node) and an expression
                let entries: usize = l.entries.iter().map(|e| 1 + e.value.node_count()).sum();

                l.name.node_count() + type_args + entries
            }
            Literal::Function(l) => {
                let fn_args: usize = l.args.iter().map(|arg| arg.ty.node_count() + 1).sum();

                fn_args + l.return_ty.node_count() + l.fn_body.node_count()
            }
        }
    }
}

impl NodeCount for MatchCase<'_> {
    fn children_count(&self) -> usize {
        self.pattern.node_count() + self.expr.node_count()
    }
}

impl NodeCount for Pattern<'_> {
    fn children_count(&self) -> usize {
        match &self {
            Pattern::Enum(pat) => {
                let arg_count: usize = pat.args.iter().map(|s| s.node_count()).sum();
                pat.name.node_count() + arg_count
            }
            Pattern::Struct(pat) => {
                let arg_count: usize = pat.entries.iter().map(|s| s.node_count()).sum();

                pat.name.node_count() + arg_count
            }
            Pattern::Namespace(pat) => pat.patterns.iter().map(|p| p.node_count()).sum(),
            Pattern::Tuple(pat) => pat.elements.iter().map(|e| e.node_count()).sum(),
            Pattern::Literal(_) => 0,
            Pattern::Or(pat) => pat.variants.iter().map(|e| e.node_count()).sum(),
            Pattern::If(pat) => {
                let count = pat.pattern.node_count();
                count + pat.condition.node_count()
            }
            Pattern::Binding(_) => 0,
            Pattern::Ignore => 0,
        }
    }
}

impl NodeCount for DestructuringPattern<'_> {
    fn children_count(&self) -> usize {
        1 + self.pattern.node_count()
    }
}

impl NodeCount for StructDefEntry<'_> {
    fn children_count(&self) -> usize {
        self.ty.node_count() + self.default.node_count()
    }
}

impl NodeCount for EnumDefEntry<'_> {
    fn children_count(&self) -> usize {
        self.args.iter().map(|t| t.node_count()).sum()
    }
}
impl NodeCount for Bound<'_> {
    fn children_count(&self) -> usize {
        let args_count: usize = self.type_args.iter().map(|t| t.node_count()).sum();
        let bound_count: usize = self.trait_bounds.iter().map(|t| t.node_count()).sum();

        args_count + bound_count
    }
}

impl NodeCount for TraitBound<'_> {
    fn children_count(&self) -> usize {
        let count = self.name.node_count();
        let args_count: usize = self.type_args.iter().map(|t| t.node_count()).sum();

        count + args_count
    }
}

impl NodeCount for Type<'_> {
    fn children_count(&self) -> usize {
        match &self {
            Type::Named(ty) => {
                let arg_count: usize = ty.type_args.iter().map(|t| t.node_count()).sum();

                ty.name.node_count() + arg_count
            }

            // TypeVar variant just counts for one<'_> node since it just wrapper for Name<'_>,
            // which is of made of a single AstNode.
            _ => 0,
        }
    }
}

impl NodeCount for AccessName {
    fn children_count(&self) -> usize {
        1
    }
}
