//! Functions to emit tree definitions, visitors, walkers, given a parsed
//! [`TreeDef`].

use convert_case::{Case, Casing};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::definitions::{
    EnumNodeDef, EnumNodeVariant, NodeFieldData, StructNodeDef, StructNodeField, TreeDef,
    TreeNodeDef, NODE_DEF_ATTR_NAME,
};

/// Suffix the given identifier with "Mut"/"_mut" etc as appropriate depending
/// on the flag `emit_mut` and casing `case`.
fn suffix_ident_mut(ident: impl ToString, emit_mut: bool, case: Case) -> syn::Ident {
    if emit_mut {
        let word = format!("{}_mut", ident.to_string());
        format_ident!("{}", word.to_case(case))
    } else {
        format_ident!("{}", ident.to_string().to_case(case))
    }
}

/// Emit a `mut` if the flag is on.
fn maybe_mut_prefix(emit_mut: bool) -> TokenStream {
    if emit_mut {
        quote! { mut }
    } else {
        quote! {}
    }
}

/// Emit a `&mut` if the flag is on, `&` otherwise.
fn ref_or_mut_ref(emit_mut: bool) -> TokenStream {
    if emit_mut {
        quote! { &mut }
    } else {
        quote! { & }
    }
}

/// Emit other items given in the [define_tree!](crate::define_tree) macro.
fn emit_other_items(def: &TreeDef) -> TokenStream {
    def.other_items.iter().map(|item| -> TokenStream { quote!(#item) }).collect()
}

/// Emit the type for the field `data`.
fn emit_node_field_data(data: &NodeFieldData, tree_def: &TreeDef) -> TokenStream {
    let node_type_name = &tree_def.opts.node_type_name;
    let nodes_type_name = &tree_def.opts.nodes_type_name;
    match data {
        NodeFieldData::Child { node_name } => {
            quote!(#node_type_name<#node_name>)
        }
        NodeFieldData::ChildList { node_name } => {
            quote!(#nodes_type_name<#node_name>)
        }
        NodeFieldData::OptionalChild { node_name } => {
            quote!(Option<#node_type_name<#node_name>>)
        }
        NodeFieldData::Other { ty } => quote!(#ty),
    }
}

/// Emit a struct node definition.
fn emit_struct_def(struct_def: &StructNodeDef, tree_def: &TreeDef) -> TokenStream {
    let rendered_fields = struct_def
        .fields
        .iter()
        .map(|field| {
            let field_data = emit_node_field_data(&field.data, tree_def);
            let StructNodeField { visibility, attrs, name, .. } = field;
            quote! {
                #(#attrs)*
                #visibility #name: #field_data
            }
        })
        .collect::<Vec<_>>();

    let StructNodeDef { visibility, attrs, name, .. } = struct_def;

    // Remove the #[tree_node] attribute
    let filtered_attrs = attrs.iter().filter(|attr| !attr.path.is_ident(NODE_DEF_ATTR_NAME));

    quote! {
        #(#filtered_attrs)*
        #visibility struct #name {
            #(#rendered_fields),*
        }
    }
}

/// Emit an enum node definition.
fn emit_enum_def(enum_def: &EnumNodeDef, tree_def: &TreeDef) -> TokenStream {
    let rendered_variants = enum_def
        .variants
        .iter()
        .map(|variant| {
            let EnumNodeVariant { attrs, name, variant_data } = variant;
            variant_data
                .as_ref()
                .map(|variant_data| {
                    let data = variant_data.iter().map(|data| emit_node_field_data(data, tree_def));
                    quote! { #(#attrs)* #name(#(#data),*) }
                })
                .unwrap_or_else(|| {
                    quote! { #(#attrs)* #name }
                })
        })
        .collect::<Vec<_>>();

    let EnumNodeDef { visibility, attrs, name, .. } = enum_def;

    // Remove the #[tree_node] attribute
    let filtered_attrs = attrs.iter().filter(|attr| !attr.path.is_ident(NODE_DEF_ATTR_NAME));

    quote! {
        #(#filtered_attrs)*
        #visibility enum #name {
            #(#rendered_variants),*
        }
    }
}

/// Emit all node definitions.
fn emit_node_defs(tree_def: &TreeDef) -> TokenStream {
    tree_def
        .nodes
        .values()
        .map(|node| match node {
            TreeNodeDef::EnumNodeDef(enum_def) => emit_enum_def(enum_def, tree_def),
            TreeNodeDef::StructNodeDef(struct_def) => emit_struct_def(struct_def, tree_def),
        })
        .collect()
}

/// Emit the visitor trait, depending on options and the `emit_mut` flag.
fn emit_visitor(tree_def: &TreeDef, emit_mut: bool) -> TokenStream {
    let visitor_name = if emit_mut {
        format_ident!("{}Mut", &tree_def.opts.visitor_trait_base_name)
    } else {
        tree_def.opts.visitor_trait_base_name.clone()
    };
    let node_ref_name = if emit_mut {
        format_ident!("{}Mut", &tree_def.opts.visitor_node_ref_base_type_name)
    } else {
        tree_def.opts.visitor_node_ref_base_type_name.clone()
    };

    let node_visitor_methods = tree_def.nodes.keys().map(|node_name| {
        let node_ret = format_ident!("{}Ret", node_name.to_string().to_case(Case::Pascal));
        let visit_node = format_ident!("visit_{}", node_name.to_string().to_case(Case::Snake));
        let self_param = if emit_mut { quote!(&mut self) } else { quote!(&self) };
        quote! {
            type #node_ret;
            fn #visit_node(#self_param, node: #node_ref_name<#node_name>) -> Result<Self::#node_ret, Self::Error>;
        }
    });

    quote! {
        pub trait #visitor_name: Sized {
            type Error;

            #(#node_visitor_methods)*
        }
    }
}

/// If the given `ty` represents a node, return the name of the node.
fn is_node_ty(ty: &syn::Type, tree_def: &TreeDef) -> Option<syn::Ident> {
    if let syn::Type::Path(path) = ty {
        if let Some(ident) = path.path.get_ident() {
            if tree_def.nodes.contains_key(ident) {
                return Some(ident.clone());
            }
        }
    }
    None
}

fn is_leaf_node(node_name: &syn::Ident, tree_def: &TreeDef) -> bool {
    let node = tree_def.nodes.get(node_name).unwrap();
    let field_matches = |field: &NodeFieldData| {
        matches!(
            &field,
            NodeFieldData::Other { ty } if is_node_ty(ty, tree_def).is_none()
        )
    };
    match node {
        TreeNodeDef::StructNodeDef(struct_def) => {
            struct_def.fields.is_empty()
                || struct_def.fields.iter().all(|data| field_matches(&data.data))
        }
        TreeNodeDef::EnumNodeDef(enum_def) => {
            enum_def.variants.is_empty()
                || enum_def.variants.iter().all(|variant| {
                    variant
                        .variant_data
                        .as_ref()
                        .map(|data| data.is_empty() || data.iter().all(field_matches))
                        .unwrap_or(true)
                })
        }
    }
}

/// Emit the walked type for the field `data`.
fn emit_walked_node_field_type(data: &NodeFieldData, tree_def: &TreeDef) -> (TokenStream, bool) {
    let get_child_ret = |child_name: &syn::Ident| {
        format_ident!("{}Ret", child_name.to_string().to_case(Case::Pascal))
    };
    match data {
        NodeFieldData::Child { node_name: child_name } => {
            let child_ret = get_child_ret(child_name);
            (quote! { V::#child_ret }, true)
        }
        NodeFieldData::ChildList { node_name: child_name } => {
            let child_ret = get_child_ret(child_name);
            (quote! { Vec<V::#child_ret> }, true)
        }
        NodeFieldData::OptionalChild { node_name: child_name } => {
            let child_ret = get_child_ret(child_name);
            (quote! { Option<V::#child_ret> }, true)
        }
        NodeFieldData::Other { ty } => {
            if let Some(child_name) = is_node_ty(ty, tree_def) {
                let child_ret = get_child_ret(&child_name);
                (quote! { V::#child_ret }, true)
            } else {
                (quote! { #ty }, false)
            }
        }
    }
}

/// Emit the walked type definition for the given struct node.
fn emit_walked_struct_type(
    struct_node: &StructNodeDef,
    tree_def: &TreeDef,
    visitor_name: &syn::Ident,
) -> Result<TokenStream, syn::Error> {
    let node_name = &struct_node.name;
    if is_leaf_node(node_name, tree_def) {
        return Ok(quote! {});
    }

    let fields = struct_node
        .fields
        .iter()
        .filter_map(|field| {
            let field_name = &field.name;
            let (field_type, is_node) = emit_walked_node_field_type(&field.data, tree_def);
            // Only emit the fields which have nodes in them.
            if is_node {
                Some(quote! {
                   pub #field_name: #field_type
                })
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    Ok(quote! {
        pub struct #node_name<V: super::#visitor_name> {
            #(#fields),*
         }
    })
}

/// Emit the walked type definition for the given enum node.
fn emit_walked_enum_type(
    enum_node: &EnumNodeDef,
    tree_def: &TreeDef,
    visitor_name: &syn::Ident,
) -> Result<TokenStream, syn::Error> {
    let node_name = &enum_node.name;
    if is_leaf_node(node_name, tree_def) {
        return Ok(quote! {});
    }
    let variants = enum_node
        .variants
        .iter()
        .map(|variant| -> Result<_, syn::Error> {
            let variant_name = &variant.name;

            // Transform data of enum variant
            let variant_data = variant
                .variant_data
                .as_ref()
                .map(|variant_data| -> Result<_, syn::Error> {
                    // Only emit the fields with nodes:
                    let fields = variant_data.iter().filter_map(|data| {
                        let (field_type, is_node) = emit_walked_node_field_type(data, tree_def);
                        if is_node {
                            Some(quote! {
                               #field_type
                            })
                        } else {
                            None
                        }
                    });
                    Ok(quote! {
                        (#(#fields),*)
                    })
                })
                .unwrap_or_else(|| Ok(quote! {}))?;

            Ok(quote! { #variant_name #variant_data })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(quote! {
        pub enum #node_name<V: super::#visitor_name> {
            #(#variants),*
        }
    })
}

/// Emit all walked types for the tree definition.
fn emit_walked_types(tree_def: &TreeDef, emit_mut: bool) -> Result<TokenStream, syn::Error> {
    let visitor_name =
        suffix_ident_mut(&tree_def.opts.visitor_trait_base_name, emit_mut, Case::Pascal);
    let walker_types = tree_def
        .nodes
        .values()
        .map(|node| match node {
            TreeNodeDef::EnumNodeDef(enum_node) => {
                emit_walked_enum_type(enum_node, tree_def, &visitor_name)
            }
            TreeNodeDef::StructNodeDef(struct_node) => {
                emit_walked_struct_type(struct_node, tree_def, &visitor_name)
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(quote! {
        #(#walker_types)*
    })
}

/// Represents an enum definition whose children are all singular (one data
/// member) and are all nodes. This is used to emit the `*_same_children` walker
/// function.
struct EnumSameChildren {
    children_names: Vec<syn::Ident>,
    children_variant_names: Vec<syn::Ident>,
}

/// Create an [EnumSameChildren] if the given enum node meets the conditions.
fn enum_variants_as_same_children(
    enum_def: &EnumNodeDef,
    tree_def: &TreeDef,
) -> Option<EnumSameChildren> {
    if is_leaf_node(&enum_def.name, tree_def) {
        return None;
    }
    let (children_names, children_variant_names): (Vec<_>, Vec<_>) = enum_def
        .variants
        .iter()
        .filter_map(|variant| {
            let data = variant.variant_data.as_ref()?;
            // Singular
            if data.len() != 1 {
                return None;
            }
            // A node (either a direct child or a "phantom" child with no wrapper)
            let member = &data.get(0).unwrap();
            match member {
                NodeFieldData::Child { node_name } => {
                    Some((node_name.clone(), variant.name.clone()))
                }
                NodeFieldData::Other { ty } => {
                    is_node_ty(ty, tree_def).map(|node_name| (node_name, variant.name.clone()))
                }
                _ => None,
            }
        })
        .unzip();

    // Ensure we covered all variants
    if children_names.len() == enum_def.variants.len() {
        Some(EnumSameChildren { children_names, children_variant_names })
    } else {
        None
    }
}

/// Emit the `*_same_children` walker function for the given enum node, if it
/// meets the conditions (see [EnumSameChildren]).
fn emit_walker_enum_function_same_children(
    enum_node: &EnumNodeDef,
    tree_def: &TreeDef,
    visitor_name: &syn::Ident,
    emit_mut: bool,
) -> Result<Option<TokenStream>, syn::Error> {
    let children = match enum_variants_as_same_children(enum_node, tree_def) {
        Some(children) => children,
        None => return Ok(None),
    };

    // Skip if empty
    if children.children_names.is_empty() {
        return Ok(None);
    }

    // where clause for all same return types
    let node_name = &enum_node.name;
    let conditions = children.children_names.iter().map(|child_name| {
        let child_ret = format_ident!("{}Ret", child_name);
        quote! {
            #child_ret = Ret
        }
    });

    // match arms
    let match_arms = children.children_variant_names.iter().map(|child_name| {
        quote! {
            #node_name::#child_name(r) => r
        }
    });

    let ref_or_mut = ref_or_mut_ref(emit_mut);
    let mut_var = maybe_mut_prefix(emit_mut);
    let node_ref_name =
        suffix_ident_mut(&tree_def.opts.visitor_node_ref_base_type_name, emit_mut, Case::Pascal);
    let walk_node_fn_name_same_children =
        format_ident!("walk_{}_same_children", node_name.to_string().to_case(Case::Snake),);
    let walk_node_fn_name = format_ident!("walk_{}", node_name.to_string().to_case(Case::Snake),);

    Ok(Some(quote! {
        pub fn #walk_node_fn_name_same_children<V: super::#visitor_name, Ret>(
            visitor: #ref_or_mut V,
            #mut_var node: super::#node_ref_name<super::#node_name>,
        ) -> Result<Ret, V::Error>
            where
                V: super::#visitor_name<
                    #(#conditions),*
                >,
        {
            Ok(match #walk_node_fn_name(visitor, node)? {
                #(#match_arms),*
            })
        }
    }))
}

/// Emit walker function(s) for the given node.
fn emit_walker_function(
    node_name: &syn::Ident,
    tree_def: &TreeDef,
    visitor_name: &syn::Ident,
    emit_mut: bool,
    inner_tokens: TokenStream,
) -> Result<TokenStream, syn::Error> {
    if is_leaf_node(node_name, tree_def) {
        return Ok(quote! {});
    }
    let ref_or_mut = ref_or_mut_ref(emit_mut);
    let mut_var = maybe_mut_prefix(emit_mut);
    let node_ref_name =
        suffix_ident_mut(&tree_def.opts.visitor_node_ref_base_type_name, emit_mut, Case::Pascal);
    let walk_node_fn_name = format_ident!("walk_{}", node_name.to_string().to_case(Case::Snake),);

    Ok(quote! {
        pub fn #walk_node_fn_name<V: super::#visitor_name>(
            visitor: #ref_or_mut V,
            #mut_var node: super::#node_ref_name<super::#node_name>,
        ) -> Result<#node_name<V>, V::Error> {
            #inner_tokens
        }
    })
}

/// Emit an expression to walk the given node field at the given `field_path`.
fn emit_walk_node_field(
    data: &NodeFieldData,
    field_path: TokenStream,
    tree_def: &TreeDef,
    emit_mut: bool,
) -> Result<Option<TokenStream>, syn::Error> {
    let get_visit_child_function_name = |child_name: &syn::Ident| {
        format_ident!("visit_{}", child_name.to_string().to_case(Case::Snake))
    };
    let iter_name = suffix_ident_mut("iter", emit_mut, Case::Snake);
    let as_ref_name = if emit_mut { format_ident!("as_mut") } else { format_ident!("as_ref") };
    let with_body_function_name = &tree_def.opts.ref_change_body_function_base_name;
    let ref_function_name = suffix_ident_mut(
        &tree_def.opts.get_ref_from_node_function_base_name,
        emit_mut,
        Case::Snake,
    );
    let node_ref_name =
        suffix_ident_mut(&tree_def.opts.visitor_node_ref_base_type_name, emit_mut, Case::Pascal);
    match data {
        NodeFieldData::Child { node_name: child_name } => {
            // Directly call visit
            let visit_child_function_name = get_visit_child_function_name(child_name);
            Ok(Some(quote! {
                visitor.#visit_child_function_name(#field_path.#ref_function_name())?
            }))
        }
        NodeFieldData::ChildList { node_name: child_name } => {
            // Iterate over the children and call visit, then collect to vector
            let visit_child_function_name = get_visit_child_function_name(child_name);
            Ok(Some(quote! {
                #field_path
                    .#iter_name()
                    .map(|t| visitor.#visit_child_function_name(t.#ref_function_name()))
                    .collect::<Result<Vec<_>, _>>()?
            }))
        }
        NodeFieldData::OptionalChild { node_name: child_name } => {
            // Map over the optional and collect inner
            let visit_child_function_name = get_visit_child_function_name(child_name);
            Ok(Some(quote! {
                #field_path
                    .#as_ref_name()
                    .map(|t| visitor.#visit_child_function_name(t.#ref_function_name()))
                    .transpose()?
            }))
        }
        NodeFieldData::Other { ty } => {
            if let Some(child_name) = is_node_ty(ty, tree_def) {
                // If this is a node ty, use the parent node's location and call visit
                let visit_child_function_name = get_visit_child_function_name(&child_name);

                if emit_mut {
                    Ok(Some(quote! {
                        visitor.#visit_child_function_name(
                            super::#node_ref_name::new(#field_path, span, id)
                        )?
                    }))
                } else {
                    Ok(Some(quote! {
                        visitor.#visit_child_function_name(
                            node.#with_body_function_name(#field_path)
                        )?
                    }))
                }
            } else {
                // Unrelated field, we skip it
                Ok(None)
            }
        }
    }
}

/// Emit a `walk_*` function for the given enum.
fn emit_walker_enum_function(
    enum_node: &EnumNodeDef,
    tree_def: &TreeDef,
    visitor_name: &syn::Ident,
    emit_mut: bool,
) -> Result<TokenStream, syn::Error> {
    let node_name = &enum_node.name;
    let ref_or_mut = ref_or_mut_ref(emit_mut);

    // Get the match cases
    let cases = enum_node
        .variants
        .iter()
        .map(|variant| -> Result<_, syn::Error> {
            // Match on each variant and visit the data members
            let variant_name = &variant.name;
            let (variant_binds, variant_walk_data) = variant
                .variant_data
                .as_ref()
                .map(|variant_data| -> Result<_, syn::Error> {
                    // We name the arguments arg{i} (they are all positional)
                    let fields = variant_data
                        .iter()
                        .enumerate()
                        .filter_map(|(i, data)| {
                            let field_name = format_ident!("arg{i}");
                            emit_walk_node_field(data, quote! { #field_name }, tree_def, emit_mut)
                                .transpose()
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let field_binds =
                        variant_data.iter().enumerate().map(|(i, _)| format_ident!("arg{i}"));
                    Ok((quote! { (#(#field_binds),*) }, quote! { (#(#fields),*) }))
                })
                .unwrap_or_else(|| Ok((quote! {}, quote! {})))?;
            Ok(quote! {
                super::#node_name::#variant_name #variant_binds
                    => #node_name::#variant_name #variant_walk_data
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    emit_walker_function(
        &enum_node.name,
        tree_def,
        visitor_name,
        emit_mut,
        quote! {
           let (span, id) = (node.span(), node.id());
           Ok(match #ref_or_mut *node {
               #(#cases),*
           })
        },
    )
}

/// Emit a `walk_*` function for the given struct.
fn emit_walker_struct_function(
    struct_node: &StructNodeDef,
    tree_def: &TreeDef,
    visitor_name: &syn::Ident,
    emit_mut: bool,
) -> Result<TokenStream, syn::Error> {
    let node_name = &struct_node.name;
    let ref_or_mut_ref = ref_or_mut_ref(emit_mut);

    let walk_fields = struct_node
        .fields
        .iter()
        .filter_map(|field| {
            let field_name = &field.name;
            emit_walk_node_field(
                &field.data,
                quote! { (#ref_or_mut_ref node.#field_name) },
                tree_def,
                emit_mut,
            )
            .transpose()
            .map(|walk_field| -> Result<_, syn::Error> {
                let walk_field = walk_field?;
                Ok(quote! {
                    #field_name: #walk_field
                })
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    emit_walker_function(
        &struct_node.name,
        tree_def,
        visitor_name,
        emit_mut,
        quote! {
            let (span, id) = (node.span(), node.id());
            Ok(#node_name {
                #(#walk_fields),*
            })
        },
    )
}

/// Emit `walk_*` functions for all the nodes in the tree.
fn emit_walker_functions(tree_def: &TreeDef, emit_mut: bool) -> Result<TokenStream, syn::Error> {
    let visitor_name =
        suffix_ident_mut(&tree_def.opts.visitor_trait_base_name, emit_mut, Case::Pascal);
    let walker_functions = tree_def
        .nodes
        .values()
        .map(|node| {
            match &node {
                TreeNodeDef::EnumNodeDef(enum_node) => {
                    // Potentially emit walk_*_same_children
                    let same_children_function = emit_walker_enum_function_same_children(
                        enum_node,
                        tree_def,
                        &visitor_name,
                        emit_mut,
                    )?
                    .unwrap_or_else(|| quote! {});
                    let base_function =
                        emit_walker_enum_function(enum_node, tree_def, &visitor_name, emit_mut)?;
                    Ok(quote! {
                        #same_children_function
                        #base_function
                    })
                }
                TreeNodeDef::StructNodeDef(struct_node) => {
                    emit_walker_struct_function(struct_node, tree_def, &visitor_name, emit_mut)
                }
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(quote! {
        #(#walker_functions)*
    })
}

/// Emit a `walk(_mut)?` module for the given tree.
fn emit_walker(tree_def: &TreeDef, emit_mut: bool) -> Result<TokenStream, syn::Error> {
    let walker_types = emit_walked_types(tree_def, emit_mut)?;
    let walker_functions = emit_walker_functions(tree_def, emit_mut)?;
    let walk_mod_name = if emit_mut { format_ident!("walk_mut") } else { format_ident!("walk") };

    Ok(quote! {
        pub mod #walk_mod_name {
            #walker_types
            #walker_functions
        }
    })
}

/// Emit the tree definition as Rust syntax.
pub(crate) fn emit_tree(tree_def: &TreeDef) -> Result<TokenStream, syn::Error> {
    Ok([
        emit_other_items(tree_def),
        emit_node_defs(tree_def),
        // Generate mut and non-mut versions of the walker and visitor
        emit_visitor(tree_def, true),
        emit_visitor(tree_def, false),
        emit_walker(tree_def, true)?,
        emit_walker(tree_def, false)?,
    ]
    .into_iter()
    .collect())
}
