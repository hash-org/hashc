//! Functions to emit tree definitions, visitors, walkers, given a parsed
//! [`TreeDef`].

use convert_case::{Case, Casing};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::definitions::{
    EnumNodeDef, EnumNodeVariant, NodeFieldData, StructNodeDef, StructNodeField, TreeDef,
    TreeNodeDef, NODE_DEF_ATTR_NAME,
};

fn suffix_ident_mut(ident: impl ToString, emit_mut: bool, case: Case) -> syn::Ident {
    if emit_mut {
        let word = format!("{}_mut", ident.to_string());
        format_ident!("{}", word.to_case(case))
    } else {
        format_ident!("{}", ident.to_string().to_case(case))
    }
}

fn emit_other_items(def: &TreeDef) -> TokenStream {
    def.other_items.iter().map(|item| -> TokenStream { quote!(#item) }).collect()
}

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

    let node_visitor_methods = tree_def.nodes.iter().map(|(node_name, _)| {
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

fn emit_walked_struct_type(
    struct_node: &StructNodeDef,
    tree_def: &TreeDef,
    visitor_name: &syn::Ident,
) -> Result<TokenStream, syn::Error> {
    let node_name = &struct_node.name;
    let fields = struct_node.fields.iter().filter_map(|field| {
        let field_name = &field.name;
        let (field_type, is_node) = emit_walked_node_field_type(&field.data, tree_def);
        if is_node {
            Some(quote! {
               pub #field_name: #field_type
            })
        } else {
            None
        }
    });
    Ok(quote! {
        pub struct #node_name<V: super::#visitor_name> {
            #(#fields),*
         }
    })
}

fn emit_walked_enum_type(
    enum_node: &EnumNodeDef,
    tree_def: &TreeDef,
    visitor_name: &syn::Ident,
) -> Result<TokenStream, syn::Error> {
    let node_name = &enum_node.name;
    let variants = enum_node
        .variants
        .iter()
        .map(|variant| -> Result<_, syn::Error> {
            let variant_name = &variant.name;
            let variant_data = variant
                .variant_data
                .as_ref()
                .map(|variant_data| {
                    if variant_data.len() < 1 {
                        return Err(syn::Error::new_spanned(
                            variant_name,
                            "Enum node variant must have at most one data member",
                        ));
                    }
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

fn emit_walked_types(tree_def: &TreeDef, emit_mut: bool) -> Result<TokenStream, syn::Error> {
    let visitor_name =
        suffix_ident_mut(&tree_def.opts.visitor_trait_base_name, emit_mut, Case::Pascal);
    let walker_types = tree_def
        .nodes
        .iter()
        .map(|(_, node)| -> Result<_, syn::Error> {
            match node {
                TreeNodeDef::EnumNodeDef(enum_node) => {
                    emit_walked_enum_type(enum_node, tree_def, &visitor_name)
                }
                TreeNodeDef::StructNodeDef(struct_node) => {
                    emit_walked_struct_type(struct_node, tree_def, &visitor_name)
                }
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(quote! {
        #(#walker_types)*
    })
}

fn emit_walker_enum_function(
    enum_node: &EnumNodeDef,
    tree_def: &TreeDef,
    visitor_name: &syn::Ident,
    emit_mut: bool,
) -> Result<TokenStream, syn::Error> {
    // @@Todo
    Ok(quote!())
}

fn emit_walker_struct_function(
    struct_node: &StructNodeDef,
    tree_def: &TreeDef,
    visitor_name: &syn::Ident,
    emit_mut: bool,
) -> Result<TokenStream, syn::Error> {
    let node_name = &struct_node.name;
    let walk_node_fn_name = format_ident!("walk_{}", node_name.to_string().to_case(Case::Snake));
    let ref_or_mut = if emit_mut {
        quote! { &mut }
    } else {
        quote! { & }
    };
    let mut_var = if emit_mut {
        quote! { mut }
    } else {
        quote! {}
    };
    let node_ref_name =
        suffix_ident_mut(&tree_def.opts.visitor_node_ref_base_type_name, emit_mut, Case::Pascal);
    let ref_function_name = suffix_ident_mut(
        &tree_def.opts.get_ref_from_node_function_base_name,
        emit_mut,
        Case::Snake,
    );
    let iter_name = suffix_ident_mut("iter", emit_mut, Case::Snake);
    let as_ref_name = if emit_mut { format_ident!("as_mut") } else { format_ident!("as_ref") };
    let with_body_function_name = &tree_def.opts.ref_change_body_function_base_name;
    let get_visit_child_function_name = |child_name: &syn::Ident| {
        format_ident!("visit_{}", child_name.to_string().to_case(Case::Snake))
    };

    let walk_fields = struct_node.fields.iter().map(|field| {
        let field_name = &field.name;
        match &field.data {
            NodeFieldData::Child { node_name: child_name } => {
                let visit_child_function_name = get_visit_child_function_name(child_name);
                quote! {
                    #field_name: visitor.#visit_child_function_name(node.#field_name.#ref_function_name())?
                }
            }
            NodeFieldData::ChildList { node_name: child_name } => {
                let visit_child_function_name = get_visit_child_function_name(child_name);
                quote! {
                    #field_name: node
                        .#field_name
                        .#iter_name()
                        .map(|t| visitor.#visit_child_function_name(t.#ref_function_name()))
                        .collect::<Result<Vec<_>, _>>()?
                }
            }
            NodeFieldData::OptionalChild { node_name: child_name } => {
                let visit_child_function_name = get_visit_child_function_name(child_name);
                quote! {
                    #field_name: node
                        .#field_name
                        .#as_ref_name()
                        .map(|t| visitor.#visit_child_function_name(t.#ref_function_name()))
                        .transpose()?
                }
            }
            NodeFieldData::Other { ty } => {
                if let Some(child_name) = is_node_ty(ty, tree_def) {
                    let visit_child_function_name = get_visit_child_function_name(&child_name);
                    quote! {
                        #field_name: visitor.#visit_child_function_name(
                            node.#with_body_function_name(#ref_or_mut node.#field_name)
                        )?
                    }
                } else {
                    quote! {}
                }
            }
        }
    });

    Ok(quote! {
        pub fn #walk_node_fn_name<V: super::#visitor_name>(
            visitor: #ref_or_mut V,
            #mut_var node: super::#node_ref_name<super::#node_name>,
        ) -> Result<#node_name<V>, V::Error> {
            Ok(#node_name {
                #(#walk_fields),*
            })
        }
    })
}

fn emit_walker_functions(tree_def: &TreeDef, emit_mut: bool) -> Result<TokenStream, syn::Error> {
    let visitor_name =
        suffix_ident_mut(&tree_def.opts.visitor_trait_base_name, emit_mut, Case::Pascal);
    let walker_functions = tree_def
        .nodes
        .iter()
        .map(|(_, node)| -> Result<_, syn::Error> {
            match &node {
                TreeNodeDef::EnumNodeDef(enum_node) => {
                    emit_walker_enum_function(&enum_node, tree_def, &visitor_name, emit_mut)
                }
                TreeNodeDef::StructNodeDef(struct_node) => {
                    emit_walker_struct_function(&struct_node, tree_def, &visitor_name, emit_mut)
                }
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(quote! {
        #(#walker_functions)*
    })
}

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

pub(crate) fn emit_tree(tree_def: &TreeDef) -> Result<TokenStream, syn::Error> {
    Ok([
        emit_node_defs(tree_def),
        emit_other_items(tree_def),
        emit_visitor(tree_def, true),
        emit_visitor(tree_def, false),
        emit_walker(tree_def, true)?,
        emit_walker(tree_def, false)?,
    ]
    .into_iter()
    .collect())
}
