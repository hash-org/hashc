//! Functions to emit tree definitions, visitors, walkers, given a parsed
//! [`TreeDef`].

use convert_case::{Case, Casing};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::definitions::{
    EnumNodeDef, EnumNodeVariant, NodeFieldData, StructNodeDef, StructNodeField, TreeDef,
    TreeNodeDef, NODE_DEF_ATTR_NAME,
};

fn emit_other_items(def: &TreeDef) -> TokenStream {
    def.other_items.iter().map(|item| -> TokenStream { quote!(#item) }).collect()
}

fn emit_node_field_data(data: &NodeFieldData, tree_def: &TreeDef) -> TokenStream {
    match data {
        NodeFieldData::Child { node_name } => {
            let node_type_name = &tree_def.opts.node_type_name;
            quote!(#node_type_name<#node_name>)
        }
        NodeFieldData::ChildList { node_name } => {
            let nodes_type_name = &tree_def.opts.nodes_type_name;
            quote!(#nodes_type_name<#node_name>)
        }
        NodeFieldData::OptionalChild { node_name } => {
            let nodes_type_name = &tree_def.opts.nodes_type_name;
            quote!(Option<#nodes_type_name<#node_name>>)
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

fn emit_node_defs(def: &TreeDef) -> TokenStream {
    def.nodes
        .values()
        .map(|node| match node {
            TreeNodeDef::EnumNodeDef(enum_def) => emit_enum_def(enum_def, def),
            TreeNodeDef::StructNodeDef(struct_def) => emit_struct_def(struct_def, def),
        })
        .collect()
}

fn emit_visitor(def: &TreeDef, emit_mut: bool) -> TokenStream {
    let visitor_name = if emit_mut {
        format_ident!("{}Mut", &def.opts.visitor_trait_base_name)
    } else {
        def.opts.visitor_trait_base_name.clone()
    };
    let node_ref_name = if emit_mut {
        format_ident!("{}Mut", &def.opts.visitor_node_ref_base_type_name)
    } else {
        def.opts.visitor_node_ref_base_type_name.clone()
    };

    let node_visitor_methods = def.nodes.iter().map(|(node_name, _)| {
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

fn emit_walker_node_field_data_type(data: &NodeFieldData) -> TokenStream {
    let get_child_ret = |child_name: &syn::Ident| {
        format_ident!("{}Ret", child_name.to_string().to_case(Case::Pascal))
    };
    match data {
        NodeFieldData::Child { node_name: child_name } => {
            let child_ret = get_child_ret(child_name);
            quote! { V::#child_ret }
        }
        NodeFieldData::ChildList { node_name: child_name } => {
            let child_ret = get_child_ret(child_name);
            quote! { Vec<V::#child_ret> }
        }
        NodeFieldData::OptionalChild { node_name: child_name } => {
            let child_ret = get_child_ret(child_name);
            quote! { Option<V::#child_ret> }
        }
        NodeFieldData::Other { ty } => quote! { #ty },
    }
}

fn emit_walker_types(def: &TreeDef, emit_mut: bool) -> TokenStream {
    let visitor_name = if emit_mut {
        format_ident!("{}Mut", &def.opts.visitor_trait_base_name)
    } else {
        def.opts.visitor_trait_base_name.clone()
    };
    let walker_types = def.nodes.iter().map(|(node_name, node)| match node {
        TreeNodeDef::EnumNodeDef(enum_node) => {
            let variants = enum_node.variants.iter().map(|variant| {
                let variant_name = &variant.name;
                let variant_data = variant
                    .variant_data
                    .as_ref()
                    .map(|variant_data| {
                        let fields = variant_data.iter().map(|data| {
                            let field_type = emit_walker_node_field_data_type(data);
                            quote! { #field_type }
                        });
                        quote! {
                            (#(#fields),*)
                        }
                    })
                    .unwrap_or_else(|| quote! {});
                quote! { #variant_name #variant_data }
            });

            quote! {
                pub enum #node_name<V: super::#visitor_name> {
                    #(#variants),*
                }
            }
        }
        TreeNodeDef::StructNodeDef(struct_node) => {
            let fields = struct_node.fields.iter().map(|field| {
                let field_name = &field.name;
                let field_type = emit_walker_node_field_data_type(&field.data);
                quote! {
                   pub #field_name: #field_type
                }
            });
            quote! {
                pub struct #node_name<V: super::#visitor_name> {
                    #(#fields),*
                 }
            }
        }
    });

    quote! {
        #(#walker_types)*
    }
}

fn emit_walker(def: &TreeDef, emit_mut: bool) -> TokenStream {
    let walker_types = emit_walker_types(def, emit_mut);
    let walker_functions = vec![quote!()];
    let walk_mod_name = if emit_mut { format_ident!("walk_mut") } else { format_ident!("walk") };

    quote! {
        pub mod #walk_mod_name {
            #walker_types
            #(#walker_functions)*
        }
    }
}

pub(crate) fn emit_tree(def: &TreeDef) -> Result<TokenStream, syn::Error> {
    Ok([
        emit_node_defs(def),
        emit_other_items(def),
        emit_visitor(def, true),
        emit_visitor(def, false),
        emit_walker(def, true),
        emit_walker(def, false),
    ]
    .into_iter()
    .collect())
}
