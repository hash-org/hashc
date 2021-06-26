// use std::{fs, path::PathBuf};
// use std::path::{Path};

// use quote::{ToTokens, quote};
// use proc_macro2::{TokenStream};
// use proc_macro_hack::proc_macro_hack;
// use syn::{LitStr, parse_macro_input};

// #[derive(Debug, Clone, PartialEq)]
// struct Dir {
//     root_rel_path: PathBuf,
//     abs_path: PathBuf,
//     items: Vec<Dir>,
// }

// impl ToTokens for Dir {
//     fn to_tokens(&self, tokens: &mut TokenStream) {
//         let root_rel_path = self.root_rel_path.display().to_string();
//         let items = &self.items;

//         let tok = quote! {
//             $crate::Dir {
//                 path: #root_rel_path,
//                 items: &[#(
//                     #items
//                  ),*],
//             }
//         };

//         tok.to_tokens(tokens);
//     }
// }

// #[proc_macro_hack]
// pub fn get_stdlib_modules(input: TokenStream) -> TokenStream {
//     let dir = parse_macro_input!(input as LitStr).value();
//     let paths: Vec<Dir> = vec![];

//     if PathBuf::from(dir).is_dir() {
//         for entry in fs::read_dir(dir).unwrap() {
//             match entry {
//                 Ok(p) => {
//                     let path = p.path();

//                     if path.is_dir() {
//                         // recurse and get all of the files with the prefix
//                         let prefix = Path::new(path.file_stem().unwrap());

//                         let path_str = path.as_path().to_str().unwrap();
//                         let arg = TokenStream::from(quote! {
//                             #path_str
//                         });

//                         let t = get_stdlib_modules(arg);
//                         let result = parse_macro_input!(t as &[&Dir]);

//                         for entry in result {
//                             paths.push(prefix.join(*entry).as_path());
//                         }
//                     } else if path.is_file() {
//                         let file_name=  path.file_stem().unwrap();
//                         paths.push(Path::new(file_name));
//                     }
//                 },
//                 Err(e) => panic!("Unable to read standard library folder: {}", e),
//             }
//         }
//     }

//     TokenStream::from(quote! {
//         #paths
//     })
// }
