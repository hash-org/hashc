//! Windows MSVC target base configuration.

use crate::{
    link::{LinkageArgs, LinkerFlavour, Lld},
    Target,
};

pub fn options() -> Target {
    let mut pre_link_args = LinkageArgs::new();
    pre_link_args.add_str_args(LinkerFlavour::Msvc(Lld::No), &["/NOLOGO"]);

    // Specify the entry point and add the crt library by default.
    //
    // @@Future: make this more configurable / derivable from the settings.
    let mut late_link_args = LinkageArgs::new();
    late_link_args.add_str_args(
        LinkerFlavour::Msvc(Lld::No),
        // ##Hack: without `defaultlib:oldnames` we get a linker error:
        // specifally for symbols like `write`, unsure why this is needed.
        &["/ENTRY:mainCRTStartup", "-defaultlib:libcmt", "-defaultlib:oldnames"],
    );

    Target {
        os: "windows".into(),
        name: "x86_64-pc-windows-msvc".into(),
        linker_flavour: LinkerFlavour::Msvc(Lld::No),
        dylib_prefix: "".into(),
        dylib_suffix: "dll".into(),
        exe_suffix: "exe".into(),
        staticlib_suffix: "lib".into(),
        staticlib_prefix: "".into(),
        dynamic_linking: true,
        pre_link_args,
        late_link_args,
        ..Default::default()
    }
}
