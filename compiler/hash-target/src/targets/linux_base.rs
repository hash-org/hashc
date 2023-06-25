use crate::Target;

/// Basic options for a linux distribution. This serves as a basis for
/// configuration options on linux targets.
pub fn options() -> Target {
    Target { os: "linux".into(), dynamic_linking: true, ..Default::default() }
}
