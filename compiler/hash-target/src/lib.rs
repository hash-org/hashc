//! Definitions to describe the target of Hash compilation.

/// The target that the compiler should compile for.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Target {
    /// The size of the pointer for the target in bytes.
    pub pointer_width: usize,

    /// The name of the target
    pub name: String,
}

impl Target {
    /// Create a new target from the given name and pointer width.
    pub fn new(name: String, pointer_width: usize) -> Self {
        Self { name, pointer_width }
    }

    /// Create a new target from the given name and pointer width.
    pub fn from_string(name: String) -> Option<Self> {
        match name.as_str() {
            "x86_64" => Some(Self::new(name, 8)),
            "x86" => Some(Self::new(name, 4)),
            "aarch64" => Some(Self::new(name, 8)),
            "arm" => Some(Self::new(name, 4)),
            _ => None,
        }
    }
}

impl Default for Target {
    fn default() -> Self {
        Self { pointer_width: 8, name: "x86_64".into() }
    }
}

/// Holds information about various targets that are currently used by the
/// compiler.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct TargetInfo {
    /// The target value of the host that the compiler is running
    /// for.
    host: Target,

    /// The target that the compiler is compiling for.
    target: Target,
}

impl TargetInfo {
    /// Create a new target info from the given host and target.
    pub fn new(host: Target, target: Target) -> Self {
        Self { host, target }
    }

    /// Get the target that the compiler is compiling for.
    pub fn target(&self) -> &Target {
        &self.target
    }

    /// Get the host target that the compiler is running on.
    pub fn host(&self) -> &Target {
        &self.host
    }
}
