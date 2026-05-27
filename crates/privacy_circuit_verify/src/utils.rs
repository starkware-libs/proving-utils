pub struct Version {
    pub major: u8,
    pub minor: u8,
    pub patch: u8,
}

impl Version {
    /// Returns the version of the privacy crates.
    pub fn current() -> Self {
        Self {
            major: env!("CARGO_PKG_VERSION_MAJOR")
                .parse()
                .expect("major version fits in u8"),
            minor: env!("CARGO_PKG_VERSION_MINOR")
                .parse()
                .expect("minor version fits in u8"),
            patch: env!("CARGO_PKG_VERSION_PATCH")
                .parse()
                .expect("patch version fits in u8"),
        }
    }
}
