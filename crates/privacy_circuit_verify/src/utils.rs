pub struct Version {
    pub major: u8,
    pub minor: u8,
    pub patch: u8,
}

impl Version {
    /// Returns the version of the privacy crates (shared workspace version).
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_current() {
        let version = Version::current();
        assert_eq!(
            version.major,
            env!("CARGO_PKG_VERSION_MAJOR").parse::<u8>().unwrap()
        );
        assert_eq!(
            version.minor,
            env!("CARGO_PKG_VERSION_MINOR").parse::<u8>().unwrap()
        );
        assert_eq!(
            version.patch,
            env!("CARGO_PKG_VERSION_PATCH").parse::<u8>().unwrap()
        );
    }
}
