use circuit_cairo_air::all_components::all_components;
use stwo::core::fields::qm31::QM31;

use crate::consts::PRIVACY_TRANSACTION_COMPONENTS;

#[test]
fn check_components() {
    let all_components = all_components::<QM31>();
    for component_name in PRIVACY_TRANSACTION_COMPONENTS {
        assert!(
            all_components.contains_key(component_name),
            "Component {component_name} is not in the all_components"
        );
    }
}
