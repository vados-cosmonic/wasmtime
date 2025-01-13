mod bindings {
    wit_bindgen::generate!({
        path: "../misc/component-async-tests/wit",
        world: "error-context-usage",
    });
    use super::Component;
    export!(Component);
}

use bindings::exports::local::local::run::Guest;
use wit_bindgen_rt::error_support::error_context_new;

struct Component;

impl Guest for Component {
    fn run() {
        let err_ctx = error_context_new("error".into());
        assert!(err_ctx.debug_message(), "error");
    }
}

// Unused function; required since this file is built as a `bin`:
fn main() {}
