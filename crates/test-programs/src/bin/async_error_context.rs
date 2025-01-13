mod bindings {
    wit_bindgen::generate!({
        path: "../misc/component-async-tests/wit",
        world: "error-context-usage",
        async: {
            exports: [
                "local:local/run#run",
            ],
        }
    });

    use super::Component;
    export!(Component);
}

use bindings::exports::local::local::run::Guest;

// TODO: add this to wit_bindgen_rt
// use wit_bindgen_rt::error_support::error_context_new;

struct Component;

impl Guest for Component {
    async fn run() {
        let err_ctx = error_context_new("error".into());
        assert!(err_ctx.debug_message(), "error");
    }
}

// Unused function; required since this file is built as a `bin`:
fn main() {}
