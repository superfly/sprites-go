

Integration tests are failing

Run integration tests with `./run-integration-tests.sh`

Fix the broken integration tests:

* Make sure the tla traces we're receiving are coming through properly. You may have to pass TEST_VERBOSE=1 to make test-integration to read them
* ALWAYS conform to @spec/sprite_env.tla. Don't change any state functionality in conflict with the spec
* When you think these tests are working, look at the tests/tmp/*.trace results and see if they're valid

* NEVER add ignore to stateless states/transition definitions

---

Validating Traces

* Once you've made integration tests, run this command: `./validate-traces.sh`
* ALWAYS make sure you're working from server, do not switch directories