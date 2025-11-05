# LeanUtils
Lean scripts for indexing sorries and verifying proofs. 

## Testing
The repository can be tested in two separate ways. 
1. On a specific Lean version: by running `lake test`
2. Across several Lean versions: by running `LeanUtilsTest/run_tests.sh`. The
   toolchains tested against are stored in `testable_toolchains.txt`. 

## Lean versions

This repository will eventually contain releases tagged with lean version
strings (e.g. v4.17.0). The user (sorry indexer, proof checker, ...) should 
use the most recent version tag which is less than or equal to the version tag
for the Lean repository being indexed/tested/...

### Bumping lean versions

When a new major Lean version is released, add the corresponding toolchain to
`LeanUtilsTest/testable_toolchain.txt`. If this does not break any unit tests,
we are good to go. Otherwise fix the test, and create a new
release with the current version tag (if necessary, the fixed version might be
backwards compatible with the current range of toolchains).


## Current Lean versions covered

Currently, the tests seem to pass on all Lean versions from `v4.9.0` to `v4.25.0-rc1`.
TODO(Paul-Lez): increase test coverage.