0. Loop over toolchains in the testable_toolchain.txt file
1. Create temporary directory with project to test on with the current toolchain
2. run lake update, lake build, lake test
3. Surface errors to the user. 
4. Clean up temporary directory. 
5. In a future where we need different versions of the repo for different
   intervals of toolchains, of course only test on the interval of toolchains
   corresponding to the current version.