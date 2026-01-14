#!/usr/bin/env bash

# Test suite for LeanUtils across multiple Lean toolchains
# Usage: ./run_tests.sh [path_to_testable_toolchains.txt]

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Path to toolchains file
TOOLCHAINS_FILE="${1:-$SCRIPT_DIR/testable_toolchains.txt}"

if [[ ! -f "$TOOLCHAINS_FILE" ]]; then
    echo -e "${RED}Error: Toolchains file not found: $TOOLCHAINS_FILE${NC}"
    exit 1
fi

echo "Testing LeanUtils across multiple toolchains"
echo "=============================================="
echo ""

# Statistics
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
declare -a FAILED_TOOLCHAINS

# Read toolchains from file
while IFS= read -r toolchain || [[ -n "$toolchain" ]]; do
    # Skip empty lines and comments
    [[ -z "$toolchain" || "$toolchain" =~ ^[[:space:]]*# ]] && continue

    TOTAL_TESTS=$((TOTAL_TESTS + 1))

    echo -e "${YELLOW}Testing toolchain: $toolchain${NC}"
    echo "-------------------------------------------"

    # Create temporary directory
    TEMP_DIR=$(mktemp -d -t lean-test-XXXXXXXXXX)

    # Cleanup function
    cleanup() {
        if [[ -d "$TEMP_DIR" ]]; then
            echo "  Cleaning up temporary directory..."
            rm -rf "$TEMP_DIR"
        fi
    }

    # Set trap to cleanup on exit
    trap cleanup EXIT

    # Copy project to temp directory
    echo "  Creating temporary test environment..."
    cp -r "$PROJECT_ROOT"/* "$TEMP_DIR/" 2>/dev/null || true
    cp -r "$PROJECT_ROOT"/.git "$TEMP_DIR/" 2>/dev/null || true
    cd "$TEMP_DIR"

    # Update lean-toolchain file
    echo "$toolchain" > lean-toolchain

    # Run tests
    TEST_FAILED=0

    # Step 1: lake update
    echo "  Running: lake update"
    set +e  # Temporarily disable exit on error to capture it ourselves
    lake update > /tmp/lake-update.log 2>&1
    UPDATE_EXIT=$?
    set -e

    if [[ $UPDATE_EXIT -ne 0 ]]; then
        echo -e "${RED}  ✗ lake update failed (exit code: $UPDATE_EXIT)${NC}"
        echo "  Error output:"
        tail -20 /tmp/lake-update.log | sed 's/^/    /'
        TEST_FAILED=1
    else
        echo -e "${GREEN}  ✓ lake update succeeded${NC}"
    fi

    # Step 2: lake build (only if update succeeded)
    if [[ $TEST_FAILED -eq 0 ]]; then
        echo "  Running: lake build"
        set +e
        lake build > /tmp/lake-build.log 2>&1
        BUILD_EXIT=$?
        set -e

        if [[ $BUILD_EXIT -ne 0 ]]; then
            echo -e "${RED}  ✗ lake build failed (exit code: $BUILD_EXIT)${NC}"
            echo "  Error output:"
            tail -20 /tmp/lake-build.log | sed 's/^/    /'
            TEST_FAILED=1
        else
            echo -e "${GREEN}  ✓ lake build succeeded${NC}"
        fi
    fi

    # Step 3: lake test (only if build succeeded)
    if [[ $TEST_FAILED -eq 0 ]]; then
        echo "  Running: lake test"
        set +e
        lake test > /tmp/lake-test.log 2>&1
        TEST_EXIT=$?
        set -e

        if [[ $TEST_EXIT -ne 0 ]]; then
            echo -e "${RED}  ✗ lake test failed (exit code: $TEST_EXIT)${NC}"
            echo "  Error output:"
            tail -20 /tmp/lake-test.log | sed 's/^/    /'
            TEST_FAILED=1
        else
            echo -e "${GREEN}  ✓ lake test succeeded${NC}"
        fi
    fi

    # Update statistics
    if [[ $TEST_FAILED -eq 0 ]]; then
        PASSED_TESTS=$((PASSED_TESTS + 1))
        echo -e "${GREEN}✓ Toolchain $toolchain: PASSED${NC}"
    else
        FAILED_TESTS=$((FAILED_TESTS + 1))
        FAILED_TOOLCHAINS+=("$toolchain")
        echo -e "${RED}✗ Toolchain $toolchain: FAILED${NC}"
    fi

    echo ""

    # Cleanup
    cleanup
    trap - EXIT

done < "$TOOLCHAINS_FILE"

# Print summary
echo ""
echo "=============================================="
echo "Test Summary"
echo "=============================================="
echo "Total toolchains tested: $TOTAL_TESTS"
echo -e "${GREEN}Passed: $PASSED_TESTS${NC}"
echo -e "${RED}Failed: $FAILED_TESTS${NC}"

if [[ $FAILED_TESTS -gt 0 ]]; then
    echo ""
    echo "Failed toolchains:"
    for tc in "${FAILED_TOOLCHAINS[@]}"; do
        echo -e "  ${RED}✗ $tc${NC}"
    done
    exit 1
else
    echo ""
    echo -e "${GREEN}All tests passed!${NC}"
    exit 0
fi
