#!/bin/bash
# Run from any directory on ARM64 macOS. Artifacts are retained for inspection.
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd)
build_dir=${1:-$(mktemp -d /private/tmp/fp64-integer.XXXXXX)}
mkdir -p "$build_dir"
build_dir=$(cd "$build_dir" && pwd)
cd "$source_dir"
common=(-Wall -Wextra -Werror -O2)
checked=(-fsanitize=undefined -fno-sanitize-recover=all)

clang -c Padic2AArch64.s -o "$build_dir/kernels.o"
clang "${common[@]}" -mgeneral-regs-only -c FP64Integer.c -o "$build_dir/integer.o"
clang "${common[@]}" "${checked[@]}" -mgeneral-regs-only -c FP64Integer.c -o "$build_dir/integer-checked.o"
clang "${common[@]}" "${checked[@]}" "$build_dir/kernels.o" \
    FP64IntegerDivisionTest.c -o "$build_dir/division-test"
"$build_dir/division-test"
clang "${common[@]}" "${checked[@]}" -frounding-math -ffp-contract=off \
    "$build_dir/kernels.o" "$build_dir/integer-checked.o" FP64IntegerTest.c -o "$build_dir/native-test"
"$build_dir/native-test"

clang -dynamiclib "$build_dir/kernels.o" "$build_dir/integer.o" -o "$build_dir/libfp64-integer.dylib"
python3 FP64IntegerReferenceTest.py "$build_dir/libfp64-integer.dylib"
python3 FP64IntegerInstructionTest.py "$build_dir/integer.o" "$build_dir/kernels.o"

clang "${common[@]}" "${checked[@]}" -ffp-contract=off \
    "$build_dir/kernels.o" "$build_dir/integer-checked.o" Padic2Packed64.c \
    FP64IntegerComparison.c -o "$build_dir/comparison"
"$build_dir/comparison" | tee "$build_dir/comparison.txt"

clang "${common[@]}" "${checked[@]}" "$build_dir/kernels.o" Padic2AArch64Test.c -o "$build_dir/padic2-test"
"$build_dir/padic2-test"
clang "${common[@]}" "${checked[@]}" "$build_dir/kernels.o" Padic2Packed64.c \
    Padic2Packed64Test.c -o "$build_dir/padic64-test"
"$build_dir/padic64-test"
printf 'Artifacts: %s\n' "$build_dir"
