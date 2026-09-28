# Native checks cover the complete candidate; ISA refinement coverage remains partial.
.PHONY: asm models model-check proofs binding smoke fixtures reference native-check native-abi lowering-check check

asm:
	mkdir -p asm/x86 asm/arm
	rustc +1.94.0 --crate-type=lib -C opt-level=3 --target x86_64-unknown-linux-gnu --emit=asm=asm/x86/uint64.s impl/uint64.rs
	rustc +1.94.0 --crate-type=lib -C opt-level=3 --target aarch64-unknown-linux-gnu --emit=asm=asm/arm/uint64.s impl/uint64.rs
	python3 scripts/build-native.py

models:
	python3 scripts/prepare-models.py

model-check: models
	python3 scripts/check-arm-model.py
	cd backends/arm && lake build SszArm.LogicalImmediateRegression

proofs: models
	cd backends/x86 && lake build
	cd backends/arm && lake build

binding: models
	python3 scripts/check-asm.py
	python3 scripts/check-runtime-binding.py
	python3 scripts/check-bool-binding.py
	python3 scripts/check-uint-binding.py
	python3 scripts/check-byte-view-binding.py
	python3 scripts/check-nat-compare-binding.py
	python3 scripts/check-nat-add-binding.py
	python3 scripts/check-nat-mul-binding.py
	python3 scripts/check-nat-division-binding.py
	python3 scripts/check-nat-conversion-binding.py
	python3 scripts/check-bitvector-binding.py
	python3 scripts/check-delimited-binding.py
	python3 scripts/check-bitlist-binding.py
	python3 scripts/check-dispatch-binding.py
	python3 scripts/check-emit-binding.py
	python3 scripts/check-measure-binding.py
	python3 scripts/check-serialize-binding.py

smoke:
	python3 scripts/check-uint64.py
	python3 scripts/check-memory.py
	python3 scripts/check-division.py

fixtures:
	cd vendor/ssz-specs && UV_PROJECT_ENVIRONMENT=.venv312 SSZ_PARANOID_ROOTS=1 uv run --python /usr/bin/python3.12 --locked --group test fill --clean

# Conformance and differential execution are not machine-code refinement proofs.
native-check: fixtures
	cargo test --manifest-path native/Cargo.toml --all-targets
	cargo run --manifest-path native/Cargo.toml --release --example conformance -- vendor/ssz-specs/fixtures
	python3 scripts/check-native-parity.py

native-abi: fixtures
	python3 scripts/check-native.py

lowering-check:
	python3 scripts/check-arm-lowering.py
	python3 scripts/check-x86-lowering.py

# Reference correctness/conformance is not a native implementation proof.
reference: fixtures
	cd vendor/ssz-specs/lean && lake build
	cd vendor/ssz-specs/lean && .lake/build/bin/conformance ../fixtures
	cd vendor/ssz-specs/lean && .lake/build/bin/regressions

check: reference model-check proofs binding smoke native-check native-abi lowering-check
