# Learnings from native SSZ formal verification

These are working engineering notes, not a completion certificate. They distinguish observed results from recommendations and cover refinement of the emitted x86-64 and AArch64 code against the pinned SSZ specification.

## 1. Where the bottleneck is

The current bottleneck is closing and composing machine-level proofs, not implementing SHA-256 or discovering the basic SSZ algorithms.

The native implementation has broad executable conformance coverage, but executable coverage and formal coverage are different. There are checked Boolean, UInt, byte-view, and runtime-kernel proof components. Both native `Nat.compare` refinements and both complete private delimited-bit decoder refinements are kernel-checked, imported into their architecture roots, and axiom-audited. This is not yet a complete refinement of every public operation.

### Expanded machine states overwhelm otherwise small arguments

A short native block can produce a large expression containing nested register writes, flag updates, memory stores, and PC changes. Unfolding those expressions again in a loop or caller proof causes several problems:

- Tactics repeatedly rediscover the same state facts.
- Elaboration spends time on definitional equality rather than the algorithm.
- Proof terms become large enough to hit recursion limits during kernel checking.
- A local representation change breaks many downstream proofs.

This has produced actual kernel deep-recursion failures, heartbeat exhaustion, and compilation timeouts. Raising limits is not a substitute for finding the expansion responsible.

### Representation mismatches become proof work

Examples encountered here include:

- A hypothesis uses `read_pc s`, while the goal uses the underlying PC register accessor.
- A comparison theorem expects a complemented operand, but simplification has already turned that operand into a concrete all-ones literal.
- A bit-vector literal's `toNat` remains opaque to arithmetic automation.
- Zero is expressed at different types or widths.
- A useful expression is unfolded before the lemma that recognizes it can run.

These are usually normalization problems, not counterexamples to the algorithm. They need small conversion lemmas and a consistent boundary representation.

One x86 ADD/ADC proof exposed a more specific dependent-instance failure. An intermediate simplifier changed the visible index of `OfNat UInt64` while leaving its implicit instance indexed by the old flag expression. Later rewrites reported that the goal was not type-correct at implicit transparency; repeated arithmetic and numeral rewrites did not repair the cause. Enabling `instances := true` on the two originating intermediate simplifiers kept index and instance consistent, and the scalar-sum block then passed in 1.5 seconds. Broadly adding a numeral conversion to the default simp set instead caused a rewrite cycle. Fix the originating normalization step; do not raise recursion limits to hide it.

### Memory, ABI, and resource obligations are substantial

Returning the right mathematical value is only part of a native refinement. We also need the actual return instruction, correct stack restoration, permitted register clobbers, preserved borrowed inputs, exact write regions, and correct arena effects.

Important cases are easy to lose in an overly simple contract:

- Immutable inputs may alias each other or already-used scratch storage.
- Empty spans do not need the separation required for nonempty spans.
- A logical capacity may be arbitrarily large even though its limb representation occupies a finite addressable slice.
- A decoder may allocate before discovering a semantic error. Its cursor cannot silently be rolled back in the model.
- A callee may legally clobber caller-saved SIMD state. A contract claiming preservation of all vector registers would be wrong.

For example, `decode_delimited` constructs a two-limb count when necessary before checking the optional limit. That allocation order matters even when the limit is absent or the eventual result is an error.

### Long unchecked chains multiply feedback cost

Writing many downstream modules before checking their prerequisites creates integration debt. A malformed generated expression can cause pages of secondary errors; a missing import or reserved identifier can conceal whether the semantic proof is even being attempted.

The first meaningful compiler error is often more useful than the size of the error log. Fix parse/type errors before analyzing the resulting cascades. Lean's recovery-generated `sorry` terms in a failed compilation are not accepted proofs; the final build and axiom audit must still be clean.

The next ARM addition proof made this concrete: a monolithic execution module hit a 300-second deadline. Splitting it by instruction family exposed six successful families checking in 1.5–2.4 seconds each, while move/flag obligations remained isolated failures. That is improved fault localization, not a completed execution proof or a measured total speedup. A separate generated division opcode syntax error cascaded into enormous downstream goals; those failed builds and recovery terms do not count as verified coverage.

### Image construction can also be expensive

Binding proofs have to connect the modeled instructions to the actual linked image. Two separately satisfiable `CodeAt` predicates do not by themselves establish that caller and callee fit in one consistent image.

The delimited decoder calls a comparison helper at a negative relative offset. Its x86 joint witness required distinct function-local label names and the real bytes between the functions. Embedding the whole gap as one large literal caused code-generation and simplification recursion problems.

Chunking the actual gap bytes bounded literal depth. Making the combined executable a proof-only, `noncomputable` definition avoided unnecessary runtime code generation; the witness was still reduced and checked by the Lean kernel. Neither change replaced gap bytes with invented instructions or added a correctness assumption.

The next arithmetic dependency exposed a different binding issue: x86 LLD relaxation emitted two six-byte `addr32 callq` instructions to `__udivti3`. The extractor classified only the outer mnemonic and initially missed both calls. It now classifies the underlying instruction while retaining the original bytes and disassembly. Executing extraction against the real linked function verified both edges and rejected the same function when the callee was undeclared. Binding discovery is not a Nat-division refinement proof; instruction prefixes must not silently hide proof dependencies.

Private Rust ABI and compiler-specialized domains must be recovered from the shipped image, not guessed from C ABI conventions or source signatures. An arithmetic probe confirmed x86 result reason at byte 64, but a guessed ARM C-style hidden result in X8 crashed: the shipped Rust helper takes the output pointer in X0. The same probe found that calling the shipped division helper with divisor zero does not implement the source error branch. Its entry has no zero/one guards; production callsites use divisors 8, 32, or 256. The ISA contract must establish the production divisor domain at callers, rather than claiming unrestricted source refinement for an optimized private helper. These probe findings are not completed arithmetic execution proofs.

The corrected arithmetic harness then passed 1,536 direct private-helper calls per ISA, checking values, borrowed/allocated representations, full error payloads, alignment, exact cursor changes and written limbs, unchanged inputs, and output/arena guards. The shared addition/division models passed the same 1,536 resource cases plus 3,072 source-only zero/one-divisor cases on each Lean toolchain. Their general arithmetic/resource theorems now pass both root axiom audits. Addition's complete linked images also have checked CodeAt witnesses (383 x86 instructions; 603 ARM instructions). Those checks alone did not establish arithmetic execution; the subsequent x86 division closure is recorded below.

ARM disassembly encodings and raw section bytes have different representations: a row's eight hex digits already denote the instruction word, whereas raw section bytes require little-endian decoding. A reversed-word generation error was caught and corrected before use; the corrected 282-word division image and the actual 65-word runtime callee now have checked CodeAt witnesses in the same ARM Program. Reuse the binding generator's existing encoding conversion rather than independently guessing byte order.

Both complete division images now have checked joint caller/runtime witnesses: 221 caller instructions plus 66 runtime instructions on x86, and 282 plus 65 on ARM. The binding command passed in 168.79 seconds. For x86, reducing the standalone runtime layout required `instances := true` during simplification, not just an initial `dsimp`: otherwise later layout projections remained opaque and expanded the finite witness until its step limit. The fix exposed the existing instance; it did not raise limits or change code.

**Both complete division helpers are now checked and integrated.** x86 `NatDivision.divide_correct` and ARM `NatDivision.program_correct` execute the actual entry through RET, including actual `__udivti3` calls in the same executable/program, for divisor ≥ 2 and arbitrary physical Small/Large representations, including empty and redundant-zero lists. Their postconditions retain the exact shared outcome, all allocated quotient limbs before normalization, cursor, original operand, memory frame, SIMD and callee-saved state. ARM imposes neither a signed-capacity restriction nor `used ≤ capacity`. The x86 final large-phase module passed in **1.0 seconds**, its aggregate in **797 ms**, and its integrated strict root audit in **807 ms**. ARM's final aggregate passed in **599 ms**, and its integrated strict root audit in **808 ms** (328 dependency jobs). These are incremental timings with dependencies already checked. ARM addition, BitVector composition, and the broader SSZ refinement remain incomplete.

### ISA model corrections change the recorded trust baseline

The pinned LNSym logical-immediate interpreter incorrectly read SP for some Rn31 sources, including the actual SSZ instruction `0xb27fefe9`. Architectural Rn31 is XZR/WZR for these source operands; destination handling is different and must remain unchanged: non-flag-setting logical operations may write SP, while ANDS with Rd31 discards the result and updates NZCV. See the [ARM ORR-immediate reference](https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/ORR--immediate---Bitwise-OR--immediate--?lang=en).

The user explicitly approved a tracked model correction rather than changing shipped assembly or imposing an artificial SP precondition. The ARM baseline is now commit `df80e2f600dc7f2976809829198a1d9fd07cb379` **plus** [the recorded patch](patches/lnsym-logical-immediate-rn31.patch), SHA256 `0586e9185877634896931dcbed0d55f03ccc5c8c22f33da77a7b9b10f885ab3c`. [sources.lock.json](sources.lock.json) records the patch and pristine/corrected source hashes; `make models` verifies the base revision and hashes, rejects unrecorded tracked changes, and applies the correction reproducibly.

The behavioral regression executes 32 real instruction words across 2,048 cases, covering all four logical-immediate operations, both widths, source Rn31 and ordinary-register controls, destination SP/ZR distinctions, and every incoming NZCV value. Before correction, native A64/QEMU passed but LNSym disagreed in 960 cases. After correction, native, model, and independent bitwise expectations agreed in all 2,048 cases. `make model-check` also passed three kernel-checked whole-state regression theorems: the actual MOV for arbitrary state/SP, ORR's SP destination, and ANDS's discarded destination plus replacement flags. The shipped assembly is unchanged. The corrected-model ARM root and strict axiom audit subsequently passed all 242 dependency jobs, including the previously completed runtime, scalar/byte-view, comparison, and delimited proofs.

Patch preparation was also exercised on an isolated pristine pinned checkout: first application and idempotent reuse passed; modified target contents, unrelated tracked source changes, and patch tampering were rejected without overwriting them. The missing-checkout network-fetch branch was not exercised.

Changing the model invalidates substantial proof dependencies. The first corrected-model arithmetic closure check took 957.31 seconds and failed in unfinished composition modules, although the actual MOV and flag instruction families passed in 1.7 and 1.6 seconds. Rechecked older comparison modules still took 126–143 seconds each; a new allocation-check module took 181 seconds. The subsequent successful completed-proof root check took 377.30 seconds, dominated by the existing byte-view control-flow module at 369 seconds. These costs are not a measured shared-model speedup. A separate invocation lesson: `lake -d backends/arm` from the repository root does not select that directory's Elan toolchain. One attempted audit therefore used Lean 4.34.1 and failed in the pinned 4.31 model; launching from `backends/arm` selected the correct toolchain and passed.

The shared addition and division ownership bridges now also pass both kernel/root audits: original operand observations plus observations of every allocated written limb imply ownership of the exact returned operand. They reuse normalization and do not discard redundant high-zero scratch writes. The x86 addition return proof consumes its bridge; this is actual reuse of a checked memory-representation fact, not a whole arithmetic execution theorem.

A separate native smoke exercised the division theorem's wider divisor domain, rather than only production divisors 8, 32, and 256: **704 calls passed on each of x86 and ARM/QEMU**, using 32 divisors from 2 through `2^64-1` and 22 physical operand representations, including empty/padded Large values and five-limb inputs. Independent Python integers supplied exact quotient/remainder and allocation expectations. The harness checked normalized output metadata, all allocated quotient limbs, cursor, unchanged arena base/capacity and input words, and output/scratch guards. This is finite evidence for the divisor-at-least-two contract, not a substitute for whole-helper proofs. Temporary harnesses and executables were removed.

The next BitVector leaves have a checked shared narrowing contract: significant limb count bounds are equivalent to numeric bounds; `to_u128` succeeds exactly for values below `2^128`; `codec::exact` succeeds exactly when the expected arbitrary-precision value equals the actual 64-bit length. Both kernels and strict root audits passed. Actual linked image/CodeAt checks passed for all four leaf images in **10.61 seconds** (x86 exact/to_u128: 53/39 instructions; ARM: 74/96). This does not yet prove execution of those leaves.

The ABI smoke confirmed an important contract detail before those execution proofs: `Option<u128>` has a **16-byte discriminant**, and None writes both halves while leaving its payload untouched. Exact-size success writes only the 32-bit status at byte 64; failure retains the original expected Nat pair, including redundant physical limbs. **82 narrowing plus 386 exact-size calls passed per ISA**, checking every output byte against independently generated expectations, untouched payload/guards, original pair, and read-only limb arrays. The shared models passed the same cases on both toolchains. Cases include empty/padded Large operands, the `2^128` boundary, and up to 35 physical limbs. Temporary sources, objects, executables, and model probes were removed. Whole-leaf execution proofs remain separate work.

### Measured bottleneck signature in the current arithmetic frontiers (2026-09-27)

A coordinated diagnostic pass by a bottleneck monitor (read-only on live trees; isolated `/tmp` probes against frozen ARM oleans, Lean 4.31.0, load 7–17 concurrent, single runs) examined the two recurring failure classes that dominate relay iterations, plus one clean elaboration measurement. Timings are single-run wall-clock on a busy shared machine; treat deltas as order-of-magnitude, not benchmarks.

**1. Projection-shape residuals, not semantic gaps, are the recurring failed-elaboration class; broad `simp` is expensive where the targeted lemma is cheap (measured 35× on one goal; a recurring pattern, not a frequency claim).**

Paired probes against frozen oleans (same goal, different proof), files under `/tmp/pbm-exp/e1_*.lean`, reproduction below:

- `r StateField.ERR (block base [Op.p1980, Op.p1984] s) = r StateField.ERR s` — the exact residual of the failed `NatAddSmallLoopFrame` 76:4 (bg937): broad `simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]` took **19.6 s**; `exact block_error base ops s` (the existing `@[simp] block_error` fold lemma in `NatAddOps.lean`, which bare `simp` never fired because `read_err` is a `state_simp_rules` definition, not default-simp) took **0.56 s**.
- `(write_pstate ps (w .PC pc s)).mem a = s.mem a` — the residual shape of failed `NatAddSmallLoopFrame` 92:8: a `rw`-chain through the existing `mem_w_of_mem_eq` (lnsym `Arm/State.lean`) took **0.65 s**; inline `unfold write_pstate w write_base_*; simp` took **0.84 s**; a reusable per-op invariance lemma (16-op `cases`) proved in **0.3–0.7 s** and then applies in milliseconds. Bare `rfl` (what bg937 tried) is a dead end here.

**2. A surface error near the top of a heavy module is discovered only after the module's elaboration work — measurement method and exact scope below.**

Method: each defective variant of `NatAddLargeLoopSelect` (accepted **137 s** ARM module, copied to `/tmp`) ran `lean` via Python `subprocess.Popen` with merged stdout/stderr; the recorded figure is the wall-clock time at which the **first line containing "error" appeared on the stream** (not merely process total). The defect was injected at **line 10, immediately after the `set_option` lines near the top of the file** — i.e., before most declarations. A reserved-token parse error (`def prefix : Nat := 0`) was first reported at **133.8 s** and an unknown-identifier error at **128.2 s**; the clean module (no defect) completed in **124.0 s**. Both defective runs therefore paid nearly the full clean-module elaboration before surfacing the error: Lean continues elaborating after parse errors, and the unknown-identifier case requires elaboration by nature. Control: the same file's imports alone elaborate in **0.55 s**, so the cost is the module's own elaboration, not import loading. Consequence (proposal, not measured): a sub-second parser-only pre-check would catch the reserved-token class cheaply; it cannot catch unknown identifiers or missing tactics, which need elaboration — and the "~130 s avoided" saving is extrapolated from this single module, not established end-to-end. bg943's x86 leaf failures (1.3–2.2 s literal-indentation/reserved-token errors) were cheap to fix only because those modules are small.

**3. A clean 137 s module is normal for state-heavy proofs; olean size is a cheap smell for it.**

`NatAddLargeLoopSelect` elaborated in **124.0 s** standalone (single run, load 13, no edits). State-heavy ARM modules store **85–180 MB** oleans (`NatAddReturnStatus` 180 MB, `NatAddArenaChecks` 173 MB, `NatAddBlocks` 128 MB; 23 modules ≥ 50 MB, 2.28 GB of a 3.58 GB build lib) while composition modules reusing opaque contracts store **30–200 KB** (`NatAddOneWord` 31.8 KB, `NatAddFirstWord` 98 KB) and check in **<1 s**. Division-side modules measured 20–31 MB (with the state-observation exception `NatDivisionLargePost` failing at 366 s — size alone is not a guarantee). The 85–130 MB / 60–274 s tier (`NatAddFront` 274 s, `NatAddSelect` 186 s, `NatAddOneWordState` 298 s) is the steady-state cost of state-observation proofs, independent of failures.

**3b. Where the 124 s goes: eight broad-`simp` calls at 13.7–18.6 s each dominate.**

Running the same clean `NatAddLargeLoopSelect` with `set_option profiler true` attributed **125 s of the 127 s wall to `simp`** (cumulative), spread over eight calls of 13.7–18.6 s plus two 0.1 s calls. (Caveat: the profiler's `simp` bucket includes tactic-elaboration work; treat the non-simp remainder as "small relative to simp", not as independently measured exclusive costs.) A state-heavy module's check time is therefore roughly (number of state-touching broad-`simp` calls) × ~15 s on this machine, plus import load. Each heavy call re-expands large ARM state expressions from scratch — the same behavior the E1 pair isolated at 19.6 s vs 0.56 s. The x86 scalar-carry scalarLoop blocker (bg946) showed the identical pattern in miniature: an omega-arithmetic residual buried under state expansion until an explicit fuel rewrite (76AE) closed it at **1.3 s**.

**Historical split outcomes these measurements corroborate** (from parent relay logs): ARM monolith OneWord **744 s** 8M-heartbeat timeout → pure-state module **298 s** + actual execution **659 ms**; FirstWord **760 s** timeout → pure-state **109 s** + actual **693 ms**; RightTrim 8M timeout → state **42 s** + actual **60 s**; OneWordLoadState **77 s** + actual **705 ms**; OneWordLoad **753 s** fail at state-enum × instruction-path simp → helper **77 s** + actual **705 ms**. x86 CarryPair **694 s** timeout → CPS helpers **0.7–3.8 s** each + composition **1.1 s**. ARM division LoopIteration ~**863 s** 12M-heartbeat failure → opaque finish-state summaries **1.1 s**. These are per-module incremental timings, not whole-DAG speedups.

**Failed-check costs in the same runs** (bg937/bg948/bg953): SmallLoopFrame **154 s** fail (repaired to 20 s after opaque cuts, one residual remaining); BorrowTrim **374 s** fail (whnf 8M heartbeat); LargeLoopRead **303 s** fail; LargePost **366 s** fail (126 isDefEq/13 whnf at 8M heartbeats); Maximum 66 s fail; Dispatch 1.1 s fail. Accepted peers: Front **274 s**, Select **186 s**, LargeLoopSelect **137 s**, BorrowTrimState **78 s**, Maximum **79 s**, LargeLoopRead **126 s**.

**Reproducing the measurement method** (after the live tree is idle; run from the repository root). These commands create fresh snapshots and representative probes; the original temporary files were deleted. Timings below are the historical observations, not expected results on a changed tree or machine.

```bash
# 1. snapshot (read-only copy, ~4 GB)
repo="$PWD"
work="$(mktemp -d /tmp/ssz-proof-profile.XXXXXX)"
cp -a "$repo/backends/arm/.lake/build/lib/lean" "$work/arm-lean-lib"
cp -a "$repo/backends/arm/.lake/packages/lnsym/.lake/build/lib/lean" "$work/lnsym-lib"
export LEAN_PATH="$work/arm-lean-lib:$work/lnsym-lib"
lean="$(cd "$repo/backends/arm" && elan which lean)"
cd "$work"

# 2. paired projection probes (identical goals, different proofs)
cat > e1_err.lean <<'EOF'
import SszArm.NatAddSmallLoopControl
import SszArm.NatAddLoopMemory
set_option profiler true
namespace SszArm.NatAdd
theorem err_guard_block (s : ArmState) (base : BitVec 64) :
    r StateField.ERR (block base [Op.p1980, Op.p1984] s) = r StateField.ERR s := by
  simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
end SszArm.NatAdd
EOF
cat > e1_errC.lean <<'EOF'
import SszArm.NatAddSmallLoopControl
import SszArm.NatAddLoopMemory
namespace SszArm.NatAdd
theorem err_guard_block (s : ArmState) (base : BitVec 64) :
    r StateField.ERR (block base [Op.p1980, Op.p1984] s) = r StateField.ERR s := by
  exact block_error base [Op.p1980, Op.p1984] s
end SszArm.NatAdd
EOF
/usr/bin/time -f "%e s" $lean e1_err.lean    # 19.6 s  (broad simp)
/usr/bin/time -f "%e s" $lean e1_errC.lean   # 0.56 s  (targeted lemma)
# mem pair (0.65 s vs 0.84 s): same header + namespace; goal
#   (write_pstate ps (w StateField.PC pc s)).mem a = s.mem a
# cheap side: `unfold write_pstate` then rw [mem_w_of_mem_eq rfl ...] per flag/PC;
# inline side: `unfold write_pstate w write_base_gpr write_base_sfp
#               write_base_pc write_base_flag write_base_error; simp`

# 3. heavy-module baseline and injected-defect variants
cp "$repo/backends/arm/SszArm/NatAddLargeLoopSelect.lean" e2_base.lean
python3 - <<'EOF'
from pathlib import Path
src = Path('e2_base.lean').read_text()
anchor = "set_option maxHeartbeats 8000000\n"
assert src.count(anchor) == 1
for suffix, defect in (
    ('parse', 'def prefix : Nat := 0'),
    ('name', 'def pbm_bad : Nat := pbm_missing_symbol'),
):
    Path(f'e2_{suffix}.lean').write_text(src.replace(anchor, anchor + defect + '\n', 1))
EOF
# Capture first reported error while continuing to drain the entire output.
cat > tstamp.py <<'EOF'
import subprocess, sys, time
t0 = time.monotonic()
p = subprocess.Popen([sys.argv[1], sys.argv[2]], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
first = None
for line in p.stdout:
    if first is None and 'error' in line:
        first = time.monotonic() - t0
        print(f"FIRST_ERROR_AT {first:.2f}s :: {line.strip()[:120]}", flush=True)
code = p.wait()
print(f"TOTAL {time.monotonic() - t0:.2f}s EXIT {code}", flush=True)
sys.exit(code)
EOF
python3 tstamp.py "$lean" e2_base.lean   # historical total ~124 s
python3 tstamp.py "$lean" e2_parse.lean  # expected failure; historical first error ~134 s
python3 tstamp.py "$lean" e2_name.lean   # expected failure; historical first error ~128 s

# 4. profiler attribution of the clean module
python3 - <<'EOF'
s = open('e2_base.lean').read()
open('e2_prof.lean','w').write(s.replace(
  "set_option maxHeartbeats 8000000", "set_option maxHeartbeats 8000000\nset_option profiler true", 1))
EOF
$lean e2_prof.lean 2>&1 | grep took   # simp ~125 s of 127 s wall
```

**Rejected hypotheses:** (a) "surface errors are found fast anyway" — measured 128–134 s time-to-first-error on a heavy module with a top-of-file defect; (b) "import loading dominates heavy-module time" — imports-only control elaborates in 0.55 s; (c) "state-projection residuals need new model lemmas everywhere" — `mem_w_of_mem_eq`, `block_error`, and `block_program` already exist; the gap is routing and simp-set membership, not missing model support; (d) "`simp_all` suffices if you wait" — repeated op×StateField expansion is the measured burn (OneWordLoad 753 s failure).

**Default workflow implied (proposal; the pre-check tool is unimplemented and the end-to-end saving unmeasured):** add a sub-second parser-only pre-check (catches reserved-token/syntax class only, not unknown identifiers or tactics) before queuing expensive builds; state goals via the pre-existing fold/projection lemmas (`block_error`, `block_program`, `mem_w_of_mem_eq`, `read_mem_bytes_of_w`) instead of re-deriving per module; treat 85 MB+ oleans as the "this module will check in minutes" signal and plan opaque-cut splits before the first 300 s+ failure, not after several.

**Coverage update (2026-09-27, from parent relay reports):** the complete x86 `NatToU128`/`NatExact` leaves now pass (bg979: 696/759 ms) with entry-through-RET physical `Owned` + `CodeAt` only, precise `None`-payload/success-status frames; the integrated strict x86 root passed (bg982, 925 ms). The shared `SszBitVector` `run_refines`-to-pinned-SSZ, `run_scratch_iff`, and `rounding_failure_no_rollback` passed on both toolchains (424/432 ms) and both root audits passed (bg982/983); this is not yet a BitVector ISA proof. A new independent Python-oracle smoke passed **3,751 entire private BitVector calls per ISA** (x86 + ARM/QEMU) and the same 3,751 shared-model cases on both toolchains, including 52 two-successful-reservation and 72 second-reservation-fail-retaining-first cases with exact allocation buffers, guards, original descriptor, arena base/capacity/used, `ScopeNat` metadata, and borrowed pointer/count. Two authoring notes from that smoke: a 3,751-row Lean array hit `maxRecDepth` and was fixed by chunking 64 rows per definition **without raising limits**, and the reserved identifier `matches` had to be renamed. Whole ARM narrow/division and both addition proofs remain pending.

**Applied projection-cut result:** ARM `NatDivisionLargePost` still failed after **351 seconds** when its new observation helper remained inside the heavy composition module. Moving that helper to `NatDivisionNormalizeStore` and using explicit `r_of_w_different`/read-after-write projections let the helper check independently in **679 ms**, then the repaired caller in **899 ms**. The complete division closure passed in **4.39 seconds**. No instruction, public contract, or proof limit changed. This is a successful local repair with warm dependencies, not a controlled clean-build or overall-project speedup. ARM `NatToU128.to_u128_correct` also passed in **658 ms**, including precise None-payload preservation and the actual return; its integrated strict root audit subsequently passed in **3.2 seconds**.

**Subsequent arithmetic closure:** x86 `NatAdd.add_correct` and `add_correct_value` now prove the entire 383-instruction helper through RET, including scalar/paired carry loops, exact reservation/cursor/full written-buffer effects, preserved original operand representations, frame and ABI. The `used ≤ capacity` premise is the existing public scratch invariant (`include/ssz.h:41–42`), not a new signed-capacity restriction. The final module checked in **751 ms**, and the integrated strict x86 root in **1.2 seconds** (649 dependency jobs). Shared `SszBitVectorMemory` then supplies the exact borrowed-pointer and expected-Nat-pair result contract, both allocation write observations, and a memory bridge to SSZ; it passed both toolchains in **526/469 ms** and the x86 root audit. ARM exact-size finishing and addition remain open. None of these helper closures establishes the still-pending BitVector assembly composition.

**BitVector call-closure binding:** `check-bitvector-binding.py` passed end to end in **346.94 seconds**, binding 228 x86 or 239 ARM postdispatch body instructions together with all four actual Nat helpers, transitive `__udivti3`, and ARM `memcpy`. Every component uses its actual linked offset and bytes; x86 retains all intervening bytes. The command is included in `make binding`. A first x86 witness exhausted the simplifier step limit after **391.46 seconds**. Checked address-table equalities now normalize the executable and runtime layout once before the finite row lookups; no proof limits were raised and no table is assumed correct. These are instruction-image witnesses, not the still-open BitVector execution refinement.

**ARM exact finishing cut:** the original `NatExactFinish` expansion timed out after **1,200 seconds**. Factoring state-field/store commutation, symbolic GPR reads, spill readbacks, fixed register restoration, and opaque per-cut vector preservation produced a complete State+Finish checkpoint in **12.69 seconds**; appending `NatExactProofs` also passed in **12.69 seconds** against accepted dependency oleans. `NatExact.exact_correct` covers the actual entry through RET, including empty/padded Large operands, the original expected pair, precise success/failure output writes, and ABI preservation. These are successful direct Lean checkpoints, not yet the standard Lake/root integration or a controlled clean-build speedup. Comparison-dependent builds remain held while the GLM comparison optimization is being edited.

**User-reported comparison profile (not rerun as a baseline):** `NatCompareBlocks` took **263 seconds**, with **249 seconds in `simp`** and **1.6 seconds in kernel type-checking**. The reported declaration timings were `load_run` **223 seconds** and `readonly_frame` **62 seconds**. This identifies proof construction, not trusted kernel checking, as the dominant cost in that run. The compiling symbolic GPR read-over-write repair reduced `load_run` to **103 seconds**, replacing 384 broad simplifier branches with one symbolic simplification per load kind and splits only over written registers; it also clears the large execution/image hypotheses before `simp_all`. The reported remaining component expansion is about **88 seconds**. Expanding once per kind hit the heartbeat limit and was discarded. The next optimization targets are effect-shape preservation lemmas and reusable component observations; merely moving the old case matrix into a helper is not an established improvement. `NatCompareTrim` (**338 seconds**) and `DelimitedTailContracts` (**236 seconds**) are reported next candidates, not yet profiled or diagnosed.

**Applied comparison optimization (GLM 5.3 Flash implementation, parent compiler relay):** the complete `NatCompareBlocks` now passes `lake env lean -Dprofiler=true SszArm/NatCompareBlocks.lean` in **5.82 seconds**, with cumulative `simp` **4.53 seconds** and kernel type-checking **196 ms**. Rechecking the reused `NatAddLoadState` independently costs **1.66 seconds** (`simp` **357 ms**); even counting that existing helper again gives **7.48 seconds** combined wall time. These new measurements are compared with the user's reported baseline above, not a rerun or controlled clean-build benchmark. The change composes PC/GPR/flag effect-shape frame lemmas, excludes real stack writes from the readonly lemma, and proves all six load kinds through the existing checked indexed-load state summary. Existing public theorem statements and proof limits are unchanged. A first dispatch candidate failed after **182.14 seconds**, spending **179 seconds** in `exact`/unification while attempting the wrong effect shape; `with_reducible` prevents those attempts from expanding the entire architectural state. The dependent Lake build and strict root integration are pending.

**Call-composition contract gap:** the next BitVector body proofs exposed two facts that coarse leaf postconditions do not imply. On x86, a frame permitting writes to the whole helper output/activation cannot establish that all previously mapped bytes remain mapped after an opaque helper call; observing the result fields covers only part of those regions. On ARM, returned registers and memory observations do not establish that the separate instruction map is unchanged. The body proofs are deriving these from actual execution semantics, rather than adding post-execution ownership or code-preservation assumptions. These invariants are not yet checked. The public aliasing contract already requires the available scratch suffix to be disjoint from inputs (`include/ssz.h:35–42`); it explicitly permits immutable aliases and used-prefix borrowing. Requiring the whole scratch capacity to be disjoint would incorrectly exclude those supported aliases.

**Dependent integration completed:** the comparison-dependent ARM rebuild accepted `NatCompareBlocks` in **7.1 seconds**, the complete comparison proofs, and the strict root in **1.3 seconds**. It also accepted the actual `NatExactState` (**1.0 second**), `NatExactFinish` (**18 seconds**), and `NatExactProofs` (**819 ms**) modules; ARM exact-size refinement is now root-imported and axiom-audited, superseding the checkpoint-only status above. The larger combined command took **1,579.45 seconds** and failed on four separate ARM addition integration frontiers, so it was not an overall successful build. The unchanged `NatCompareTrim` rebuilt in **185 seconds**, but this is not a tactic-attributed profile or evidence that its implementation was optimized.

**Checked reusable call invariants:** `SszX86.BitVector.Mapping.retains_mapping` now strengthens actual Kraken executions with retention of every previously mapped address; the scalar instruction proof checked in **2.4 seconds**, the full AVX/directive/execution closure in **746 ms**, and its strict root audit in **795 ms**. `SszArm.BitVector.run_program` proves instruction-map preservation for every actual LNSym instruction, step, and run; it checked in **9.6 seconds** and its strict root audit in **812 ms**. These close the invariant gap above without weakening leaf contracts or assuming post-execution ownership. The ARM proof needed program-only projections, an opaque decoder-pair projection, and optional post-split simplification: a no-progress `simp` inside `first` otherwise rolled back successful case splits. Broad context simplification had also unfolded irrelevant value computations and hit recursion limits; no proof limits were raised.

**Shared arithmetic and physical padding:** the BitVector ceiling/remainder and exact-success-to-u128 facts were moved from the x86 proof directory into the existing shared `SszBitVector` model, with no compatibility module. Both kernels accepted the shared version (**439/486 ms**), followed by both strict root audits. The actual outer error copy writes **80 bytes**, even though the final observed reason is only the 32-bit field at offset 72. ARM's 72-byte copy to `out+8` and paired status/padding stores, and x86's padding-word copy, must remain inside the physical output footprint. Semantic field observations alone do not justify narrowing that footprint to 76 bytes or treating copied padding as initialized.

**Both-ISA addition closure:** the complete ARM `NatAdd.add_correct` and `add_correct_arithmetic` entry-through-RET theorems now check (**855 ms**) and are imported by the strict ARM root (**1.4 seconds**, including the axiom audit). This closes the ARM addition gap above: division for production divisors ≥2, addition, narrowing, and exact-size checking now have whole-private-helper proofs on both ISAs. The final integration failures were representation projection normalization, terminal list-membership disjunctions, dependent `Fin` rewrites, and omitted simplification of `True ∧ True`; no execution premises or proof-limit increases were added. BitVector whole-body composition remains open.

**Cache decoded instructions; normalize memory as memory:** the ARM BitVector five-instruction division-status block checked in **6.7 seconds** after replacing computed `Option.get (decode_raw_inst word)` instruction fields with literal decoded ASTs carrying kernel-checked `rfl` decoder witnesses. Proving the generic `Option.get` witness via `Option.some_get` was necessary but did not itself stop repeated decoder reduction during execution simplification. The existing `Memory.write_mem_bytes_eq_mem_write_bytes` lemma then reduced a store to one memory-only record update; recursively unfolding `write_mem_bytes` instead left irrelevant old-PC differences buried beneath memory writes. The x86 full division-error copy checked in **5.3 seconds** after `with_reducible` prevented final state matching from recursively unfolding memory, exposing the actual missing equality: the signed 32-bit stored reason was an integer `bmod`, while the summary used `BitVec.toInt`.

**Distinguish instruction execution from static membership work:** isolated x86 macro expansion located a default-depth recursion failure in `by decide` for `index < program.length`, before instruction execution. A selected literal row still needs membership evidence, but the instruction AST has no computable equality instance for deciding list membership. `List.getElem_mem` plus definitional equality supplies that evidence; caching `program.length = 228` with `by rfl` avoids re-deciding the full table length. In this case the bare term `:= rfl` still hit elaborator recursion, while the tactic form checked. Restoring explicit label-table normalization also removed a stuck `labels.filter`. The resulting actual constructor TEST/JE path checked at unchanged default limits in **0.95 seconds**; the decoder module checked in **845 ms**. Remaining consumer failures were finite state, cast, and memory-effect goals, not recursion. Diagnostic sources were removed.

**Normalize branch evidence, not just the destination state:** the x86 BitVector SHR/TEST/JE block left an actual flag condition `(StatusFlags.from_result shifted flags).zf = true` in context while its continuation selected the destination with `shifted = 0`. Repeated state simplification did not bridge these differently shaped conditions. A single-branch diagnostic exposed the mismatch; unfolding `StatusFlags.from_result` in the branch hypothesis closed the complete padding-tail execution proof in **5.3 seconds**, without changing limits or adding premises. The diagnostic source was removed; whole-body composition remains open.

**ARM BitVector body closure:** `SszArm.BitVector.program_correct` and `program_refines` now cover the actual postdispatch entry at `base + 428` through the real RET. The checked theorem derives every helper call, branch and resource invariant from original physical ownership and linked code; it preserves both complete allocated buffers, including high zero words, through later rejection. The final body and public theorem modules checked in **722 ms** and **689 ms**; strict root import and transitive axiom audit passed in **1.5 seconds**. Public dispatch and the x86 whole-body composition remain open.

**Bind actual tail calls explicitly:** the BitList wrapper calls the delimited helper, while ProgressiveBitList restores the caller activation and jumps directly to that helper on both ISAs. The shared extractor now records an unconditional external branch only when its target is an explicitly allowed callee. Actual linked-image smoke runs selected **30 x86 instructions** and **26 ARM instructions**, each with one tail call; the same real tail target was rejected on each ISA when omitted from the allowlist. This is binding evidence, not wrapper execution refinement.

**x86 BitVector body closure and bounded composition:** `SszX86.BitVector.wholeprogram_correct` and `program_refines` now derive actual postdispatch entry `base + 115` through RET from only original ownership and joint code binding. All division, optional rounding, exact-scope, padding, and constructor paths retain both complete allocated buffers, exact cursor/no-rollback effects, original inputs, and ABI frames. The final success composition initially exhausted the unchanged **200,000-heartbeat** limit while unifying expanded memory states; an explicit stack projection and opaque memory equality reduced the accepted module to **684 ms**. The final theorem module checked in **586 ms** and the strict x86 root/transitive axiom audit in **1.0 second**. Together with ARM, both BitVector bodies are now closed; earlier dispatcher execution and whole-library refinement remain open.

**Bit-list wrapper joint binding:** the new `check-bitlist-binding.py`, wired into `make binding`, checks one actual linked image containing the wrapper, Delimited, and NatCompare on each ISA. The x86 witness passed for **30 wrapper instructions / 60,073 linked bytes**. The ARM witness passed for **26 wrapper instructions / 70,952 linked bytes** after adding the missing explicit NatCompare image import; the successful x86 check was not rerun to diagnose that ARM-only failure. Both include the real progressive tail jump and shared helper code. Temporary witnesses are removed automatically. Wrapper execution/ownership proofs remain separate work.

**ARM BitList and ProgressiveBitList wrapper closure:** `SszArm.BitList.program_correct`, both kind-specific execution theorems, and both pinned-SSZ corollaries are now strict-root audited. The proof executes the actual seven-instruction Some-cap setup/BL and ten-instruction progressive restore/tail-B, derives helper ownership rather than assuming it, and reaches the original caller's RET. It retains arbitrary cap representations, original borrowed input, exact committed scratch/cursor effects, descriptor/input preservation, and ABI restoration; the progressive path correctly permits reuse of the old activation after restoring it. The final theorem module checked in **692 ms** and strict root audit in **1.5 seconds**. x86 wrapper composition and earlier private-function dispatch remain open.

**Bind dispatcher data as well as instructions:** `check-dispatch-binding.py` passed both actual linked images in **6.37 seconds**: **15 x86 entry instructions**, the real **52-byte signed-offset jump table**, and **24 ARM entry/branch instructions**, with all seven primitive body frontiers checked. The x86 lowering now accepts only the observed byte-validated RIP-relative LEA, signed indexed MOVSLQ, and register JMP forms; mismatched encodings were rejected in a throwaway smoke. Displaced terminal coordinates let the extractor stop before the indirect jump without pretending it is a direct edge; an actual mid-instruction terminal at byte 42 was rejected. The final indirect instruction is bound from its exact bytes and its target remains a machine-proof obligation. Existing body/callee closure checks remain separate.

**First original-entry decoder closures:** the ARM Boolean, ByteVector, ByteList, and BitVector theorems now execute from the real private `codec::deserialize` entry at `base + 0`, not an assumed postdispatch state. The prologue derives saved-register memory, the actual branch tree selects the accepted body, and original physical ownership derives body ownership. Each result retains original return/SP/register restoration, native writes and immutable inputs; BitVector retains both full scratch allocations and the pinned-SSZ/resource split. Their strict root import/transitive audit passed in **975 ms**. This does not close the external C ABI/schema-construction wrapper, remaining decoder kinds, or serialization.

**x86 bit-list wrapper closure:** both actual BitList and ProgressiveBitList postdispatch paths now have strict-root-audited execution and pinned-SSZ refinements, including the real CALL versus restore/tail-JMP distinction. Original ownership derives helper ownership; input/descriptor bytes, borrowed pointers including empty results, complete committed count limbs, exact cursor/no-rollback effects, and original return/ABI frames are retained. Final execution/refinement/resource modules checked in **804/663/687 ms**; strict root audit passed in **807 ms**. This closes both ISAs' primitive postdispatch decoder bodies, not the external decoder API.

**All seven ARM private decoder entries:** `SszArm.DispatchProofs` now composes actual PC0 prologue/tag dispatch through RET for Bool, UInt, both byte views, BitVector, and both bit-list variants. UInt ownership protects original width limbs from actual cursor/free-suffix writes while permitting used-prefix/read-only aliases and noncanonical representations; its final postcondition preserves every width-limb byte and descriptor Nat. The aggregate checked in **642 ms** and the strict root/transitive axiom audit in **1.1 seconds**. Bit-list address-preservation rewrites were kept outside expanded `read_mem_bytes` applications: explicit congruence reduced the accepted post module from a heartbeat failure to **752 ms**, without changing limits. Composite tags and the external C/schema wrapper remain outside this coverage.

**Serialization artifact boundary and real constructor prerequisite:** the shipped images contain standalone `measure`, `emit`, and `serialize`, but no observed standalone/call-site `encoded_size`; `serialize_alloc` is evidenced only as a bit-view inlining inside `json_of`, with a JSON continuation rather than its own RET. Source-model proofs must not invent missing ISA entries. The actual standalone `Nat::from_u128` images have now been extracted and byte-validated: **47 x86 instructions / 177 bytes**, **105 ARM instructions / 420 bytes**, complete entry0 control flow with no callees/frontiers. ARM passes the 128-bit argument in **X2/X3**, not X1/X2, and its lowered stores use real SP−16 scratch. Constructor execution proofs are separate pending work.

**Native wide-constructor binding and smoke:** the consolidated `check-nat-conversion-binding.py` now checks exact/to-u128/from-u128 images on both ISAs and passed all six actual CodeAt witnesses in **21.10 seconds**. The real private `Nat::from_u128` was separately executed **82,656 times per ISA**, covering eight base alignments, capacities 0–40, every cursor within each capacity, Small and wide inputs, exact successes and exhaustion. The throwaway C harness checked every result byte (including untouched padding), complete scratch bytes, cursor, and base/capacity preservation; ARM used QEMU. Use the established LLVM assembler for the shipped assembly and export the private symbol only in a temporary object. No native/source artifact was changed; the temporary harness was removed. Execution/resource proofs remain separate from these finite checks.

**Primitive serialization model closure:** the five `SszSerialize*` modules now have checked pinned-spec correspondence for all seven primitive kinds, wrong value kinds, arbitrary padded Nat operands, dirty packed-bit tails, and exact ordered measurement/host/output/byte-allocation outcomes. Public resource iff contracts prevent hiding semantic errors behind unconstrained host failures; traces retain full helper reservations/written limbs and earlier commits. The Option-valued output model proves prefix initialization without reading old output contents, untouched tails, and unchanged output on pre-emission failure. Both strict roots passed (**2.1 seconds x86 / 2.3 seconds ARM**). Executable smoke compared **1,528 cases per toolchain** against pinned serialization and exercised output shortage, final byte exhaustion, and zero allocation. Additional checks distinguished logical width **2^63** (host size succeeds, physical byte allocation fails) from width **2^64** (host conversion fails first), and confirmed zero byte allocation returns pointer **1** without inspecting positive-allocation guards or changing the cursor. These are logical-model proofs, not serializer ISA/ABI certificates.

**Actual primitive emitter extraction and smoke:** selected original-entry paths contain **276 x86 instructions** and **336 ARM words**, including the real x86 value-tag indirect jump and its actual 16-byte table (destinations 256/414/307/347). The x86 lowering accepts all observed emitter instructions; all 276 ASTs compiled, nine corrupted table-opcode encodings were rejected, and the existing two-ISA dispatcher binding regression passed in **6.11 seconds**. Both new emitter image modules compiled (**914 ms x86 / 1.7 seconds ARM**); these are image definitions, not completed execution refinements or joint binding witnesses. The real private emitters each passed **5,468 calls**, including padded UInt operands/widths, zero extension, empty/aligned/dirty bit tails, optional progressive caps, exact output length and spare capacity. The temporary native harness checked all result/output bytes, untouched padding/tails, and descriptor/value/backing/Nat-limb preservation; ARM ran under QEMU. Temporary artifacts were removed. Emitter execution refinements remain open.

**x86 wide-constructor execution closure:** `NatFromU128Corollaries` now composes all 47 actual instructions from original entry through the real RET, with exact `fromWide` result/cursor, complete two-word allocation, result-padding frame, preserved arena header, and original ABI. Allocation failures preserve every non-result byte; the separate Small theorem requires no arena/header premises. Original ownership does not assume allocator success or `used ≤ capacity`. Final entry/refinement and resource corollaries checked in **790/676 ms**; the strict root/transitive audit passed in **954 ms**. Earlier six-image binding and **82,656 native calls per ISA** remain the runtime/binding evidence; ARM constructor execution is still pending. Typed scalar memory equalities avoided pair-projection rewrite mismatches, and explicit UInt64/BitVec Nat bridges closed physical interval goals without expanding machine states or raising limits.

**ARM wide-constructor closure and bounded emitter binding:** the complete 105-word constructor now has checked original-entry execution, exact `fromWide` result/resource observations, full allocated-word ownership, original LR/SP/ABI, and actual SP−16 scratch framing. The final proof/resource/model modules checked in **1.3 seconds / 1.0 second / 960 ms**; the strict root audit passed in **2.2 seconds**. Both constructor ISAs are now root-audited; their earlier native/binding evidence remains applicable because native assembly was unchanged. Separately, `decoder_arm_binding.emit_source` passed its generated joint CodeAt witness for **336 actual emitter words plus 14 actual memcpy words**. Flat lookup checks exceeded recursion depth; bounded 64-row suffix equalities, ordered segments, and a generic map-lookup lemma closed the same witness at default limits. The combined two-ISA emitter binding CLI and emitter execution refinements remain pending.

**Eval isolation hazard observed during parallel proof work:** retained Python globals were shared across task agents in this run. Reusing a generic `patch` variable accidentally applied another agent's intended patch; the edit was identified, retained by its owner, and its generator exercised successfully. Use uniquely named, single-call function-local scopes for Eval work, especially across `await`; reconstruct each tool payload locally immediately before calling it. Prefer direct anchored edits. Do not assume retained globals belong exclusively to the current agent.

**All seven x86 private decoder entries:** `SszX86.DispatchProofs` now composes original entry through the real prologue, descriptor load, RIP-relative table lookup, signed32 extension, indirect jump, primitive body, and RET. Original ownership derives body ownership and saved-register observations; results retain existing pinned/resource refinements and add original return/SP/ABI, all original read-only regions, and all **52 actual table bytes**. Read-only aliases and used-prefix storage remain allowed; UInt retains its existing physical input-size bound. Final UInt/BitVector/aggregate modules checked in **639 ms / 5.1 seconds / 549 ms**, and the strict root passed in **801 ms**. Both ISAs now cover all seven private primitive decoder entries. Composite codecs and the external C/schema wrapper remain outside this closure.

**Permanent joint primitive-emitter binding:** `scripts/check-emit-binding.py`, now included in `make binding`, passed both toolchains in **89.87 seconds**. The x86 witness binds all **276 selected actual instructions**, **19 actual memcpy instructions**, real intervening linked bytes, and **16 read-only table bytes** in one executable; the ARM witness binds **336 emitter words plus 14 memcpy words** in one program. Helper labels/layout are checked against the accepted runtime, not assumed from a call name. The x86 structural executable is noncomputable because no generated checker machine code is required; all witness equalities still use kernel proofs, with existing proof limits unchanged. Layout-instance reduction must be enabled explicitly for linked helper lookups. Execution refinements remain in progress: this binding result does not establish entry-to-RET behavior. Preserve active descriptor/value observations and every original Nat limb/backing byte; inactive object padding is framed only outside actual writes. Untouched supplied output tails additionally require separation from result/status and activation writes, not merely separation of the written prefix.

**Primitive measurement preparation:** actual extraction now retains **476 x86 instructions** (no primitive frontier) and **1,030 ARM words** (only recursive-measure/measure_parts composite frontiers). ARM constructor-error propagation includes its real memcpy call. Classify internal lowering branches by target address, not `.LBB` spelling: lowered BSR/CLZ labels are genuine internal control flow. All 476 x86 AST rows compiled; **1,088 native NOP/INCL/SHRD/SBB register/flag boundary scenarios** passed, and three corrupted NOP encodings were rejected. Exact INCL `%edi` bytes need a direct existing `Operation.inc` AST because Kraken's parser lacks that mnemonic. These are extraction/lowering checks, not measurement execution refinements; two independent ISA proof slices are now in progress. The shared image-generator regression also passed all six Nat-conversion witnesses in **14.90 seconds**.

**Actual private measurement smoke:** each ISA passed **233,376 calls** covering all seven primitive descriptors, matching/wrong primitive value kinds, both retain flags, absent/present progressive limits, empty/padded Nat representations, widths/caps of $2^{64}$, bytes 0–40, and bit counts 0–128. Checks included all 80 result bytes, descriptor/value/backing buffers, every original Nat limb, complete arena header, and scratch. These physically small-count cases are nonallocating; they do not establish measurement's wide-allocation/no-rollback paths. A further **58,344 calls per ISA** passed with arbitrary nonzero upper option-tag padding and inactive None payload bytes. The actual x86 option test consumes bit0 after its unconditional full-word loads, so mapping those words must not become an assumption that padding is zero. ARM execution uses the repository's freestanding Clang/runtime/QEMU pattern, not an unavailable cross-GCC. Temporary binaries were removed; native assembly was unchanged.

**Shared padded-limb measurement arithmetic:** moved the pure size/scan facts into `SszSerializeMeasure`, removing the backend-specific `MeasureUintMath` module and migrating its callers without aliases. Both strict roots now audit the significant-limb bit length, rounded byte size, zero case, physical-length-derived 128-bit size bound, wide-width comparison bound, and BSR stopping certificate. The permanent shared module checked in **768 ms on x86 Lean / 828 ms on ARM Lean**; both strict roots rebuilt successfully. An executable smoke passed **4,680 padded-limb size/minimal-width cases per toolchain**, including zero lists, high-zero padding, both zero/all-one low limbs, and values beyond 128 bits. These are shared arithmetic results, not measurement execution closure. Preserve the distinction between `0#64` and ordinary overloaded zero when using syntactic `simp` matching; normalize deliberately. Reserved `prefix` identifiers and `simpa` rewriting its own hypothesis were additional cross-toolchain proof failures resolved without changing statements or limits.

**Emitter-binding checkpoint boundary:** the joint binding check passed again in **91.44 seconds**, with the same actual caller/helper instruction counts and x86 table bytes. Its dependency closure and structural caller/helper code-ownership lemmas are now imported by the strict roots; the execution-proof modules remain separate and unfinished. Checkpoint this verified image-binding milestone independently rather than including partially compiling emitter bodies.

**Permanent joint primitive-measurement binding:** `scripts/check-measure-binding.py` passed end to end in **85.91 seconds** and is registered in `make binding`. One x86 executable binds **476 caller instructions, 107 NatCompare instructions, 47 constructor instructions, actual intervening bytes, and all 52 read-only dispatch-table bytes**. One ARM program binds **1,030 caller words, 178 NatCompare words, 105 constructor words, and 14 memcpy words**, including the real constructor-error propagation call. Both strict roots audit the structural measurement image interfaces (**927 x86 / 558 ARM jobs**). Six corrupted-image scenarios per ISA were rejected: origin, extent, caller bytes, callee offset, row address, and table. Existing emitter and Nat-conversion binding checks passed again in **92.67 / 15.84 seconds**. This establishes image binding, not measurement execution refinement.

**Measured declaration-boundary effect in the x86 binding witness:** the initial joint witness exceeded a 120-second command deadline, then passed kernel checking with profiling in **266.85 seconds**. Moving the same bounded fetch checks and label checks from local `have` proofs to separate opaque top-level theorems preserved the image, statements, and proof limits; the stricter warnings-as-errors run passed in **80.19 seconds**. These are observed wall times, not a controlled isolated benchmark or a CPU-work reduction claim; cumulative profiler categories overlap parallel declaration work and must not be summed as wall time. ARM's bounded ordered-lookup witness passed in **4.31 seconds** without additional proof options. The only increased limit was the shell command deadline, not Lean's proof limits.

**Primitive wrong-kind ownership boundary:** the shared logical `Serialize.Value` retains Seq/Union payloads and erases them faithfully. The native `Emit.ValueAt`/`ValueBorrowed` predicates reused by primitive measurement observe only the tag for these wrong-kind composite values. Exact WrongType behavior and the byte-exact outside-writes frame do not establish typed composite payload/tree ownership. Full composite/API integration must supply those footprints; do not describe this primitive slice as proving their preservation. Primitive fields, backing bytes, and original Nat limbs have their separate ownership predicates.

**Another shared-Eval hazard:** function-local variables do not isolate Python's `sys.modules`. A cached `decoder_binding` module lacked the newly added memcpy key even though the current file contained it. The x86 extraction had already succeeded; retrying only ARM in a fresh Python subprocess exercised the current source successfully. Run script/generator checks in fresh subprocesses rather than trusting cached imports or reloading modules shared with other agents.

**Pretty-identical states can hide an instance-transparency mismatch:** the x86 emitter's Small UInt pair endpoint printed identical register states and PCs, but `pp.all` exposed a `Decidable` argument still containing the semireducible register getter after the visible guard had simplified to raw register projections. Repeated instance-aware `simp` and explicit guard rewriting did not repair it; rewriting reported that the expression was not type-correct at implicit transparency. Normalizing the visible state/PC and then using `with_unfolding_all exact selected` let definitional equality unfold the hidden getter too. The module checked in **5.2 seconds**, without changing the statement, machine path, or proof limits. Inspect full terms before adding more arithmetic or case splits to an apparently identical endpoint.

**Joint native serialize-wrapper binding:** `scripts/check-serialize-binding.py` passed both toolchains with warnings as errors in **261.61 seconds**. The original x86 wrapper contributes **99 instructions** to one **1,024-instruction** image; ARM contributes **173 words** to one **1,836-word** program. Each closure includes primitive measurement, emission, NatCompare, Nat::from_u128, and shared memcpy at their actual linked offsets. Both x86 read-only tables are checked: 52 measurement bytes and 16 emitter bytes. **Twelve corrupted-image scenarios per ISA** were rejected, including gap bytes, caller/helper bytes, instruction rows, call targets, offsets, entries/frontiers, and tables. The existing joint measurement command passed again in **86.38 seconds** after generator reuse. This establishes structural image ownership, not serializer or measurement execution refinement; the unfinished execution roots remain separate.

**Bounded binding certificates still need bounded composition:** the larger x86 image exceeded the existing simplifier-step limit in a 64-row wrapper fetch certificate. Separate opaque take-32/drop-32 certificates and a Boolean conjunction proof checked without raising limits. ARM's flat 336-row emitter equality exceeded recursion depth inside the new combined image; bounded literal suffix equalities removed that flat reduction. These changes made the larger obligations fit their existing limits, not a measured speedup over the smaller image.

**Keep computed flags opaque during instruction composition:** the ARM measurement BitVector gate's two-instruction proof reached kernel recursion failure after **116 seconds**, despite printing identical endpoint states. A separate stage parameterized by an abstract `PState`, concrete single-instruction effects, and small PC/Z/program/error observations removed the repeated `AddWithCarry` expansion. The stage checked in **712 ms** and the gate in **716 ms**; the similarly decomposed eight-instruction scan load checked in **802 ms**. These are accepted leaf proofs, not acceptance of the complete measurement root.

**A write frame does not preserve readability inside its footprint:** serializer composition needs mapped callee scratch and temporary-result padding even when their values are unspecified. The existing `SszX86.BitVector.Mapping.retains_mapping` theorem strengthens an actual `Eventually` execution with mapped-domain preservation across every interpreted instruction. Reuse that execution theorem rather than adding a future-state mapping assumption or incorrectly extracting inside-frame readability from an outside-writes frame.

**Complete x86 primitive emission:** `SszX86.Emit.program_correct` and `program_refines` now compose all seven primitive kinds from the actual private emitter entry through linked memcpy calls and the original caller RET. The **740-job** execution target passed; the root importing these theorems passed its strict axiom audit in a **1,067-job** build. Premises describe original successful logical inputs and physical ownership, not a readable Plan or future execution. The post includes exact SSZ bytes and success fields, prefix initialization, unchanged capacity tails/result padding, original borrowed inputs, and restored stack/callee-saved/vector state; it does not assert a universal RAX sret value. The joint emitter binding regression passed both ISAs in **94.57 seconds**. A fresh shipped-assembly C/QEMU run passed **571 pinned fixtures plus direct ABI edge checks per ISA** in **8.70 seconds**, across all six fixture formats. ARM emitter execution, complete measurement/serializer wrappers, composites, and whole-library refinement remain unfinished; those runtime checks are not substitutes for their ISA proofs.

**Abstract composition must also hide concrete decoder reduction:** an ARM three-instruction comparison remainder still reached kernel recursion failure after **104 seconds** with abstract flags and opaque intermediate states. Proving its fold/congruence composition once over arbitrary operations and states, then instantiating that theorem, checked the stage in **1.2 seconds**. A concrete `change` followed by a typed congruence chain was not sufficient. The downstream comparison phases then checked in **1.1 seconds**; the complete measurement root remains open.

**Use existing unsigned arithmetic laws before modular certificates:** the x86 wide-count bridge stalled for **120 seconds** in a small modular subtraction lemma. Replacing modular `omega` certificates with `BitVec.add_neg_eq_sub`, `BitVec.toNat_sub_of_le`, and `BitVec.toNat_add_of_lt` made the complete wide arithmetic module check in **841 ms**, without changing its statements or proof limits. The preceding shift/radix bridges were not the bottleneck.

**Make diagnostic progress output bypass Lean's capture:** `#eval IO.println` output, even explicitly flushed, did not expose progress before the nightly checker timed out. Lean captures evaluation streams as diagnostics. Temporary `IO.eprintln` markers with `-DstderrAsMessages=false` localized the stalled declaration; disabling asynchronous elaboration alone did not. Keep these markers and scheduling options out of production proofs and remove the temporary copies after diagnosis.

**Complete ARM primitive emission:** `SszArm.Emit.program_correct` and `program_refines` now cover all seven primitive kinds from original entry through actual linked memcpy and original-LR return. The execution target passed **453 jobs**; the strict root audit importing both theorems passed **643 jobs**. The contract retains original successful-input/physical-ownership premises, exact SSZ output and success fields, output/result padding frames, borrowed inputs, and stack/callee-saved ABI restoration; it adds no readable-Plan or future-execution assumption. Joint emitter binding passed both ISAs in **111.55 seconds**, binding **336 ARM words plus 14 memcpy words**, and the existing x86 image/table closure. Fresh shipped-assembly execution passed **571 pinned fixtures plus direct ABI checks per ISA** in **10.07 seconds**. Primitive measurement and full serializer-wrapper execution are still separate unfinished obligations.

**Adjacent tactic macro terms need bounded precedence:** a two-argument macro declared with `zero:term short:term` parsed `zero short` as an application, producing misleading function-expected errors and consuming following tactic syntax. Using `term:max` for both atomic hypothesis arguments removed the ambiguity. The bounded vector-load proof then checked in **4.2 seconds** after explicitly splitting its remaining arithmetic branch condition; no proof limit or machine premise changed.

**Even register-preservation reflexivity can expand expensive arithmetic:** x86 UInt measurement still hit a **120-second** deadline after introducing an opaque scaled-state definition. Uncaptured markers localized the stall to its small projection-lemma region; asynchronous elaboration did not identify a unique declaration. Proving register/memory/saved-word preservation first over arbitrary replacement low/high words, then instantiating those opaque lemmas, removed the stall. Replacing a remaining recursive `congr 1` with an explicit `congrArg (fun n : Nat => n / 8)` finished `MeasureUintNumber` in **852 ms**. Its enclosing body/root was not yet accepted at this checkpoint. The diagnostic copy was removed; production proof limits were unchanged.

**Tactic grammar can reserve ordinary downstream identifiers:** a publication macro's literal `capacity` token made unrelated serializer binders fail to parse. Declaring the macro separator as the soft keyword `&"capacity"` fixes the grammar rather than escaping every downstream variable. Soft separators also require bounded `term:max` arguments so an argument cannot consume the following identifier. Existing publication callsites remained unchanged, and the complete **846-job** x86 serializer continuation DAG checked afterward; the end-to-end wrapper theorem still depends on measurement execution.

**Unsigned guard proofs should precede broad state simplification:** the ARM list-width proof had only a reversed unsigned comparison left, but default simplification converted its arithmetic facts back to `BitVec` order and left `omega` with no usable constraints. A small `toNat` guard lemma, applied before state simplification, discharged both the effect and instruction-following branches. `MeasureScalarListWidth` checked in **856 ms** without changing the machine contract.

**Do not let reflexivity premises choose the final state:** in x86 UInt wrong-type publication, passing an inferred final state to `noalloc_body_post` together with `rfl` premises caused elaboration to select the original state before matching the actual memory-writing endpoint. Supplying the actual updated flags and result memory explicitly fixed the integration. The complete `MeasureUintBody` target passed **334 jobs**, with the body checking in **733 ms**; the full measurement root remains separate.

**Localize arithmetic inside tactics, not just declarations:** sequential elaboration plus uncaptured, flushed stderr markers inside a temporary proof copy identified the x86 constructor-ownership stall in the header/return-slot separation proof. The modular identity was trivial, but `bv_omega` ran in the full machine/ownership context. Moving that identity to a private lemma over one arbitrary address and one natural displacement reduced the formerly **120-second** target to **1.2 seconds**, including all ownership obligations. The diagnostic copy was removed; production scheduling and proof limits stayed unchanged.

**Use the decoded literal form in memory-rewrite patterns:** x86 spill-store commutation still failed after zeta reduction and `with_unfolding_all rw` because the theorem instantiation used bare `16` while the decoded stores used `16#64`. Instantiating the commutation theorem with the exact bit-vector literals, and converting its disjointness premise separately, checked `MeasureBitsSpills` in **703 ms**. Wider unfolding is not a substitute for a matching rewrite pattern.

**Name the actual intermediate state as well as the final state:** an inferred constructor error-propagation state was selected as the pre-load state from a reflexive memory premise. That made the loaded tag/zero/status obligations false and drove a later memory-unification attempt to the default heartbeat limit. Passing the actual `fromWideLoaded` state explicitly made `MeasureBitsConstructorFinish` check in **811 ms**; the following constructor body checked in **692 ms**, without new execution or initialization premises.

**Distinguish accepted primitive programs from a complete measurement root:** ARM's scalar body target checked in **293 jobs**, and the original-entry-to-return programs for Bool, UInt, byte vectors, byte lists, and bit vectors checked in the **420-job** primitive-program target. Bit-list and progressive-bit-list integration, the complete measurement root, and serializer-wrapper composition remain separate obligations; these intermediate successes do not establish composite-codec or full-library coverage.

**Close spill-memory adapters before composing load equalities:** the x86 bit-list counter's decoded two-store memory and generic spill helper used different closed literal representations. A state-independent equality between the two memory forms resolved the resource handoffs without unfolding stores repeatedly. Saved-load composition additionally needed the original stack-pointer equality before transitivity; asking unification to discover it exhausted the default heartbeat limit. Explicit memory and address normalization checked the counter in **871 ms**, the complete bit body in **819 ms**, and the full measurement proof in **598 ms**.

**Checked x86 primitive serializer milestone:** complete measurement and serializer-wrapper entry-through-RET refinement now pass the **1,325-job** strict root, including root axiom audits of both `program_correct` and `program_refines`. The serializer proof checked in **751 ms**. A fresh native run passed **571 pinned fixtures plus direct ABI edge checks on each ISA**, linking only shipped assembly. This closes the seven primitive x86 serializer kinds, not composite codecs, C/schema wrappers, or Merkle/proof ISA refinement; SHA trust is unchanged.

The serializer image certificate independently rechecked both shipped closures: **99 wrapper / 1,024 total selected x86 instructions** and **173 wrapper / 1,836 total selected ARM instructions**. The combined check took **267.51 seconds** after a 120-second process deadline interrupted the first attempt; Lean proof limits were unchanged. Image binding alone is not execution refinement; the new x86 root supplies the latter.

**Localize context search before adding proof abstractions:** an ARM returned-error proof repeatedly exhausted 200,000 heartbeats even after its run/post composition was split. Sequential, flushed tactic markers located the actual stall after finite payload-index normalization: `all_goals assumption` searched a large concrete-state context. Selecting the six already-named payload witnesses explicitly checked the module in **959 ms**. The temporary diagnostic module was removed; no proof limits changed.

**Checked prerequisites for recursive codecs:** `SszCodecTypes` retains native NatOperand representations throughout all thirteen descriptor kinds and six recursive value kinds, with total raw-schema erasure and exact primitive adapters. `SszLimbMul`/`SszNatMul` model the real row-major multiply/add/carry loops, significant-word dispatch, normalized borrowing, checked reservations and complete scratch writes. Both toolchains accepted these modules; strict roots passed **1,333 x86 jobs / 647 ARM jobs**. These are mathematical representation/algorithm proofs, not multiplication or composite-codec ISA refinement.

Model runtime smokes on both toolchains exercised nested fixed/variable container serialization, union selection, >64-bit recursive metadata, multiply carries, redundant limbs, borrowing, alignment and capacity boundaries. Separate freestanding probes exercised the shipped private multiplication helpers on both ISAs, including scratch/tail frames and failure preservation. The first ARM probe incorrectly used C's hidden X8 structure-return convention and faulted; inspecting the shipped entry showed the Rust internal result pointer in **X0**. An explicit first output-pointer argument passed. Only temporary ELF symbol visibility was changed to call the private helpers; assembly instructions and native sources were unchanged, and temporary binaries were removed.

**Checked ARM primitive serializer milestone:** complete measurement checked in **652 jobs** and serializer-wrapper composition in **769 jobs**; their public program modules checked in **946 ms / 899 ms**. The strict ARM root now imports and audits both original-entry-through-return refinements and passed **936 jobs**. A fresh shipped-assembly smoke again passed **571 pinned fixtures plus direct ABI checks on each ISA**. Both ISAs now cover complete private primitive measurement and serialization; recursive composite codec execution, external C/schema wrappers and hashing/Merkle/proof ISA refinement remain open. No SHA trust or proof limits changed.

## 2. What has helped

### Opaque block summaries instead of repeated symbolic execution

A basic-block contract should expose only what its callers need:

- Entry PC and permitted exit PCs.
- The logical state change.
- Relevant output registers and flags.
- Modified memory regions and register clobbers.
- Preservation of borrowed views, alignment, and error state.

Conceptually, the interface is:

```text
code at the expected addresses + entry invariant
    implies
some finite execution reaches an exit invariant,
with the advertised result and frame/resource effects
```

The contract must be proved from the real instruction semantics. Once checked, higher-level proofs should apply the theorem without reopening the nested machine-state updates used to establish it.

A concrete result: the earlier monolithic ARM ordering proof failed after about 112 seconds with kernel deep recursion. Splitting it into result-byte, frame, return-PC, and path contracts produced a checked module in about 4.5 seconds. These are individual observed builds, not a controlled whole-project benchmark. See [NatCompareOrder.lean](backends/arm/SszArm/NatCompareOrder.lean).

### Separate execution, arithmetic, and frame arguments

These obligations benefit from different representations and automation:

| Obligation | Useful boundary |
| --- | --- |
| Instruction execution | A small state transition for a specific block or instruction family |
| Arithmetic correctness | Mathematical values, explicit bounds, and narrowly normalized bit-vector expressions |
| Preservation | A frame describing unchanged registers and memory outside written regions |
| Control flow | Entry/exit PC facts and branch conditions expressed mathematically |
| Resource behavior | Exact reservation and cursor transitions, including failure paths |

Arithmetic proofs should not inspect long memory-store expressions. Frame proofs should not recompute the algorithm's arithmetic. Final block theorems combine the separate certificates.

Another useful application was ARM stack preservation: expose a block's stack delta and prove its SP projection, then derive alignment from that fact. This replaced brittle alignment backtracking through the large opcode effect definition. The resulting `DelimitedOps` module checked, but that alone does not establish the full decoder refinement.

Further checked examples:

- **ARM delimited instruction semantics:** the monolithic instruction proof exceeded a 300-second check deadline. Separating branch, integer, load, store, and SIMD contracts localized the remaining problems. Small pure lemmas for masks and sign extension reduced the repaired integer module to a 1.2-second successful check; the final instruction dispatcher then checked in about 11 seconds. This establishes the instruction/block interface, not the decoder's complete loop, resource, and return theorem.
- **x86 call composition:** applying the comparison contract originally exhausted one million heartbeats while reducing the return-address store. An opaque `stored_return_load` lemma let the repaired call-composition module check in 713 milliseconds. The instruction semantics and callee specification were not weakened.
- **ARM error-tail observations:** proving an unnecessary whole-memory image equality timed out after 592 seconds at 16 million heartbeats. Keeping the same public error-result theorem and separate full frame/execution contracts, but proving the required output fields with existing read-after-write and SIMD-zero-store facts, produced a **38-second passing module**. Choose a sufficient auxiliary claim; do not weaken the public contract or repeatedly unfold unrelated register state.
- **ARM arithmetic indexed loads:** reducing enumeration from 1,792 cases to 56 still left the load block failing after 722 seconds. A generic opaque theorem for indexed read, temporary-register save/restore, and stack restoration checked in **1.2 seconds**. Composing the actual seven load kinds with it then checked in **95 seconds**, without increasing limits or changing instructions. This closes that load interface, not the whole addition theorem. The separate return-value module still took **469 seconds** to pass; expensive state normalization remains elsewhere.
- **ARM one-word addition:** the combined block failed after **744 seconds**. Separating carry/control/frame observations from execution and instruction-image hypotheses produced an opaque state module that passed in **298 seconds**, followed by a **659 ms** passing execution composition. The state proof is still expensive; the complete addition refinement remains pending. Avoid unfolding execution/image hypotheses while simplifying state observations.
- **x86 paired carry execution:** guarding a repeated instruction dispatcher by PC still left a **694-second timeout**. Replacing it with checked load, arithmetic, store, and state-equality contracts let the paired-path composition pass in **1.1 seconds**; its new helper modules checked separately in roughly **0.7–3.8 seconds each**. The 1.1-second figure is incremental composition time, not total development or clean-build time. The whole addition helper is still incomplete.

These results support reducing repeated unfolding, not a claim that every proof will have the same speedup.

### Reuse existing facts before inventing tactics

Existing unsigned comparison/flag lemmas from the division proofs also apply to `Nat.compare`. Existing byte-view lemmas handle comparisons against zero. Shared packing and bit-count facts avoid proving the same mathematics separately for x86 and ARM.

Useful shared modules include [SszNatABI.lean](proofs/SszNatABI.lean), [SszBitView.lean](proofs/SszBitView.lean), and [SszArena.lean](proofs/SszArena.lean).

Prefer a small explicit simplification set at a boundary over a broad `simp_all` that unfolds implementation details opportunistically. Normalize hypotheses and goals consistently. Do not unfold a definition before applying the theorem that summarizes it.

### Check the smallest useful dependency frontier

A productive loop is:

1. Write one meaningful contract and its implementation proof.
2. Check that module and its necessary dependencies.
3. Fix the first substantive failure.
4. Treat the checked interface as stable.
5. Build the next composition layer against it.

Splitting files only helps if it also isolates proof obligations and dependencies. Moving the same enormous reduction into another file does not make it cheaper.

Parallel work is useful across independent routines, architectures, or pure arithmetic/memory contracts. It is less useful when every branch waits on the same unproved callee interface. Keep one integration owner, explicit file ownership, and short compiler-diagnostic relays. Prefer reproducible files and artifacts over assumptions about shared interactive process state.

Measure progress by closed, checked interfaces and the remaining dependency frontier—not generated proof lines or the number of workers.

### Distinguish necessary adapters from duplicated reasoning

The two ISAs need different flag, load/store, instruction-step, stack, and register-preservation proofs. Those are necessary adapters to different semantics. The same logical count calculation, allocation order, optional-Nat layout, retained-byte rule, or two-limb value equation should not be maintained independently in both adapters.

The pilot now shares these algorithm/representation facts, including `PreparedAt.pair` for the comparison call and `result_refines` for the final SSZ memory observation. It does not make repeated literal-cast or large-state normalization failures disappear. Reuse a checked normalizer at a stable word/ABI boundary rather than copying local simplifier recipes; keep the instruction-specific transport on the ISA side.

## 3. How machine code could make future verification easier

Here, “bytecode” means the emitted native instruction stream. The project currently targets x86-64 and AArch64, not a portable bytecode VM. None of the following requires changing the SSZ wire format.

These are recommendations, not changes already proved beneficial end-to-end. Each has a native performance or engineering tradeoff.

| Prefer | Why it helps proofs | Tradeoff or qualification |
| --- | --- | --- |
| Direct calls and explicit branch targets | Makes the call graph and reachable instruction closure explicit | Indirect dispatch can be faster or smaller in some cases; eliminating it is not automatically a runtime win |
| Small, reusable helper routines with stable contracts | Allows comparison, loads, division, and reservation behavior to be proved once and reused | Excessive outlining adds calls, spills, and ABI obligations |
| Predictable stack frames and explicit scratch regions | Simplifies ownership, write footprints, alignment, and restoration proofs | Must not introduce unnecessary stack traffic merely for proof convenience |
| Regular load/store forms and a small set of arithmetic idioms | Supports reusable instruction-family lemmas | A restricted instruction vocabulary can lose performance |
| Local, explicit flag dependencies | Keeps a branch's meaning close to the comparison that establishes it | Aggressive scheduling or flag reuse may be profitable on hardware |
| SIMD operations actually supported by the ISA model | Avoids having to extend semantics in the middle of an SSZ proof | Do not disable all SIMD unnecessarily; supported vector memory operations are already useful |
| Stable block identities, namespaced labels, and reproducible artifacts | Reduces accidental proof churn and label collisions | Byte offsets may still change; binding must detect that rather than reuse stale certificates |

The existing ARM build already disables jump tables and automatic loop/SLP vectorization while retaining supported SIMD operations. This reflects gaps in the current ISA model, not a claim that scalar code is inherently easier or better in every case. See [native_build.py](scripts/native_build.py).

When lowering an unsupported instruction, prove the lowering sequence's real semantics and side effects. A replacement that computes the right register value but corrupts live flags, stack bytes, or ABI state is not sufficient. Common lowering sequences are good candidates for reusable checked contracts rather than repeated expansion in every caller.

### Use an algorithm-level intermediate specification

The delimited-bit pilot now has a shared executable native-algorithm specification between the machine code and the original SSZ specification: [SszDelimited.lean](proofs/SszDelimited.lean), with its correspondence proofs in [SszDelimitedProofs.lean](proofs/SszDelimitedProofs.lean). Both complete private callees refine this model through their actual returns, and the model refines pinned SSZ semantics. These proofs are checked on both toolchains and root-audited. Public dispatch wrappers remain open.

```text
x86 instruction/block proofs ─┐
                             ├─> native-algorithm specification ─> pinned SSZ specification
ARM instruction/block proofs ─┘
```

The intermediate layer should follow the implementation's loops, branch order, word arithmetic, and resource effects. It should not duplicate every instruction, architectural register, or flag update. Otherwise it inherits most of the brittleness we are trying to remove.

The delimited-bit model explicitly:

1. Rejects empty input and distinguishes all-zero input from a trailing-zero encoding.
2. Finds the last byte's highest set bit and constructs the count using two 64-bit words, with a proof that their value equals the logical bit count.
3. Represents that count as Small or two-limb Large, with the exact arena reservation and failure behavior.
4. Performs the optional bound check **after** that reservation.
5. Returns the original borrowed byte prefix and logical length, or the exact error and committed resource state.

Keep machine-word wraparound and overflow checks where the implementation relies on them; do not replace them with unrestricted natural-number arithmetic without a proof. Keep arbitrary logical capacities, noncanonical limb forms, read-only aliases, and zero-length ranges in scope.

This yields two distinct obligations:

- **Assembly to intermediate model:** a simulation relation connects registers/memory to logical variables and views. Actual blocks implement model transitions, preserve the required frame, and terminate through the real return path.
- **Intermediate model to SSZ:** prove algorithmic equivalence once for both ISAs. Resource failure is not an SSZ semantic error: specify its exact conditions/effects, and prove that sufficient resources lead to the specified semantic result. A theorem saying only “if native execution happens to succeed, its value agrees” would be too weak.

Parts of this layer already exist in the shared outcome, packing, limb, representation, and arena modules. What is not yet complete is a uniform algorithm-oriented transition model for every codec and Merkle routine.

Expected end-to-end benefit remains an engineering hypothesis. The shared model removes a place for duplicated semantic/resource reasoning, but does not eliminate instruction-model normalization or memory/ABI proofs. Reuse the checked blocks and compare actual proof/checking behavior before generalizing. Do not rewrite closed proofs or build a general-purpose verifier merely to introduce another abstraction.

If a lifter or generator constructs the intermediate model, its connection to the actual instructions must still be checked. Generated models and successful tests are not a substitute for that bridge.

### Completed callee pilot: reuse demonstrated, end-to-end speedup unmeasured

- The shared refinement establishes both bit-list variants, exact scratch-failure conditions, and the committed allocation/cursor state independently of the optional limit. A large count is reserved before checking that limit; rejection does not roll it back. The resource/geometry proof module checked in **657 ms on x86's Lean version and 783 ms on ARM's**. With the shared memory-observation and comparison-ABI bridges added, it checked in **839 ms and 892 ms**, respectively; both root audits passed.
- Both local optional-Nat layout definitions have been removed in favor of the checked shared `NatMemory.OptionAt`; `None` still imposes no payload read. Both ISAs reuse the shared retained length, count words, reservation geometry, prepared-count representation, resource effects, and memory-result-to-SSZ bridge. Register/stack/call state stays ISA-specific.
- There is **no successful pre-pilot end-to-end decoder proof timing** to compare against. Both complete private callee theorems are now closed, but this establishes completion—not that the model caused a numerical end-to-end speedup.
- Low-level composition still dominates the unresolved frontier. An ARM arena-store proof timed out at **295 seconds** after an initial factoring attempt. Instruction-sized opaque contracts reduced the next failed check to **8.4 seconds**, exposing smaller register-preservation goals; after those repairs, the module **passed in 8.6 seconds**. This is a measured local factoring win, not a gain attributable to the intermediate semantic model.
- The x86 bit-save block changed from a **112-second kernel recursion failure to a 1.0-second passing check** after splitting its store and register/test transitions into opaque contracts. Its arena-commit proof changed from a **40-second timeout to a 1.0-second pass** after address and mapped-load normalization. These are further local proof-engineering gains, not evidence of an intermediate-model speedup.
- ARM's checked count phase now derives the Small/Large branch from the shared `CountWords.high_zero_iff`, `countWords_data_value`, and existing SSZ bit-count threshold theorem instead of rebuilding the division argument locally. That module checked in **6.0 seconds**; the malformed-input phase, which connects actual scan/error-return execution to the shared `run` postcondition, checked in **6.6 seconds**. This demonstrates model reuse in machine composition, but neither phase alone closes the whole decoder.
- ARM's `Delimited.decode_correct` composes every validation, count, allocation, optional native comparison, success/error, and real-return path into the shared `Post`. Its final composition module checked in **637 ms with dependencies already built**; this is not a clean-build or total-development measurement. Adding `Post.refines` connects the observed memory to pinned SSZ deserialization while explicitly retaining scratch failure. The integrated module and root axiom audit passed in **634 ms and 959 ms**, respectively. No execution or Nat-ordering hypothesis was added.
- x86's complete `Delimited.decode_correct`, `Post.outcome`, `Post.refines`, and `Post.bitList` module checked in **640 ms with dependencies already built**; its root audit checked in **846 ms**. ARM's final module, including both bit-list corollaries, and root audit checked in **1.5 seconds and 1.6 seconds**. These are incremental final-module checks, not comparable clean-build or development-time benchmarks.
- x86's large-reservation composition initially failed after **133 seconds**, including a four-million-heartbeat memory-expression timeout. Explicit observation equalities replaced simplifier traversal through committed memory; after syntax and normalization repairs the same phase passed in **945 ms**. The shared model supplied the target count/allocation facts, but the measured timeout fix was local memory-proof factoring.
- Adding a theorem to the existing shared Nat ABI module invalidated old comparison dependencies. The subsequent root builds took **7.88 seconds on x86 and 162.27 seconds on ARM**; most ARM time was in those existing machine proofs. Keep stable representation interfaces separate from frequently edited implementation proofs. A small new semantic proof does not imply a cheap dependency rebuild.
- After ARM integration, joint linked-image binding passed for **184 x86 decoder instructions plus 107 comparison instructions**, and **253 ARM decoder instructions plus 178 comparison instructions**. **571 pinned fixtures plus direct ABI edge checks passed on each ISA**, including ARM/QEMU. The combined binding/runtime command took **128.76 seconds**. These checks corroborate the artifacts and exercised behavior; they do not replace either ISA theorem.
- Executing the shared model on both Lean toolchains passed **55,296 semantic cases and 9,024 count/resource-stage cases**. The latter cover the Small/Large boundary, word wrap boundaries, alignment, exact-fit/exhausted arenas, capacities above `2^63`, and reservation retention on rejection. Huge lengths were exercised only through count/prepare/finish—not by allocating exabyte inputs or claiming native execution of them.
- After both callee proofs and root audits were integrated, **`make check` passed in 349.66 seconds**. It covered the pinned reference, both proof builds, artifact binding, native conformance and ABI checks, 960 generated differential values plus 480 compatibility pairs, and both lowering-validation suites. This is the integrated verification pipeline time, not a clean proof-build benchmark or a before/after speedup measurement.

**Assessment:** retain the shared model. It demonstrably removed duplicated semantic/resource definitions and let both native proofs target one checked algorithm contract; both final SSZ bridges now reuse the same refinement theorem. **Did it make the work faster? That is not established by the available timing evidence.** The observed large checking-time improvements came from opaque instruction contracts, explicit observations, and word/address normalization, not an isolated intermediate-model experiment. The model also added proof modules and dependency rebuild costs. For subsequent work, reuse this separation when there is a genuinely shared algorithm; keep stable interfaces small, measure fresh and incremental checks separately, and do not rewrite closed proofs or introduce a general IR framework merely for uniformity.

## 4. General strategy for this FV effort

### A. Pin the specification, semantics, and artifacts

Keep the SSZ specification revision, ISA-model revisions, compiler/toolchain versions, and assembly-lowering pipeline reproducible. [sources.lock.json](sources.lock.json) records the source pins.

The target is the actual shipped assembly. Rust is the implementation source used to generate it; source-level intuition or a successful Rust test is not a proof that the emitted instructions implement SSZ. The machine proof and artifact binding must connect to the same code.

### B. Establish an architecture-independent semantic layer

Define the operation's mathematical result and prove its relationship to the pinned SSZ model. Keep packing, bit counts, natural-number representations, capacity arithmetic, and tree properties shared where possible.

Keep logical size separate from physical storage:

- Capacities and generalized indices are mathematical naturals, not silently truncated machine integers.
- Addressable memory spans have explicit finite bounds and alignment requirements.
- Any narrower arithmetic bound used by an implementation must be derived from those premises, not imposed to discard difficult valid cases.

The resource-aware native model must also specify host failures and committed scratch effects. Those are distinct from the specification's semantic rejection reasons.

### C. Connect memory representations to mathematical values

Use explicit predicates for descriptors, borrowed byte/limb slices, output layouts, and arena state. State the precise separation and preservation requirements.

Do not require canonical limb encodings unless the API actually requires them. Do not forbid harmless read-only aliases just to simplify a proof. Treat empty ranges as empty, even when their pointer values coincide with other regions.

### D. Prove actual blocks, then loops and calls

Prove instruction/block transitions with compact contracts. Use loop invariants expressed in terms of logical progress—remaining limbs, processed bytes, accumulated roots—and memory views, not growing symbolic execution histories.

At a call site, establish the callee's real code location, argument representation, stack/return conditions, and memory preconditions. Apply its checked contract and account for all allowed clobbers and resource effects. Caller and callee code assumptions must be jointly realizable in the linked image.

An eventual-execution theorem with an existential finite step count is often enough; it need not expose an enormous expanded trace to callers. The theorem must still cover termination and the actual return path.

### E. Close the complete operation boundary

A helper theorem is a milestone, not a public API proof. Compose dispatch, validation, helper calls, all success/error branches, and return behavior.

Check for hidden scope reductions:

- Are all promised types and descriptor forms covered?
- Are large capacities, malformed inputs, and resource failures represented?
- Are terminal frontiers proved unreachable, rather than simply excluded?
- Are scratch effects on errors correct?
- Are the original borrowed inputs and required ABI state preserved?

### F. Keep four kinds of evidence separate

1. **Semantic correspondence:** the mathematical operation matches the pinned SSZ model.
2. **ISA refinement:** the modeled machine executes to the specified result with the required frame and resource effects.
3. **Artifact binding:** the modeled instructions and call geometry match the actual linked bytes. A `CodeAt` witness is not, by itself, a refinement theorem.
4. **Executable validation:** native x86 and ARM/QEMU runs exercise real paths against independent or pinned expected results. Tests are useful evidence, not universal proofs.

Completed proof components should be imported into their architecture roots and included in the axiom audit. Whole-project checks belong after integration as well as targeted checks during development. Keep incomplete components explicitly incomplete.

Recent executable evidence: 491,648 direct calls to the actual delimited decoder passed on each of native x86 and ARM/QEMU. The smoke checked success and malformed/limit errors, exact observed result fields, output guards, noncanonical and greater-than-64-bit capacities, read-only aliases, and already-used or zero-free scratch. These runs exercised small logical counts; they did **not** exercise the enormous physical inputs needed to trigger the decoder's large-count allocation path. Both complete callee theorems now cover that resource branch formally. Temporary harnesses were removed automatically.

## 5. Hashing and the trusted boundary

SHA-256 correctness is currently permitted as an explicit hypothesis. It is not an excuse to assume that SSZ hashing or Merkleization is correct.

For a native call, the trusted contract must cover both the digest and the necessary execution/ABI/memory behavior. Assuming only a pure function equation does not justify a call to arbitrary machine code. The contract must cover the input forms actually used, including full concatenations and non-32-byte proof-node inputs; it must not silently be restricted to pairs of 32-byte nodes.

No collision-freedom or injectivity assumption is needed merely to prove that this implementation computes the specified SSZ result. Such assumptions must not be smuggled into the tree proof.

The remaining hashing decomposition is:

1. Prove bounded and progressive Merkle engines against the hash contract: accumulator invariants, subtree ordering, padding, capacities, and empty-tree behavior.
2. Prove type-specific layout and root construction: basic-value packing versus recursive composite roots, field ordering, and length/selector/active-field mix-ins.
3. Prove generalized-index and proof-construction/verification operations separately where they are part of the API.
4. Compose the native implementations with their ISA-level memory and call contracts.

Merkleization concentrates difficult reusable invariants. Type-specific hashing has broader case coverage and recursive integration obligations. They are layers of the same operation, not alternatives.

All hash-dependent results must remain visibly conditional on the stated hash contract. Do not add a global correctness axiom. The rest of the development still requires ordinary kernel-checked proofs: no `sorry`, `admit`, unsafe proof shortcuts, `native_decide`, `bv_decide`, or external oracle substitution. The axiom audit also distinguishes ordinary Lean foundations from accidental or newly introduced assumptions.

## 6. Practical next priorities

- Consider a parser-only pre-check for syntax and reserved-token errors before expensive builds; that tool remains unimplemented and its speed unmeasured. Unknown names and missing tactics require elaboration, preferably in a small import probe. The measured failure mode was first error output after 128–134 seconds of module elaboration, not slow import loading.
- Route state-projection goals through the existing fold/projection lemmas (`block_error`, `block_program`, `mem_w_of_mem_eq`, `read_mem_bytes_of_w`) instead of broad `simp`; measured 0.56 s vs 19.6 s for the identical ARM goal (2026-09-27 section in "Where the bottleneck is").
- Reuse the now-closed comparison contracts to finish the decoder dependency frontiers before expanding more unchecked descendants.
- Reuse the successful opaque-summary pattern for repeated load/store, stack, flag, call, and return shapes.
- Keep arithmetic facts shared between ISAs and representation conversion explicit at boundaries.
- Diagnose elaboration/kernel expansion before increasing limits; collect whole-project measurements before claiming an overall speedup.
- Consider proof-friendly emission changes only where they preserve the API and have an acceptable measured native performance tradeoff.
- Keep coverage, assumptions, binding evidence, and executable evidence distinct throughout the final integration.
