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

The corrected arithmetic harness then passed 1,536 direct private-helper calls per ISA, checking values, borrowed/allocated representations, full error payloads, alignment, exact cursor changes and written limbs, unchanged inputs, and output/arena guards. The shared addition/division models passed the same 1,536 resource cases plus 3,072 source-only zero/one-divisor cases on each Lean toolchain. Their general arithmetic/resource theorems now pass both root axiom audits. Addition's complete linked images also have checked CodeAt witnesses (383 x86 instructions; 603 ARM instructions). These are checked dependencies for the pending BitVector proof, not completed Nat.add/Nat-division assembly refinements; those require the remaining execution and memory proofs.

ARM disassembly encodings and raw section bytes have different representations: a row's eight hex digits already denote the instruction word, whereas raw section bytes require little-endian decoding. A reversed-word generation error was caught and corrected before use; the corrected 282-word division image and the actual 65-word runtime callee now have checked CodeAt witnesses in the same ARM Program. Reuse the binding generator's existing encoding conversion rather than independently guessing byte order.

Both complete division images now have checked joint caller/runtime witnesses: 221 caller instructions plus 66 runtime instructions on x86, and 282 plus 65 on ARM. The binding command passed in 168.79 seconds. For x86, reducing the standalone runtime layout required `instances := true` during simplification, not just an initial `dsimp`: otherwise later layout projections remained opaque and expanded the finite witness until its step limit. The fix exposed the existing instance; it did not raise limits or change code. Whole Nat-division execution refinements remain pending.

### ISA model corrections change the recorded trust baseline

The pinned LNSym logical-immediate interpreter incorrectly read SP for some Rn31 sources, including the actual SSZ instruction `0xb27fefe9`. Architectural Rn31 is XZR/WZR for these source operands; destination handling is different and must remain unchanged: non-flag-setting logical operations may write SP, while ANDS with Rd31 discards the result and updates NZCV. See the [ARM ORR-immediate reference](https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/ORR--immediate---Bitwise-OR--immediate--?lang=en).

The user explicitly approved a tracked model correction rather than changing shipped assembly or imposing an artificial SP precondition. The ARM baseline is now commit `df80e2f600dc7f2976809829198a1d9fd07cb379` **plus** [the recorded patch](patches/lnsym-logical-immediate-rn31.patch), SHA256 `0586e9185877634896931dcbed0d55f03ccc5c8c22f33da77a7b9b10f885ab3c`. [sources.lock.json](sources.lock.json) records the patch and pristine/corrected source hashes; `make models` verifies the base revision and hashes, rejects unrecorded tracked changes, and applies the correction reproducibly.

The behavioral regression executes 32 real instruction words across 2,048 cases, covering all four logical-immediate operations, both widths, source Rn31 and ordinary-register controls, destination SP/ZR distinctions, and every incoming NZCV value. Before correction, native A64/QEMU passed but LNSym disagreed in 960 cases. After correction, native, model, and independent bitwise expectations agreed in all 2,048 cases. `make model-check` also passed three kernel-checked whole-state regression theorems: the actual MOV for arbitrary state/SP, ORR's SP destination, and ANDS's discarded destination plus replacement flags. The shipped assembly is unchanged. The corrected-model ARM root and strict axiom audit subsequently passed all 242 dependency jobs, including the previously completed runtime, scalar/byte-view, comparison, and delimited proofs.

Patch preparation was also exercised on an isolated pristine pinned checkout: first application and idempotent reuse passed; modified target contents, unrelated tracked source changes, and patch tampering were rejected without overwriting them. The missing-checkout network-fetch branch was not exercised.

Changing the model invalidates substantial proof dependencies. The first corrected-model arithmetic closure check took 957.31 seconds and failed in unfinished composition modules, although the actual MOV and flag instruction families passed in 1.7 and 1.6 seconds. Rechecked older comparison modules still took 126–143 seconds each; a new allocation-check module took 181 seconds. The subsequent successful completed-proof root check took 377.30 seconds, dominated by the existing byte-view control-flow module at 369 seconds. These costs are not a measured shared-model speedup. A separate invocation lesson: `lake -d backends/arm` from the repository root does not select that directory's Elan toolchain. One attempted audit therefore used Lean 4.34.1 and failed in the pinned 4.31 model; launching from `backends/arm` selected the correct toolchain and passed.

The shared addition and division ownership bridges now also pass both kernel/root audits: original operand observations plus observations of every allocated written limb imply ownership of the exact returned operand. They reuse normalization and do not discard redundant high-zero scratch writes. The x86 addition return proof consumes its bridge; this is actual reuse of a checked memory-representation fact, not a whole arithmetic execution theorem.

A separate native smoke exercised the division theorem's wider divisor domain, rather than only production divisors 8, 32, and 256: **704 calls passed on each of x86 and ARM/QEMU**, using 32 divisors from 2 through `2^64-1` and 22 physical operand representations, including empty/padded Large values and five-limb inputs. Independent Python integers supplied exact quotient/remainder and allocation expectations. The harness checked normalized output metadata, all allocated quotient limbs, cursor, unchanged arena base/capacity and input words, and output/scratch guards. This is finite evidence for the proposed divisor-at-least-two contract, not acceptance of the pending whole-helper theorems. Temporary harnesses and executables were removed.

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

- Reuse the now-closed comparison contracts to finish the decoder dependency frontiers before expanding more unchecked descendants.
- Reuse the successful opaque-summary pattern for repeated load/store, stack, flag, call, and return shapes.
- Keep arithmetic facts shared between ISAs and representation conversion explicit at boundaries.
- Diagnose elaboration/kernel expansion before increasing limits; collect whole-project measurements before claiming an overall speedup.
- Consider proof-friendly emission changes only where they preserve the API and have an acceptable measured native performance tradeoff.
- Keep coverage, assumptions, binding evidence, and executable evidence distinct throughout the final integration.
