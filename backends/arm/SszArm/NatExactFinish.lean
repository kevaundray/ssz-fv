import SszArm.NatExactEntry
import SszArm.UintResultMemory
import SszArm.NatExactState

namespace SszArm.NatExact

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)
open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

structure ReturnSpace (s : ArmState) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  output : (r (.GPR 0#5) s).toNat + 68 ≤ 2^64
  separate : (r (.GPR 0#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat
  pair : (r (.GPR 1#5) s).toNat + 16 ≤ 2^64
  pairOutput : (r (.GPR 1#5) s).toNat + 16 ≤ (r (.GPR 0#5) s).toNat ∨
    (r (.GPR 0#5) s).toNat + 68 ≤ (r (.GPR 1#5) s).toNat
  pairStack : (r (.GPR 1#5) s).toNat + 16 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 1#5) s).toNat

theorem Owned.returnSpace {s : ArmState} {expected : SszNative.NatOperand}
    (owned : Owned s expected) : ReturnSpace s := by
  have stack := owned.stackBound
  refine ⟨stack, owned.outputBound, ?_, owned.expectedBound, ?_, ?_⟩
  · rcases owned.outputStack with empty | separate
    · omega
    · have h := separate ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
      simp only [Prod.fst, Prod.snd] at h
      omega
  · rcases owned.expectedOwned with empty | separate
    · omega
    · exact separate ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
  · rcases owned.expectedOwned with empty | separate
    · omega
    · have h := separate ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [localWrites])
      simp only [Prod.fst, Prod.snd] at h
      omega

/-- Each cut contains at most thirteen instructions. Restoring SP does not erase
its spill words; the explicit memory below retains both persistent stores. -/
inductive Cut where | actual | text | zeros | result
  deriving DecidableEq

def Cut.ops : Cut → List Op
  | .actual => [.p124, .p128, .p132, .p136, .p140, .p144, .p148, .p152, .p156, .p160, .p164, .p168]
  | .text => [.p172, .p176, .p180, .p184, .p188, .p192, .p196, .p200, .p204, .p208]
  | .zeros => [.p212, .p216, .p220, .p224, .p228, .p232, .p236, .p240, .p244, .p248, .p252, .p256, .p260]
  | .result => [.p264, .p268, .p272, .p276]

def spillTwo (s : ArmState) (first second : BitVec 64) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) second
    (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) first s)

def actualImage (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 0#5) s + 40#64) (r (.GPR 2#5) s)
    (write_mem_bytes 8 (r (.GPR 0#5) s + 32#64) 0#64
      (spillTwo s (r (.GPR 9#5) s) (r (.GPR 10#5) s)))

def textImage (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 0#5) s + 8#64) 0#64
    (write_mem_bytes 8 (r (.GPR 0#5) s) (r (.GPR 8#5) s)
      (spillTwo s (r (.GPR 9#5) s) (r (.GPR 10#5) s)))

def zerosImage (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 0#5) s + 56#64) 0#64
    (write_mem_bytes 8 (r (.GPR 0#5) s + 48#64) 0#64
      (spillTwo s (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s) (r (.GPR 10#5) s)))

def resultImage (s : ArmState) : ArmState :=
  write_mem_bytes 4 (r (.GPR 0#5) s + 64#64) 3#32
    (write_mem_bytes 8 (r (.GPR 0#5) s + 24#64) (r (.GPR 9#5) s)
      (write_mem_bytes 8 (r (.GPR 0#5) s + 16#64) (r (.GPR 8#5) s) s))

def Cut.image (base : BitVec 64) : Cut → ArmState → ArmState
  | .actual, s => w .PC (base + 172#64) (w (.GPR 8#5) 1#64 (actualImage s))
  | .text, s => w .PC (base + 212#64) (textImage s)
  | .zeros, s => w .PC (base + 264#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s)
        (w (.GPR 8#5) (read_mem_bytes 8 (r (.GPR 1#5) s) s) (zerosImage s)))
  | .result, s => w .PC (r (.GPR 30#5) s) (w (.GPR 8#5) 3#64 (resultImage s))

def Cut.start : Cut → Nat
  | .actual => 124 | .text => 172 | .zeros => 212 | .result => 264

macro "exact_side" : tactic => `(tactic| first | assumption | omega | bv_omega)

macro "exact_reads" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) (disch := exact_side) only
    [state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.setWidth_ofNat_of_le,
     BitVec.sub_add_cancel, BitVec.add_sub_cancel, UintCodec.Tail.write_pair_words,
     read_mem_bytes_write_mem_bytes_same, read_mem_bytes_write_mem_bytes_disjoint])

theorem restored_w (s : ArmState) (field : StateField) (value : state_value field)
    (same : r field s = value) : w field value s = s := by
  rw [← same, w_irrelevant]

/-- The lowering's restore order differs from its save order. Commute just the
three fixed registers once, independently of instructions and memory. -/
theorem restore_spill_registers (s : ArmState) (sp saved9 saved10 temporary9 temporarySP : BitVec 64)
    (hsp : r (.GPR 31#5) s = sp) (h9 : r (.GPR 9#5) s = saved9)
    (h10 : r (.GPR 10#5) s = saved10) :
    w (.GPR 31#5) sp
      (w (.GPR 9#5) saved9
        (w (.GPR 10#5) saved10
          (w (.GPR 9#5) temporary9 (w (.GPR 31#5) temporarySP s)))) = s := by
  rw [w_of_w_commute (fld1 := .GPR 9#5) (fld2 := .GPR 10#5) (by decide)]
  rw [w_of_w_shadow]
  rw [w_of_w_commute (fld1 := .GPR 9#5) (fld2 := .GPR 31#5) (by decide)]
  rw [w_of_w_commute (fld1 := .GPR 10#5) (fld2 := .GPR 31#5) (by decide)]
  rw [w_of_w_shadow, restored_w s (.GPR 9#5) saved9 h9,
    restored_w s (.GPR 10#5) saved10 h10, restored_w s (.GPR 31#5) sp hsp]

theorem actual_spills (s : ArmState) (space : ReturnSpace s) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (actualImage s) = r (.GPR 9#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (actualImage s) = r (.GPR 10#5) s := by
  obtain ⟨stack, output, separate, pair, pairOutput, pairStack⟩ := space
  constructor <;> simp only [actualImage, spillTwo] <;> exact_reads

theorem text_spills (s : ArmState) (space : ReturnSpace s) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (textImage s) = r (.GPR 9#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (textImage s) = r (.GPR 10#5) s := by
  obtain ⟨stack, output, separate, pair, pairOutput, pairStack⟩ := space
  constructor <;> simp only [textImage, spillTwo] <;> exact_reads

theorem zeros_spills (s : ArmState) (space : ReturnSpace s) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (zerosImage s) =
      read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (zerosImage s) = r (.GPR 10#5) s := by
  obtain ⟨stack, output, separate, pair, pairOutput, pairStack⟩ := space
  constructor <;> simp only [zerosImage, spillTwo] <;> exact_reads

/-- Normalize the state once, rather than expanding instructions for each
StateField. All load facts below concern only the two fixed spill words. -/
macro "exact_cut_normalize" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [Cut.ops, Cut.image, actualImage, textImage, zerosImage, resultImage, spillTwo,
     block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, store_w, gpr_w_pc,
     state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

theorem actual_effect (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (hp : read_pc s = base + 124#64) :
    block base Cut.actual.ops s = Cut.actual.image base s := by
  have spills := actual_spills s space
  simp only [actualImage, spillTwo] at spills
  have hpc : r .PC s = base + 124#64 := hp
  exact_cut_normalize
  simp only [spills.1, spills.2, hpc, BitVec.add_assoc,
    show 124#64 + 48#64 = 172#64 by decide]
  apply congrArg (w .PC (base + 172#64))
  apply restore_spill_registers <;>
    simp (config := {decide := true}) [r_gpr_w, actualImage, spillTwo, r_of_write_mem_bytes]

theorem text_effect (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (hp : read_pc s = base + 172#64) :
    block base Cut.text.ops s = Cut.text.image base s := by
  have spills := text_spills s space
  simp only [textImage, spillTwo] at spills
  have hpc : r .PC s = base + 172#64 := hp
  exact_cut_normalize
  simp only [spills.1, spills.2, hpc, BitVec.add_assoc,
    show 172#64 + 40#64 = 212#64 by decide]
  apply congrArg (w .PC (base + 212#64))
  apply restore_spill_registers <;>
    simp (config := {decide := true}) [r_gpr_w, textImage, spillTwo, r_of_write_mem_bytes]

theorem zeros_effect (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (hp : read_pc s = base + 212#64) :
    block base Cut.zeros.ops s = Cut.zeros.image base s := by
  have spills := zeros_spills s space
  simp only [zerosImage, spillTwo] at spills
  have hpc : r .PC s = base + 212#64 := hp
  exact_cut_normalize
  simp only [spills.1, spills.2, hpc, BitVec.add_assoc,
    show 212#64 + 52#64 = 264#64 by decide]
  apply congrArg (w .PC (base + 264#64))
  apply restore_spill_registers <;>
    simp (config := {decide := true}) [r_gpr_w, zerosImage, spillTwo, r_of_write_mem_bytes]

theorem result_effect (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (hp : read_pc s = base + 264#64) :
    block base Cut.result.ops s = Cut.result.image base s := by
  have output := space.output
  have physical : (r (.GPR 0#5) s + 16#64).toNat + 16 ≤ 2^64 := by bv_omega
  exact_cut_normalize
  rw [UintCodec.Tail.write_pair_words _ _ _ _ physical]
  simp only [BitVec.add_assoc, show 16#64 + 8#64 = 24#64 by decide]
  try rfl

theorem cut_effect (cut : Cut) (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s) (hp : read_pc s = base + BitVec.ofNat 64 cut.start) :
    block base cut.ops s = cut.image base s := by
  cases cut
  · exact actual_effect s base space hp
  · exact text_effect s base space hp
  · exact zeros_effect s base space hp
  · exact result_effect s base space hp

theorem cut_run (cut : Cut) (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + BitVec.ofNat 64 cut.start) :
    run cut.ops.length s = cut.image base s := by
  rw [← cut_effect cut s base space hp]
  apply block_run base cut.ops s hc he ha
  have hpc : r .PC s = base + BitVec.ofNat 64 cut.start := hp
  cases cut <;> simp [Cut.ops, Cut.start, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

@[simp] theorem cut_register (cut : Cut) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (h8 : reg ≠ 8#5) (h9 : reg ≠ 9#5) :
    r (.GPR reg) (cut.image base s) = r (.GPR reg) s := by
  cases cut <;> simp [Cut.image, actualImage, textImage, zerosImage, resultImage,
    spillTwo, state_simp_rules, h8, h9]

@[simp] theorem cut_program (cut : Cut) (s : ArmState) (base : BitVec 64) :
    (cut.image base s).program = s.program := by
  cases cut <;> simp [Cut.image, actualImage, textImage, zerosImage, resultImage,
    spillTwo, state_simp_rules]

@[simp] theorem cut_error (cut : Cut) (s : ArmState) (base : BitVec 64) :
    read_err (cut.image base s) = read_err s := by
  cases cut <;> simp [Cut.image, actualImage, textImage, zerosImage, resultImage,
    spillTwo, state_simp_rules]

@[simp] theorem cut_sfp (cut : Cut) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (cut.image base s) = r (.SFP reg) s := by
  cases cut <;>
    simp (config := {decide := true, instances := true})
      [Cut.image, actualImage, textImage, zerosImage, resultImage, spillTwo, state_simp_rules]

theorem cut_space (cut : Cut) (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s) : ReturnSpace (cut.image base s) := by
  obtain ⟨stack, output, separate, pair, pairOutput, pairStack⟩ := space
  constructor <;>
    simp only [cut_register cut s base 31#5 (by decide) (by decide),
      cut_register cut s base 0#5 (by decide) (by decide),
      cut_register cut s base 1#5 (by decide) (by decide)] <;> assumption

theorem cut_aligned (cut : Cut) (s : ArmState) (base : BitVec 64)
    (ha : CheckSPAlignment s) : CheckSPAlignment (cut.image base s) := by
  simpa only [CheckSPAlignment, state_simp_rules,
    cut_register cut s base 31#5 (by decide) (by decide)] using ha

def failureResult (s : ArmState) (base : BitVec 64) : ArmState :=
  Cut.result.image base (Cut.zeros.image base (Cut.text.image base (Cut.actual.image base s)))

theorem failure_run (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 124#64) : run 39 s = failureResult s base := by
  have first := cut_run .actual s base space hc he ha hp
  have second := cut_run .text (Cut.actual.image base s) base (cut_space _ _ _ space)
    (by simpa only [CodeAt, cut_program] using hc) (by simpa using he)
    (cut_aligned _ _ _ ha) (by simp [Cut.image, state_simp_rules, Cut.start])
  have third := cut_run .zeros (Cut.text.image base (Cut.actual.image base s)) base
    (cut_space _ _ _ (cut_space _ _ _ space))
    (by simpa only [CodeAt, cut_program] using hc) (by simpa using he)
    (cut_aligned _ _ _ (cut_aligned _ _ _ ha))
    (by simp [Cut.image, state_simp_rules, Cut.start])
  have fourth := cut_run .result (Cut.zeros.image base (Cut.text.image base (Cut.actual.image base s))) base
    (cut_space _ _ _ (cut_space _ _ _ (cut_space _ _ _ space)))
    (by simpa only [CodeAt, cut_program] using hc) (by simpa using he)
    (cut_aligned _ _ _ (cut_aligned _ _ _ (cut_aligned _ _ _ ha)))
    (by simp [Cut.image, state_simp_rules, Cut.start])
  simp only [Cut.ops, List.length_cons, List.length_nil] at first second third fourth
  change run (12 + (10 + (13 + 4))) s = _
  rw [run_plus, first, run_plus, second, run_plus, third, fourth]
  rfl

macro "exact_failure_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [failureResult, Cut.image, actualImage, textImage, zerosImage, resultImage, spillTwo,
     state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

theorem failure_returned (s : ArmState) (base : BitVec 64) (he : read_err s = .None) :
    Returned s (failureResult s base) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact_failure_expand
  · simpa only [failureResult, cut_error] using he
  · simp [failureResult, cut_register]
  · intro reg low high
    have h8 : reg ≠ 8#5 := by bv_omega
    have h9 : reg ≠ 9#5 := by bv_omega
    simp only [failureResult, cut_register _ _ _ reg h8 h9]
  · intro reg low high
    simp only [failureResult, cut_sfp]

theorem failure_frame (s : ArmState) (base : BitVec 64) (space : ReturnSpace s) :
    MemoryFrame (localWrites s) s (failureResult s base) := by
  obtain ⟨stack, output, separate, pair, pairOutput, pairStack⟩ := space
  intro a outside
  have out := outside ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [localWrites])
  exact_failure_expand
  exact_reads
  simp (disch := exact_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem failure_image (s : ArmState) (base : BitVec 64) (expected : SszNative.NatOperand)
    (owned : Owned s expected)
    (rejected : SszNative.NatNarrow.runExact expected (r (.GPR 2#5) s) = false) :
    SszNative.NatNarrow.ExactResultAt (widthLoad (failureResult s base))
      (r (.GPR 0#5) s).toNat expected (r (.GPR 2#5) s) := by
  have frame := failure_frame s base owned.returnSpace
  have kept := NatDivision.operand_at_preserved frame expected owned.expectedAt.2.2 owned.operandOwned
  have pairReads := owned.expected_reads
  obtain ⟨stack, output, separate, pair, pairOutput, pairStack⟩ := owned.returnSpace
  simp only [SszNative.NatNarrow.ExactResultAt, rejected, Bool.false_eq_true, ↓reduceIte]
  refine ⟨?_, ?_, ⟨?_, ?_, kept⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    exact_failure_expand
    exact_reads
    try simp only [pairReads.1, pairReads.2]

def successResult (s : ArmState) (base : BitVec 64) : ArmState :=
  block base [.p272, .p276] s

theorem success_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 272#64) : run 2 s = successResult s base := by
  apply block_run base [.p272, .p276] s hc he ha
  have hpc : r .PC s = base + 272#64 := hp
  simp [Follows, Op.row, Op.effect, next, state_simp_rules, hpc, BitVec.add_assoc]

theorem success_returned (s : ArmState) (base : BitVec 64) (he : read_err s = .None) :
    Returned s (successResult s base) := by
  constructor
  · simp [successResult, block, Op.effect, next, state_simp_rules]
  · simpa [successResult, block, Op.effect, next, state_simp_rules] using he
  · simp [successResult, block, Op.effect, next, state_simp_rules]
  · intro reg low high
    simp [successResult, block, Op.effect, next, state_simp_rules]
  · intro reg low high
    simp [successResult, block, Op.effect, next, state_simp_rules]

theorem success_frame (s : ArmState) (base : BitVec 64) (expected : SszNative.NatOperand)
    (owned : Owned s expected)
    (accepted : SszNative.NatNarrow.runExact expected (r (.GPR 2#5) s) = true) :
    MemoryFrame (writesFor s expected) s (successResult s base) := by
  have output := owned.outputBound
  intro a outside
  have out := outside ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [writesFor, accepted])
  simp only [successResult, block, List.foldl_cons, List.foldl_nil, Op.effect, next,
    state_simp_rules, ArmState.mem_w_eq_mem]
  apply write_mem_bytes_frame <;> bv_omega

theorem success_image (s : ArmState) (base : BitVec 64) (expected : SszNative.NatOperand)
    (owned : Owned s expected) (h8 : r (.GPR 8#5) s = 0#64)
    (accepted : SszNative.NatNarrow.runExact expected (r (.GPR 2#5) s) = true) :
    SszNative.NatNarrow.ExactResultAt (widthLoad (successResult s base))
      (r (.GPR 0#5) s).toNat expected (r (.GPR 2#5) s) := by
  have output := owned.outputBound
  simp only [SszNative.NatNarrow.ExactResultAt, accepted, ↓reduceIte, widthLoad,
    BitVec.ofNat_add, BitVec.ofNat_toNat, successResult, block, List.foldl_cons,
    List.foldl_nil, Op.effect, next, state_simp_rules, h8]
  exact_reads

end SszArm.NatExact
