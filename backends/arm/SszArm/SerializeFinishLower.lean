import SszArm.SerializeFinishStage

namespace SszArm.Serialize.Finish

open Delimited (MemoryFrame Protected)

inductive Lower where
  | host48 | host32 | host16 | host0
  | capacity16 | capacity0 | capacity32 | capacity48
  deriving DecidableEq

def Lower.entry : Lower → Nat
  | .host48 => 228 | .host32 => 276 | .host16 => 324 | .host0 => 372
  | .capacity16 => 436 | .capacity0 => 484 | .capacity32 => 524 | .capacity48 => 572

def Lower.finish : Lower → Nat
  | .host48 => 276 | .host32 => 324 | .host16 => 372 | .host0 => 412
  | .capacity16 => 484 | .capacity0 => 524 | .capacity32 => 572 | .capacity48 => 620

def Lower.displacement : Lower → BitVec 64
  | .host48 | .capacity48 => 48#64
  | .host32 | .capacity32 => 32#64
  | .host16 | .capacity16 => 16#64
  | .host0 | .capacity0 => 0#64

def Lower.low (kind : Lower) (s : ArmState) : BitVec 64 :=
  match kind with
  | .host0 | .capacity0 => r (.GPR 8#5) s
  | _ => 0#64

def Lower.ops : Lower → List Op
  | .host48 => [.p228, .p232, .p236, .p240, .p244, .p248, .p252, .p256, .p260,
      .p264, .p268, .p272]
  | .host32 => [.p276, .p280, .p284, .p288, .p292, .p296, .p300, .p304, .p308,
      .p312, .p316, .p320]
  | .host16 => [.p324, .p328, .p332, .p336, .p340, .p344, .p348, .p352, .p356,
      .p360, .p364, .p368]
  | .host0 => [.p372, .p376, .p380, .p384, .p388, .p392, .p396, .p400, .p404, .p408]
  | .capacity16 => [.p436, .p440, .p444, .p448, .p452, .p456, .p460, .p464, .p468,
      .p472, .p476, .p480]
  | .capacity0 => [.p484, .p488, .p492, .p496, .p500, .p504, .p508, .p512, .p516, .p520]
  | .capacity32 => [.p524, .p528, .p532, .p536, .p540, .p544, .p548, .p552, .p556,
      .p560, .p564, .p568]
  | .capacity48 => [.p572, .p576, .p580, .p584, .p588, .p592, .p596, .p600, .p604,
      .p608, .p612, .p616]

def scratch (s : ArmState) : ArmState :=
  write_mem_bytes 8 (sp s - 8#64) (r (.GPR 10#5) s)
    (write_mem_bytes 8 (sp s - 16#64) (r (.GPR 9#5) s) s)

def Lower.memory (kind : Lower) (s : ArmState) : ArmState :=
  write_mem_bytes 8 (result s + kind.displacement + 8#64) 0#64
    (write_mem_bytes 8 (result s + kind.displacement) (kind.low s) (scratch s))

/-- Both reloads observe the post-result-store state. No nonalias premise is hidden. -/
def Lower.state (kind : Lower) (base : BitVec 64) (s : ArmState) : ArmState :=
  let memory := kind.memory s
  w .PC (base + BitVec.ofNat 64 kind.finish)
    (w (.GPR 9#5) (read_mem_bytes 8 (sp s - 16#64) memory)
      (w (.GPR 10#5) (read_mem_bytes 8 (sp s - 8#64) memory) memory))

theorem Lower.effect (kind : Lower) (base : BitVec 64) (s : ArmState)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry) :
    block base kind.ops s = kind.state base s := by
  change r .PC s = _ at pc
  cases kind <;>
    simp only [Lower.entry] at pc <;>
    simp [Lower.ops, block, Op.effect, next, put, Lower.state, Lower.memory,
      Lower.displacement, Lower.low, Lower.finish, scratch, sp, result,
      state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg, pc]
  all_goals
    apply state_eq_iff_components_eq.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro field
      simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes,
        Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]
      cases field with
      | GPR reg =>
        by_cases stack : reg = 31#5 <;>
          by_cases nine : reg = 9#5 <;>
          by_cases ten : reg = 10#5 <;>
          simp_all [state_simp_rules, r, w, read_base_gpr,
            write_base_gpr, write_base_pc, read_store, write_store]
      | SFP reg =>
        simp [r, w, read_base_sfp, write_base_gpr, write_base_pc]
      | PC =>
        simp [r, w, read_base_pc, write_base_gpr, write_base_pc]
      | FLAG flag =>
        simp [r, w, read_base_flag, write_base_gpr, write_base_pc]
      | ERR =>
        simp [r, w, read_base_error, write_base_gpr, write_base_pc]
    · simp [state_simp_rules]
    · intro bytes address
      simp [state_simp_rules, Memory.State.read_mem_bytes_eq_mem_read_bytes,
        Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem Lower.run (kind : Lower) (base : BitVec 64) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry) :
    run kind.ops.length s = kind.state base s := by
  rw [← kind.effect base s pc]
  apply block_run base kind.ops s code error aligned
  change r .PC s = _ at pc
  cases kind <;>
    simp only [Lower.entry] at pc <;>
    simp [Follows, Lower.ops, Op.row, Op.effect, next, put,
      state_simp_rules, BitVec.add_assoc, pc]

@[simp] theorem Lower.program (kind : Lower) (base : BitVec 64) (s : ArmState) :
    (kind.state base s).program = s.program := by
  simp [Lower.state, Lower.memory, scratch, state_simp_rules]

@[simp] theorem Lower.error (kind : Lower) (base : BitVec 64) (s : ArmState) :
    read_err (kind.state base s) = read_err s := by
  simp [Lower.state, Lower.memory, scratch, state_simp_rules]

@[simp] theorem Lower.pc (kind : Lower) (base : BitVec 64) (s : ArmState) :
    read_pc (kind.state base s) = base + BitVec.ofNat 64 kind.finish := by
  simp [Lower.state, state_simp_rules]

@[simp] theorem Lower.register (kind : Lower) (base : BitVec 64) (s : ArmState)
    (reg : BitVec 5) (nine : reg ≠ 9#5) (ten : reg ≠ 10#5) :
    r (.GPR reg) (kind.state base s) = r (.GPR reg) s := by
  simp [Lower.state, Lower.memory, scratch, state_simp_rules, nine, ten]

@[simp] theorem Lower.sp (kind : Lower) (base : BitVec 64) (s : ArmState) :
    sp (kind.state base s) = sp s := kind.register base s _ (by decide) (by decide)

@[simp] theorem Lower.result (kind : Lower) (base : BitVec 64) (s : ArmState) :
    result (kind.state base s) = result s := kind.register base s _ (by decide) (by decide)

@[simp] theorem Lower.vector (kind : Lower) (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (kind.state base s) = r (.SFP reg) s := by
  simp [Lower.state, Lower.memory, scratch, state_simp_rules]

@[simp] theorem Lower.mem (kind : Lower) (base : BitVec 64) (s : ArmState) :
    (kind.state base s).mem = (kind.memory s).mem := by
  simp [Lower.state, state_simp_rules]

/-- Only local nonwrapping geometry; neither output nor lowering scratch is initialized. -/
structure ErrorSpace (s : ArmState) : Prop where
  stackLow : 16 ≤ (sp s).toNat
  stackHigh : (sp s).toNat + 144 ≤ 2^64
  resultHigh : (result s).toNat + 72 ≤ 2^64
  scratchApart : (result s).toNat + 72 ≤ (sp s).toNat - 16 ∨
    (sp s).toNat ≤ (result s).toNat
  savedApart : (result s).toNat + 72 ≤ (sp s).toNat + 96 ∨
    (sp s).toNat + 144 ≤ (result s).toNat

theorem Lower.space (kind : Lower) (base : BitVec 64) (s : ArmState)
    (space : ErrorSpace s) : ErrorSpace (kind.state base s) := by
  constructor
  · simpa only [Lower.sp] using space.stackLow
  · simpa only [Lower.sp] using space.stackHigh
  · simpa only [Lower.result] using space.resultHigh
  · simpa only [Lower.sp, Lower.result] using space.scratchApart
  · simpa only [Lower.sp, Lower.result] using space.savedApart

private theorem Lower.displacement_le (kind : Lower) :
    kind.displacement.toNat ≤ 48 := by cases kind <;> decide

private theorem Lower.scratch_read (kind : Lower) (s : ArmState)
    (space : ErrorSpace s) (bytes : Nat) (address : BitVec 64)
    (lower : (Finish.sp s).toNat - 16 ≤ address.toNat)
    (upper : address.toNat + bytes ≤ (Finish.sp s).toNat) :
    read_mem_bytes bytes address (kind.memory s) =
      read_mem_bytes bytes address (scratch s) := by
  rcases space with ⟨stackLow, stackHigh, resultHigh, scratchApart, savedApart⟩
  have displacement := kind.displacement_le
  unfold Lower.memory
  rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ bytes 8
    address (Finish.result s + kind.displacement + 8#64) _
    (by bv_omega) (by bv_omega) (by rcases scratchApart with h | h <;> bv_omega)]
  rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ bytes 8
    address (Finish.result s + kind.displacement) _
    (by bv_omega) (by bv_omega) (by rcases scratchApart with h | h <;> bv_omega)]

theorem Lower.reloads (kind : Lower) (base : BitVec 64) (s : ArmState)
    (space : ErrorSpace s) :
    r (.GPR 9#5) (kind.state base s) = r (.GPR 9#5) s ∧
    r (.GPR 10#5) (kind.state base s) = r (.GPR 10#5) s := by
  have low := space.stackLow
  have high := space.stackHigh
  constructor
  · simp only [Lower.state, state_simp_rules]
    simp [state_simp_rules]
    rw [kind.scratch_read s space 8 (Finish.sp s - 16#64) (by bv_omega) (by bv_omega)]
    unfold scratch
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8
      (Finish.sp s - 16#64) (Finish.sp s - 8#64) _
      (by bv_omega) (by bv_omega) (by left; bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)
  · simp only [Lower.state, state_simp_rules]
    simp [state_simp_rules]
    rw [kind.scratch_read s space 8 (Finish.sp s - 8#64) (by bv_omega) (by bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)

theorem Lower.frame (kind : Lower) (base : BitVec 64) (s : ArmState)
    (space : ErrorSpace s) :
    MemoryFrame [((Finish.sp s).toNat - 16, 16),
      ((Finish.result s + kind.displacement).toNat, 16)]
      s (kind.state base s) := by
  rcases space with ⟨stackLow, stackHigh, resultHigh, scratchApart, savedApart⟩
  have displacement := kind.displacement_le
  intro address outside
  have stackOutside := outside ((Finish.sp s).toNat - 16, 16) (by simp)
  have resultOutside := outside ((Finish.result s + kind.displacement).toNat, 16) (by simp)
  rw [Lower.mem]
  unfold Lower.memory scratch
  rw [BoolCodec.write_mem_bytes_frame _ (Finish.result s + kind.displacement + 8#64)
    8 _ address (by bv_omega) (by bv_omega)]
  rw [BoolCodec.write_mem_bytes_frame _ (Finish.result s + kind.displacement)
    8 _ address (by bv_omega) (by bv_omega)]
  rw [BoolCodec.write_mem_bytes_frame _ (Finish.sp s - 8#64)
    8 _ address (by bv_omega) (by bv_omega)]
  exact BoolCodec.write_mem_bytes_frame _ (Finish.sp s - 16#64)
    8 _ address (by bv_omega) (by bv_omega)

end SszArm.Serialize.Finish
