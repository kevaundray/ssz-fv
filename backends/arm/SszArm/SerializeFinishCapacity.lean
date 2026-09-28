import SszArm.SerializeFinishLower
import SszArm.MeasureContract

namespace SszArm.Serialize.Finish

open Delimited (MemoryFrame)
open UintCodec (widthLoad)

inductive Failure where
  | host | capacity
  deriving DecidableEq

def Failure.entry : Failure → Nat | .host => 224 | .capacity => 432

def Failure.ops : Failure → List Op
  | .host => [.p224] ++ Lower.host48.ops ++ Lower.host32.ops ++ Lower.host16.ops ++
      Lower.host0.ops ++ [.p412]
  | .capacity => [.p432] ++ Lower.capacity16.ops ++ Lower.capacity0.ops ++
      Lower.capacity32.ops ++ Lower.capacity48.ops

def Failure.state (kind : Failure) (base : BitVec 64) (s : ArmState) : ArmState :=
  match kind with
  | .host => w .PC (base + 620#64)
      (Lower.host0.state base (Lower.host16.state base
        (Lower.host32.state base (Lower.host48.state base (put 8#5 1#64 s)))))
  | .capacity => Lower.capacity48.state base (Lower.capacity32.state base
      (Lower.capacity0.state base (Lower.capacity16.state base (put 8#5 1#64 s))))

theorem block_append (base : BitVec 64) (xs ys : List Op) (s : ArmState) :
    block base (xs ++ ys) s = block base ys (block base xs s) := by
  simp [block, List.foldl_append]

private theorem lower_pc_field (kind : Lower) (base : BitVec 64) (s : ArmState) :
    r .PC (kind.state base s) = base + BitVec.ofNat 64 kind.finish :=
  kind.pc base s

private theorem lower_error_field (kind : Lower) (base : BitVec 64) (s : ArmState) :
    r .ERR (kind.state base s) = r .ERR s :=
  kind.error base s

theorem Failure.effect (kind : Failure) (base : BitVec 64) (s : ArmState)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry) :
    block base kind.ops s = kind.state base s := by
  change r .PC s = _ at pc
  cases kind <;> simp only [Failure.entry] at pc
  · simp only [Failure.ops, block_append]
    change block base [.p412]
      (block base Lower.host0.ops (block base Lower.host16.ops
        (block base Lower.host32.ops (block base Lower.host48.ops (put 8#5 1#64 s))))) = _
    rw [Lower.effect .host48 base _ (by simp [Lower.entry, put, next, state_simp_rules,
      pc, BitVec.add_assoc])]
    rw [Lower.effect .host32 base _ (by simp [Lower.entry, Lower.finish])]
    rw [Lower.effect .host16 base _ (by simp [Lower.entry, Lower.finish])]
    rw [Lower.effect .host0 base _ (by simp [Lower.entry, Lower.finish])]
    rfl
  · simp only [Failure.ops, block_append]
    change block base Lower.capacity48.ops (block base Lower.capacity32.ops
      (block base Lower.capacity0.ops (block base Lower.capacity16.ops (put 8#5 1#64 s)))) = _
    rw [Lower.effect .capacity16 base _ (by simp [Lower.entry, put, next, state_simp_rules,
      pc, BitVec.add_assoc])]
    rw [Lower.effect .capacity0 base _ (by simp [Lower.entry, Lower.finish])]
    rw [Lower.effect .capacity32 base _ (by simp [Lower.entry, Lower.finish])]
    rw [Lower.effect .capacity48 base _ (by simp [Lower.entry, Lower.finish])]
    rfl

theorem Failure.run (kind : Failure) (base : BitVec 64) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry) :
    run kind.ops.length s = kind.state base s := by
  rw [← kind.effect base s pc]
  apply block_run base kind.ops s code error aligned
  change r .PC s = _ at pc
  cases kind <;> simp only [Failure.entry] at pc <;>
    simp [Follows, Failure.ops, Lower.ops, Op.row, Op.effect, next, put,
      state_simp_rules, BitVec.add_assoc, pc]

@[simp] theorem Failure.pc (kind : Failure) (base : BitVec 64) (s : ArmState) :
    read_pc (kind.state base s) = base + 620#64 := by
  cases kind <;>
    simp [Failure.state, Lower.finish, state_simp_rules, lower_pc_field]

@[simp] theorem Failure.program (kind : Failure) (base : BitVec 64) (s : ArmState) :
    (kind.state base s).program = s.program := by
  cases kind <;> simp [Failure.state, put, next, state_simp_rules]

@[simp] theorem Failure.error (kind : Failure) (base : BitVec 64) (s : ArmState) :
    read_err (kind.state base s) = read_err s := by
  cases kind <;>
    simp [Failure.state, put, next, state_simp_rules, lower_error_field]

private theorem failure_error_field (kind : Failure) (base : BitVec 64) (s : ArmState) :
    r .ERR (kind.state base s) = r .ERR s :=
  kind.error base s

@[simp] theorem Failure.register (kind : Failure) (base : BitVec 64) (s : ArmState)
    (reg : BitVec 5) (eight : reg ≠ 8#5) (nine : reg ≠ 9#5) (ten : reg ≠ 10#5) :
    r (.GPR reg) (kind.state base s) = r (.GPR reg) s := by
  cases kind <;> simp [Failure.state, put, next, state_simp_rules, eight, nine, ten]

@[simp] theorem Failure.sp (kind : Failure) (base : BitVec 64) (s : ArmState) :
    sp (kind.state base s) = sp s := kind.register base s _ (by decide) (by decide) (by decide)

@[simp] theorem Failure.result (kind : Failure) (base : BitVec 64) (s : ArmState) :
    result (kind.state base s) = result s := kind.register base s _ (by decide) (by decide) (by decide)

@[simp] theorem Failure.vector (kind : Failure) (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (kind.state base s) = r (.SFP reg) s := by
  cases kind <;> simp [Failure.state, put, next, state_simp_rules]

/-- The status store writes four bytes, deliberately leaving result[68..72) alone. -/
def failureTagged (base : BitVec 64) (s : ArmState) : ArmState :=
  w .PC (base + 628#64)
    (write_mem_bytes 4 (result s + 64#64) 32769#32 (w (.GPR 8#5) 32769#64 s))

theorem failure_tag_run (base : BitVec 64) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 620#64) : run 2 s = failureTagged base s := by
  have execution := block_run base [.p620, .p624] s code error aligned (by
    change r .PC s = _ at pc
    simp [Follows, Op.row, Op.effect, next, put, state_simp_rules, pc, BitVec.add_assoc])
  change run 2 s = _ at execution
  rw [execution]
  change r .PC s = _ at pc
  have pcValue := pc
  simp only [r, read_base_pc] at pcValue
  simp [block, Op.effect, next, put, failureTagged, result, state_simp_rules,
    pc, pcValue, BitVec.add_assoc, Memory.write_mem_bytes_eq_mem_write_bytes,
    r, w, read_base_gpr, read_base_pc, write_base_gpr, write_base_pc,
    read_store, write_store]

def Failure.returned (kind : Failure) (base : BitVec 64) (s : ArmState) : ArmState :=
  Finish.returned (failureTagged base (kind.state base s))

theorem Failure.return_run (kind : Failure) (base : BitVec 64) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry) :
    _root_.run (kind.ops.length + (2 + 5)) s = kind.returned base s := by
  rw [run_plus, kind.run base s code error aligned pc, run_plus]
  have stateCode := code.congr (kind.program base s)
  have stateError := (kind.error base s).trans error
  have stateAligned : CheckSPAlignment (kind.state base s) := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Failure.sp] using aligned
  rw [failure_tag_run base _ stateCode stateError stateAligned (kind.pc base s)]
  change _root_.run 5 (failureTagged base (kind.state base s)) =
    Finish.returned (failureTagged base (kind.state base s))
  apply Finish.return_run .capacity base (failureTagged base (kind.state base s))
  · exact stateCode.congr (by simp [failureTagged, state_simp_rules])
  · change r .ERR (failureTagged base (kind.state base s)) = .None
    simpa [failureTagged, state_simp_rules, failure_error_field] using error
  · simpa [failureTagged, CheckSPAlignment, read_gpr, state_simp_rules] using stateAligned
  · simp [failureTagged, Exit.entry, state_simp_rules]

private theorem put_error_space (s : ArmState) (space : ErrorSpace s) :
    ErrorSpace (put 8#5 1#64 s) := by
  rcases space with ⟨lo, hi, out, apart, saved⟩
  constructor
  · simpa [Finish.sp, put, next, state_simp_rules] using lo
  · simpa [Finish.sp, put, next, state_simp_rules] using hi
  · simpa [Finish.result, put, next, state_simp_rules] using out
  · simpa [Finish.sp, Finish.result, put, next, state_simp_rules] using apart
  · simpa [Finish.sp, Finish.result, put, next, state_simp_rules] using saved

private theorem failure_error_space (kind : Failure) (base : BitVec 64)
    (s : ArmState) (space : ErrorSpace s) : ErrorSpace (kind.state base s) := by
  rcases space with ⟨lo, hi, out, apart, saved⟩
  constructor
  · simpa only [Failure.sp] using lo
  · simpa only [Failure.sp] using hi
  · simpa only [Failure.result] using out
  · simpa only [Failure.sp, Failure.result] using apart
  · simpa only [Failure.sp, Failure.result] using saved

private theorem lower_payload_lane (kind : Lower) (base : BitVec 64) (s : ArmState)
    (space : ErrorSpace s) (out : BitVec 64) (output : Finish.result s = out)
    (index : Fin 8) :
    read_mem_bytes 8 (out + BitVec.ofNat 64 (8 * index.val)) (kind.state base s) =
      if 8 * index.val = kind.displacement.toNat then kind.low s
      else if 8 * index.val = kind.displacement.toNat + 8 then 0#64
      else read_mem_bytes 8 (out + BitVec.ofNat 64 (8 * index.val)) s := by
  rw [← output]
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp (kind.mem base s)]
  rcases space with ⟨stackLow, stackHigh, resultHigh, scratchApart, savedApart⟩
  have indexBound := index.isLt
  have displacement : kind.displacement.toNat = 0 ∨ kind.displacement.toNat = 16 ∨
      kind.displacement.toNat = 32 ∨ kind.displacement.toNat = 48 := by
    cases kind <;> decide
  have scratchRead :
      read_mem_bytes 8 (Finish.result s + BitVec.ofNat 64 (8 * index.val)) (scratch s) =
        read_mem_bytes 8 (Finish.result s + BitVec.ofNat 64 (8 * index.val)) s := by
    unfold scratch
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8
      (Finish.result s + BitVec.ofNat 64 (8 * index.val)) (Finish.sp s - 8#64) _
      (by bv_omega) (by bv_omega) (by rcases scratchApart with h | h <;> bv_omega)]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8
      (Finish.result s + BitVec.ofNat 64 (8 * index.val)) (Finish.sp s - 16#64) _
      (by bv_omega) (by bv_omega) (by rcases scratchApart with h | h <;> bv_omega)]
  by_cases first : 8 * index.val = kind.displacement.toNat
  · rw [if_pos first]
    have address : Finish.result s + BitVec.ofNat 64 (8 * index.val) =
        Finish.result s + kind.displacement := by bv_omega
    rw [address, Lower.memory]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8
      (Finish.result s + kind.displacement) (Finish.result s + kind.displacement + 8#64) _
      (by bv_omega) (by bv_omega) (by left; bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)
  · rw [if_neg first]
    by_cases second : 8 * index.val = kind.displacement.toNat + 8
    · rw [if_pos second]
      have address : Finish.result s + BitVec.ofNat 64 (8 * index.val) =
          Finish.result s + kind.displacement + 8#64 := by bv_omega
      rw [address, Lower.memory]
      exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)
    · rw [if_neg second, Lower.memory]
      rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8
        (Finish.result s + BitVec.ofNat 64 (8 * index.val))
        (Finish.result s + kind.displacement + 8#64) _
        (by bv_omega) (by bv_omega)
        (by rcases displacement with h | h | h | h <;> bv_omega)]
      rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8
        (Finish.result s + BitVec.ofNat 64 (8 * index.val))
        (Finish.result s + kind.displacement) _
        (by bv_omega) (by bv_omega)
        (by rcases displacement with h | h | h | h <;> bv_omega)]
      exact scratchRead

private theorem failure_tag_payload (base : BitVec 64) (s : ArmState)
    (space : ErrorSpace s) (index : Fin 8) :
    read_mem_bytes 8 (Finish.result s + BitVec.ofNat 64 (8 * index.val))
        (failureTagged base s) =
      read_mem_bytes 8 (Finish.result s + BitVec.ofNat 64 (8 * index.val)) s := by
  have physical := space.resultHigh
  have indexBound := index.isLt
  simp only [failureTagged, state_simp_rules]
  rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 4
    (Finish.result s + BitVec.ofNat 64 (8 * index.val)) (Finish.result s + 64#64) _
    (by bv_omega) (by bv_omega) (by left; bv_omega)]
  simp [state_simp_rules]

/-- Full error writer fields, with no prior reads or initialized result premise. -/
theorem Failure.payload (kind : Failure) (base : BitVec 64) (s : ArmState)
    (space : ErrorSpace s) (index : Fin 8) :
    read_mem_bytes 8 (Finish.result s + BitVec.ofNat 64 (8 * index.val)) (kind.returned base s) =
      if index.val = 0 then 1#64 else 0#64 := by
  have beforeTag :
      read_mem_bytes 8 (Finish.result s + BitVec.ofNat 64 (8 * index.val))
          (kind.returned base s) =
        read_mem_bytes 8 (Finish.result s + BitVec.ofNat 64 (8 * index.val))
          (kind.state base s) := by
    unfold Failure.returned
    rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp
      (returned_memory (failureTagged base (kind.state base s)))]
    simpa only [Failure.result] using failure_tag_payload base (kind.state base s)
      (failure_error_space kind base s space) index
  rw [beforeTag]
  have initialSpace := put_error_space s space
  cases kind with
  | host =>
    let t0 := put 8#5 1#64 s
    let t1 := Lower.host48.state base t0
    let t2 := Lower.host32.state base t1
    let t3 := Lower.host16.state base t2
    have space1 := Lower.host48.space base t0 initialSpace
    have space2 := Lower.host32.space base t1 space1
    have space3 := Lower.host16.space base t2 space2
    simp only [Failure.state, state_simp_rules]
    rw [lower_payload_lane .host0 base t3 space3 (Finish.result s)
      (by simp [t3, t2, t1, t0, Finish.result, put, next, state_simp_rules]) index]
    rw [lower_payload_lane .host16 base t2 space2 (Finish.result s)
      (by simp [t2, t1, t0, Finish.result, put, next, state_simp_rules]) index]
    rw [lower_payload_lane .host32 base t1 space1 (Finish.result s)
      (by simp [t1, t0, Finish.result, put, next, state_simp_rules]) index]
    rw [lower_payload_lane .host48 base t0 initialSpace (Finish.result s)
      (by simp [t0, Finish.result, put, next, state_simp_rules]) index]
    rcases index with ⟨index, bound⟩
    have indices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
    rcases indices with h | h | h | h | h | h | h | h <;> subst index <;>
      simp [Lower.low, Lower.displacement, t3, t2, t1, t0, put, next, state_simp_rules]
  | capacity =>
    let t0 := put 8#5 1#64 s
    let t1 := Lower.capacity16.state base t0
    let t2 := Lower.capacity0.state base t1
    let t3 := Lower.capacity32.state base t2
    have space1 := Lower.capacity16.space base t0 initialSpace
    have space2 := Lower.capacity0.space base t1 space1
    have space3 := Lower.capacity32.space base t2 space2
    simp only [Failure.state]
    rw [lower_payload_lane .capacity48 base t3 space3 (Finish.result s)
      (by simp [t3, t2, t1, t0, Finish.result, put, next, state_simp_rules]) index]
    rw [lower_payload_lane .capacity32 base t2 space2 (Finish.result s)
      (by simp [t2, t1, t0, Finish.result, put, next, state_simp_rules]) index]
    rw [lower_payload_lane .capacity0 base t1 space1 (Finish.result s)
      (by simp [t1, t0, Finish.result, put, next, state_simp_rules]) index]
    rw [lower_payload_lane .capacity16 base t0 initialSpace (Finish.result s)
      (by simp [t0, Finish.result, put, next, state_simp_rules]) index]
    rcases index with ⟨index, bound⟩
    have indices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
    rcases indices with h | h | h | h | h | h | h | h <;> subst index <;>
      simp [Lower.low, Lower.displacement, t3, t2, t1, t0, put, next, state_simp_rules]

theorem Failure.status (kind : Failure) (base : BitVec 64) (s : ArmState)
    (space : ErrorSpace s) :
    read_mem_bytes 4 (Finish.result s + 64#64) (kind.returned base s) = 32769#32 := by
  have bound := space.resultHigh
  unfold Failure.returned
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp
    (returned_memory (failureTagged base (kind.state base s)))]
  simp only [failureTagged, state_simp_rules, Failure.result]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 4 _ _ (by bv_omega)

private theorem lower_frame_step (kind : Lower) (base : BitVec 64) (original s : ArmState)
    (space : ErrorSpace s) (stack : Finish.sp s = Finish.sp original)
    (output : Finish.result s = Finish.result original)
    (frame : MemoryFrame [((Finish.sp original).toNat - 16, 16),
      ((Finish.result original).toNat, 68)] original s) :
    MemoryFrame [((Finish.sp original).toNat - 16, 16),
      ((Finish.result original).toNat, 68)] original (kind.state base s) := by
  apply frame.trans
  intro address outside
  have stackOutside := outside ((Finish.sp original).toNat - 16, 16) (by simp)
  have resultOutside := outside ((Finish.result original).toNat, 68) (by simp)
  have resultHigh := space.resultHigh
  have displacement : kind.displacement.toNat ≤ 48 := by cases kind <;> decide
  apply kind.frame base s space address
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simpa only [Prod.fst, Prod.snd, stack] using stackOutside
  · simp only [Prod.fst, Prod.snd]
    rw [← output] at resultOutside
    bv_omega

private theorem failure_state_frame (kind : Failure) (base : BitVec 64) (s : ArmState)
    (space : ErrorSpace s) :
    MemoryFrame [((Finish.sp s).toNat - 16, 16), ((Finish.result s).toNat, 68)]
      s (kind.state base s) := by
  let t0 := put 8#5 1#64 s
  have space0 := put_error_space s space
  have stack0 : Finish.sp t0 = Finish.sp s := by
    simp [t0, Finish.sp, put, next, state_simp_rules]
  have output0 : Finish.result t0 = Finish.result s := by
    simp [t0, Finish.result, put, next, state_simp_rules]
  have frame0 : MemoryFrame [((Finish.sp s).toNat - 16, 16),
      ((Finish.result s).toNat, 68)] s t0 := by
    intro address outside
    simp [t0, put, next, state_simp_rules]
  cases kind with
  | host =>
    let t1 := Lower.host48.state base t0
    let t2 := Lower.host32.state base t1
    let t3 := Lower.host16.state base t2
    have space1 := Lower.host48.space base t0 space0
    have space2 := Lower.host32.space base t1 space1
    have space3 := Lower.host16.space base t2 space2
    have frame1 := lower_frame_step .host48 base s t0 space0 stack0 output0 frame0
    have frame2 := lower_frame_step .host32 base s t1 space1
      (by simpa [t1] using stack0) (by simpa [t1] using output0) frame1
    have frame3 := lower_frame_step .host16 base s t2 space2
      (by simpa [t2, t1] using stack0) (by simpa [t2, t1] using output0) frame2
    have frame4 := lower_frame_step .host0 base s t3 space3
      (by simpa [t3, t2, t1] using stack0) (by simpa [t3, t2, t1] using output0) frame3
    intro address outside
    simpa only [Failure.state, ArmState.mem_w_eq_mem] using frame4 address outside
  | capacity =>
    let t1 := Lower.capacity16.state base t0
    let t2 := Lower.capacity0.state base t1
    let t3 := Lower.capacity32.state base t2
    have space1 := Lower.capacity16.space base t0 space0
    have space2 := Lower.capacity0.space base t1 space1
    have space3 := Lower.capacity32.space base t2 space2
    have frame1 := lower_frame_step .capacity16 base s t0 space0 stack0 output0 frame0
    have frame2 := lower_frame_step .capacity0 base s t1 space1
      (by simpa [t1] using stack0) (by simpa [t1] using output0) frame1
    have frame3 := lower_frame_step .capacity32 base s t2 space2
      (by simpa [t2, t1] using stack0) (by simpa [t2, t1] using output0) frame2
    have frame4 := lower_frame_step .capacity48 base s t3 space3
      (by simpa [t3, t2, t1] using stack0) (by simpa [t3, t2, t1] using output0) frame3
    exact frame4

theorem Failure.frame (kind : Failure) (base : BitVec 64) (s : ArmState)
    (space : ErrorSpace s) :
    MemoryFrame [((Finish.sp s).toNat - 16, 16), ((Finish.result s).toNat, 68)]
      s (kind.returned base s) := by
  have physical := space.resultHigh
  have stateFrame := failure_state_frame kind base s space
  intro address outside
  have resultOutside := outside ((Finish.result s).toNat, 68) (by simp)
  unfold Failure.returned
  rw [returned_memory]
  simp only [failureTagged, ArmState.mem_w_eq_mem, Failure.result]
  rw [BoolCodec.write_mem_bytes_frame _ (Finish.result s + 64#64)
    4 _ address (by bv_omega) (by bv_omega)]
  simp only [ArmState.mem_w_eq_mem]
  exact stateFrame address outside

theorem Failure.padding (kind : Failure) (base : BitVec 64) (s : ArmState)
    (space : ErrorSpace s) :
    read_mem_bytes 4 (Finish.result s + 68#64) (kind.returned base s) =
      read_mem_bytes 4 (Finish.result s + 68#64) s := by
  have physical := space.resultHigh
  have low := space.stackLow
  have apart := space.scratchApart
  apply (kind.frame base s space).read _ 4 (by bv_omega)
  right
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> bv_omega

theorem Failure.error_at (kind : Failure) (base : BitVec 64) (s : ArmState)
    (space : ErrorSpace s) :
    Measure.ErrorAt (widthLoad (kind.returned base s)) (Finish.result s).toNat .outputTooSmall := by
  have payload := kind.payload base s space
  have status := kind.status base s space
  have lane0 : read_mem_bytes 8 (Finish.result s + 0#64) (kind.returned base s) = 1#64 :=
    payload ⟨0, by decide⟩
  have lane1 : read_mem_bytes 8 (Finish.result s + 8#64) (kind.returned base s) = 0#64 :=
    payload ⟨1, by decide⟩
  have lane2 : read_mem_bytes 8 (Finish.result s + 16#64) (kind.returned base s) = 0#64 :=
    payload ⟨2, by decide⟩
  have lane3 : read_mem_bytes 8 (Finish.result s + 24#64) (kind.returned base s) = 0#64 :=
    payload ⟨3, by decide⟩
  have lane4 : read_mem_bytes 8 (Finish.result s + 32#64) (kind.returned base s) = 0#64 :=
    payload ⟨4, by decide⟩
  have lane5 : read_mem_bytes 8 (Finish.result s + 40#64) (kind.returned base s) = 0#64 :=
    payload ⟨5, by decide⟩
  have lane6 : read_mem_bytes 8 (Finish.result s + 48#64) (kind.returned base s) = 0#64 :=
    payload ⟨6, by decide⟩
  have lane7 : read_mem_bytes 8 (Finish.result s + 56#64) (kind.returned base s) = 0#64 :=
    payload ⟨7, by decide⟩
  refine ⟨?_, ?_, ⟨?_, ?_, trivial⟩, ⟨?_, ?_, trivial⟩, ?_, ?_, ?_⟩
  · simpa [widthLoad, BitVec.ofNat_toNat] using congrArg (fun x : BitVec 64 => some x.toNat) lane0
  · simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using
      congrArg (fun x : BitVec 64 => some x.toNat) lane1
  · simpa [Measure.errorOperands, SszNative.NatOperand.pointer, widthLoad,
      BitVec.ofNat_add, BitVec.ofNat_toNat] using congrArg (fun x : BitVec 64 => some x.toNat) lane2
  · simpa [Measure.errorOperands, SszNative.NatOperand.payload, widthLoad,
      BitVec.ofNat_add, BitVec.ofNat_toNat, Nat.add_assoc] using
      congrArg (fun x : BitVec 64 => some x.toNat) lane3
  · simpa [Measure.errorOperands, SszNative.NatOperand.pointer, widthLoad,
      BitVec.ofNat_add, BitVec.ofNat_toNat] using congrArg (fun x : BitVec 64 => some x.toNat) lane4
  · simpa [Measure.errorOperands, SszNative.NatOperand.payload, widthLoad,
      BitVec.ofNat_add, BitVec.ofNat_toNat, Nat.add_assoc] using
      congrArg (fun x : BitVec 64 => some x.toNat) lane5
  · simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using
      congrArg (fun x : BitVec 64 => some x.toNat) lane6
  · simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using
      congrArg (fun x : BitVec 64 => some x.toNat) lane7
  · simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, Measure.errorCode] using
      congrArg (fun x : BitVec 32 => some x.toNat) status

/-- The lowering scratch and actual result stores preserve all six saved words. -/
theorem Failure.returned_original (kind : Failure) (base : BitVec 64) (original s : ArmState)
    (space : ErrorSpace s) (savedFrom : SavedFrom original s)
    (program : s.program = original.program) (error : read_err s = .None) :
    Emit.Returned original (kind.returned base s) := by
  let t := failureTagged base (kind.state base s)
  have stack : Finish.sp t = Finish.sp s := by
    simp [t, failureTagged, Finish.sp, state_simp_rules]
  have frame : MemoryFrame [((Finish.sp s).toNat - 16, 16),
      ((Finish.result s).toNat, 68)] s t := by
    intro address outside
    have preserved := kind.frame base s space address outside
    simpa only [Failure.returned, returned_memory] using preserved
  have savedNext : SavedFrom original t := by
    constructor
    · rw [stack]
      exact savedFrom.stack
    · intro reg displacement member
      rw [stack]
      have bounds := saved_bounds reg displacement member
      have physical := space.stackHigh
      have low := space.stackLow
      have apart := space.savedApart
      have same := frame.read (Finish.sp s + BitVec.ofNat 64 displacement) 8 (by bv_omega) (by
        right
        intro span membership
        simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
        rcases membership with rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> bv_omega)
      exact same.trans (savedFrom.words reg displacement member)
    · intro reg low high untouched
      have eight : reg ≠ 8#5 := by bv_omega
      have nine : reg ≠ 9#5 := by bv_omega
      have ten : reg ≠ 10#5 := by bv_omega
      have same : r (.GPR reg) t = r (.GPR reg) s := by
        simp [t, failureTagged, state_simp_rules, eight,
          kind.register base s reg eight nine ten]
      exact same.trans (savedFrom.registers reg low high untouched)
    · intro reg low high
      simpa [t, failureTagged, state_simp_rules] using savedFrom.vectors reg low high
  exact Finish.returned_original original t savedNext
    (by simpa [t, failureTagged, state_simp_rules] using program)
    (by simpa [t, failureTagged, state_simp_rules, failure_error_field] using error)

end SszArm.Serialize.Finish
