import SszArm.BitVectorPaddingMemory
import SszArm.BitVectorErrorExec

namespace SszArm.BitVector.Padding

open Delimited (MemoryFrame)
open UintCodec (widthLoad)

/-- The shared error tail writes its status and two one-valued tags. -/
def completed (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 4732#64) (w (.GPR 9#5) 1#64
    (write_mem_bytes 8 (r (.GPR 23#5) s + 8#64) 1#64
      (write_mem_bytes 8 (r (.GPR 23#5) s) 1#64
        (write_mem_bytes 4 (r (.GPR 23#5) s + 72#64) 15#32 (result s base)))))

private theorem tail_image (s : ArmState) (base : BitVec 64) (space : Space s) :
    ErrorTail.Tail.padding.result (result s base) base = completed s base := by
  have output := space.output
  have physical : (r (.GPR 23#5) s).toNat + 16 ≤ 2^64 := by omega
  simp (config := {decide := true, instances := true}) only
    [ErrorTail.Tail.result, ErrorTail.Tail.stop, final_register s base 23#5 (by decide),
     final_reason, show (15#64).setWidth 32 = 15#32 by decide, completed]
  rw [UintCodec.Tail.write_pair_words _ _ _ _ physical]

theorem completed_run (s : ArmState) (base : BitVec 64)
    (space : Space s) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6052#64) :
    run 52 s = completed s base := by
  have first := executes s base space code error aligned pc
  have tailAligned : CheckSPAlignment (result s base) := by
    simpa (config := {decide := true, instances := true}) only
      [CheckSPAlignment, state_simp_rules, final_register s base 31#5 (by decide)] using aligned
  have last := ErrorTail.executes .padding (result s base) base
    (by simpa only [CodeAt, final_program] using code)
    (by simpa only [final_error] using error) tailAligned
    (by simpa only [ErrorTail.Tail.start] using final_pc s base)
  change run 4 (result s base) = _ at last
  rw [tail_image s base space] at last
  change run (48 + 4) s = _
  rw [run_plus, first, last]

@[simp] theorem completed_pc (s : ArmState) (base : BitVec 64) :
    read_pc (completed s base) = base + 4732#64 := by
  simp [completed, state_simp_rules]

theorem completed_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (h8 : reg ≠ 8#5) (h9 : reg ≠ 9#5) :
    r (.GPR reg) (completed s base) = r (.GPR reg) s := by
  simp [completed, state_simp_rules, h9, final_register s base reg h8]

@[simp] theorem completed_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (completed s base) = r (.GPR 31#5) s :=
  completed_register s base 31#5 (by decide) (by decide)

@[simp] theorem completed_program (s : ArmState) (base : BitVec 64) :
    (completed s base).program = s.program := by
  simp [completed, state_simp_rules]

@[simp] theorem completed_error (s : ArmState) (base : BitVec 64) :
    read_err (completed s base) = read_err s := by
  have kept : r .ERR (result s base) = r .ERR s := final_error s base
  simp (config := {decide := true, instances := true}) [completed, state_simp_rules, kept]

@[simp] theorem completed_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (completed s base) = r (.SFP reg) s := by
  simp [completed, state_simp_rules]

theorem completed_frame (s : ArmState) (base : BitVec 64) (space : Space s) :
    MemoryFrame (writes s) s (completed s base) := by
  have output := space.output
  intro address outside
  have out := outside ((r (.GPR 23#5) s).toNat, 80) (by simp [writes])
  have kept := final_frame s base space address outside
  simp only [completed, ArmState.mem_w_eq_mem]
  simp (disch := padding_side) [BoolCodec.write_mem_bytes_frame, kept]

private theorem completed_zero (s : ArmState) (base : BitVec 64) (space : Space s)
    (offset : Nat) (member : offset ∈ [16, 24, 32, 40, 48, 56, 64]) :
    read_mem_bytes 8 (r (.GPR 23#5) s + BitVec.ofNat 64 offset) (completed s base) = 0#64 := by
  have output := space.output
  have zero := zero_output s base space offset member
  have bounds : 16 ≤ offset ∧ offset + 8 ≤ 72 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [completed]
  padding_reads
  exact zero

private theorem completed_tag (s : ArmState) (base : BitVec 64) (space : Space s) :
    read_mem_bytes 8 (r (.GPR 23#5) s) (completed s base) = 1#64 := by
  have output := space.output
  simp only [completed]
  padding_reads

private theorem completed_text (s : ArmState) (base : BitVec 64) (space : Space s) :
    read_mem_bytes 8 (r (.GPR 23#5) s + 8#64) (completed s base) = 1#64 := by
  have output := space.output
  simp only [completed]
  padding_reads

private theorem completed_reason (s : ArmState) (base : BitVec 64) (space : Space s) :
    read_mem_bytes 4 (r (.GPR 23#5) s + 72#64) (completed s base) = 15#32 := by
  have output := space.output
  simp only [completed]
  padding_reads

private theorem completed_zero_load (s : ArmState) (base : BitVec 64) (space : Space s)
    (offset : Nat) (member : offset ∈ [16, 24, 32, 40, 48, 56, 64]) :
    widthLoad (completed s base) ((r (.GPR 23#5) s).toNat + offset) 8 = some 0 := by
  simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    completed_zero s base space offset member, BitVec.toNat_ofNat]

private theorem completed_nat (s : ArmState) (base : BitVec 64) (space : Space s)
    (offset : Nat) (member : offset ∈ [24, 40, 56]) :
    SszNative.NatMemory.At (widthLoad (completed s base))
      ((r (.GPR 23#5) s).toNat + offset) 0 := by
  have first : offset ∈ [16, 24, 32, 40, 48, 56, 64] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with rfl | rfl | rfl <;> simp
  have second : offset + 8 ∈ [16, 24, 32, 40, 48, 56, 64] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with rfl | rfl | rfl <;> simp
  apply Or.inl
  refine ⟨⟨completed_zero_load s base space offset first, ?_⟩, by decide⟩
  simpa only [Nat.add_assoc] using completed_zero_load s base space (offset + 8) second

/-- Padding errors do not inspect the input bytes or impose Nat canonicality. -/
theorem completed_result (s : ArmState) (base : BitVec 64) (space : Space s)
    (source : Nat) (data : Ssz.Bytes) :
    SszNative.BitVector.ResultAt (widthLoad (completed s base))
      (r (.GPR 23#5) s).toNat source data (.error .paddingBits) := by
  change SszNative.UintCodec.errorAt _ _ 15 0 0
  refine ⟨?_, ?_, completed_zero_load s base space 16 (by decide),
    completed_nat s base space 24 (by decide), completed_nat s base space 40 (by decide),
    completed_nat s base space 56 (by decide), ?_⟩
  · simp only [widthLoad, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      completed_tag s base space, BitVec.toNat_ofNat]
  · simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      completed_text s base space, BitVec.toNat_ofNat]
  · simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      completed_reason s base space, BitVec.toNat_ofNat]

structure Correct (s t : ArmState) (base : BitVec 64) (source : Nat) (data : Ssz.Bytes) : Prop where
  pc : read_pc t = base + 4732#64
  result : SszNative.BitVector.ResultAt (widthLoad t) (r (.GPR 23#5) s).toNat
    source data (.error .paddingBits)
  frame : MemoryFrame (writes s) s t
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  error : read_err t = read_err s
  program : t.program = s.program
  registers : ∀ reg : BitVec 5, reg ≠ 8#5 → reg ≠ 9#5 → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem correct (s : ArmState) (base : BitVec 64) (space : Space s)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 6052#64) (source : Nat) (data : Ssz.Bytes) :
    ∃ fuel, Correct s (run fuel s) base source data := by
  refine ⟨52, ?_⟩
  rw [completed_run s base space code error aligned pc]
  exact ⟨completed_pc s base, completed_result s base space source data,
    completed_frame s base space, completed_sp s base, completed_error s base,
    completed_program s base, completed_register s base, completed_vector s base⟩

end SszArm.BitVector.Padding
