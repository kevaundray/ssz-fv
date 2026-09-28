import SszArm.BitVectorPadding

namespace SszArm.BitVector.Padding

open Delimited (MemoryFrame)

theorem zero16 (s : ArmState) (base : BitVec 64) (space : Space s) :
    read_mem_bytes 8 (r (.GPR 23#5) s + 16#64) (result s base) = 0#64 := by
  obtain ⟨stack, output, separate⟩ := space
  padding_expand
  padding_reads

theorem zero24 (s : ArmState) (base : BitVec 64) (space : Space s) :
    read_mem_bytes 8 (r (.GPR 23#5) s + 24#64) (result s base) = 0#64 := by
  obtain ⟨stack, output, separate⟩ := space
  padding_expand
  padding_reads

theorem zero32 (s : ArmState) (base : BitVec 64) (space : Space s) :
    read_mem_bytes 8 (r (.GPR 23#5) s + 32#64) (result s base) = 0#64 := by
  obtain ⟨stack, output, separate⟩ := space
  padding_expand
  padding_reads

theorem zero40 (s : ArmState) (base : BitVec 64) (space : Space s) :
    read_mem_bytes 8 (r (.GPR 23#5) s + 40#64) (result s base) = 0#64 := by
  obtain ⟨stack, output, separate⟩ := space
  padding_expand
  padding_reads

theorem zero48 (s : ArmState) (base : BitVec 64) (space : Space s) :
    read_mem_bytes 8 (r (.GPR 23#5) s + 48#64) (result s base) = 0#64 := by
  obtain ⟨stack, output, separate⟩ := space
  padding_expand
  padding_reads

theorem zero56 (s : ArmState) (base : BitVec 64) (space : Space s) :
    read_mem_bytes 8 (r (.GPR 23#5) s + 56#64) (result s base) = 0#64 := by
  obtain ⟨stack, output, separate⟩ := space
  padding_expand
  padding_reads

theorem zero64 (s : ArmState) (base : BitVec 64) (space : Space s) :
    read_mem_bytes 8 (r (.GPR 23#5) s + 64#64) (result s base) = 0#64 := by
  obtain ⟨stack, output, separate⟩ := space
  padding_expand
  padding_reads

/-- Text length plus both machine words of each of the three zero Nats. -/
def ZeroOutput (s t : ArmState) : Prop :=
  ∀ offset ∈ [16, 24, 32, 40, 48, 56, 64],
    read_mem_bytes 8 (r (.GPR 23#5) s + BitVec.ofNat 64 offset) t = 0#64

theorem zero_output (s : ArmState) (base : BitVec 64) (space : Space s) :
    ZeroOutput s (result s base) := by
  intro offset member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact zero16 s base space
  · exact zero24 s base space
  · exact zero32 s base space
  · exact zero40 s base space
  · exact zero48 s base space
  · exact zero56 s base space
  · exact zero64 s base space

structure Terminal (s t : ArmState) (base : BitVec 64) : Prop where
  pc : read_pc t = base + 8224#64
  reason : r (.GPR 8#5) t = 15#64
  zeroOutput : ZeroOutput s t
  registers : ∀ reg : BitVec 5, reg ≠ 8#5 → r (.GPR reg) t = r (.GPR reg) s
  program : t.program = s.program
  error : read_err t = read_err s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  frame : MemoryFrame (writes s) s t

theorem terminal (s : ArmState) (base : BitVec 64) (space : Space s) :
    Terminal s (result s base) base := by
  exact ⟨final_pc s base, final_reason s base, zero_output s base space,
    final_register s base, final_program s base, final_error s base,
    final_vector s base, final_frame s base space⟩

/-- No final state, desired store, or whole-path fuel is assumed. -/
theorem actual_terminal (s : ArmState) (base : BitVec 64)
    (space : Space s) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6052#64) :
    ∃ fuel, Terminal s (run fuel s) base := by
  refine ⟨48, ?_⟩
  rw [executes s base space code error aligned pc]
  exact terminal s base space

end SszArm.BitVector.Padding
