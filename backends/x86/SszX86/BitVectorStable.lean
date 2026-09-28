import SszX86.BitVectorFrame
import SszX86.BitVectorMappingClosure

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- Coarse read-only preservation is separate from the exact final write frame.
The latter never grants permission to reservation alignment padding. -/
def StableFrame (s : MachineData) (address capacity used : BitVec 64) (m : DataMem) : Prop :=
  RegionsFrame s.dmem m
    [(s.regs.rdi.toNat, 80), (workStart s, workSize),
      (s.regs.rbx.toNat + 16, 8), (address.toNat + used.toNat, capacity.toNat - used.toNat)]

theorem Protected.subrange {s : MachineData} {address capacity used : BitVec 64}
    {p n : Nat} (owned : Protected s address capacity used p n)
    (off count : Nat) (inside : off + count ≤ n) :
    Protected s address capacity used (p + off) count := by
  rcases owned with ⟨bound, output, work, cursor, arena⟩
  constructor <;> unfold Body.Apart at * <;> omega

theorem Protected.advance {s : MachineData} {address capacity used next : BitVec 64}
    {p n : Nat} (owned : Protected s address capacity used p n)
    (progress : used.toNat ≤ next.toNat) (bound : next.toNat ≤ capacity.toNat) :
    Protected s address capacity next p n := by
  refine ⟨owned.bound, owned.output, owned.work, owned.cursor, ?_⟩
  have apart := owned.arena
  unfold Body.Apart at *
  omega

theorem StableFrame.load {s : MachineData} {address capacity used : BitVec 64} {m : DataMem}
    (frame : StableFrame s address capacity used m) {p n : Nat}
    (owned : Protected s address capacity used p n) :
    Mem.loadInt m (BitVec.ofNat 64 p) n = Mem.loadInt s.dmem (BitVec.ofNat 64 p) n := by
  apply RegionsFrame.load frame p n owned.bound
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact owned.output
  · exact owned.work
  · exact owned.cursor
  · exact owned.arena

theorem StableFrame.width {s : MachineData} {address capacity used : BitVec 64} {m : DataMem}
    (frame : StableFrame s address capacity used m) {p n : Nat}
    (owned : Protected s address capacity used p n) :
    widthLoad m p n = widthLoad s.dmem p n := by
  unfold widthLoad
  rw [frame.load owned]

theorem StableFrame.operand {s : MachineData} {address capacity used : BitVec 64} {m : DataMem}
    (frame : StableFrame s address capacity used m) (operand : NatOperand)
    (stored : operand.At (widthLoad s.dmem))
    (owned : OperandProtected s address capacity used operand) : operand.At (widthLoad m) := by
  cases operand with
  | small limb => trivial
  | large pointer words =>
    obtain ⟨positive, aligned, bound, limbs⟩ := stored
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    rw [frame.width (owned.subrange (8 * i.val) 8 (by have := i.isLt; omega))]
    exact limbs i

theorem StableFrame.saved_region (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    Protected s address capacity used (s.regs.rsp.toNat + 312) 56 := by
  refine ⟨owned.stack_bound, ?_, ?_, ?_, ?_⟩
  · have apart := owned.output_saved
    unfold Body.Apart at *
    omega
  · unfold Body.Apart workStart workSize
    have lower := owned.stack_low
    omega
  · have apart := owned.cursor_saved
    unfold Body.Apart at *
    omega
  · have apart := owned.arena_saved
    unfold Body.Apart at *
    omega

theorem StableFrame.header_region (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    Protected s address capacity used s.regs.rbx.toNat 16 := by
  refine ⟨by have := owned.header_bound; omega, ?_, ?_, ?_, ?_⟩
  · have apart := owned.header_output
    unfold Body.Apart at *
    omega
  · have apart := owned.header_work
    unfold Body.Apart at *
    omega
  · unfold Body.Apart
    omega
  · have apart := owned.arena_header
    unfold Body.Apart at *
    omega

end SszX86.BitVector
