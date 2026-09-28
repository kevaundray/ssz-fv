import SszX86.EmitSetup
import SszX86.EmitJump

namespace SszX86.Emit
open BoolCodec

def descriptorTested (s : MachineData) (af : Bool) : MachineData :=
  {s with status :=
    StatusFlags.from_result s.regs.rax.toBitVec {cf := false, af, of := false}}

def descriptorCompared (s : MachineData) : MachineData :=
  {s with status := Memcmp.subFlags (s.regs.rax.toBitVec.take 32) 1#32}

/-- The real TEST/JE distinguishes Bool before consulting the value table. -/
theorem descriptor_zero_branch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ af, Eventually (step e) P
      (descriptorTested s af, if s.regs.rax.toBitVec == 0#64 then base + 190 else base + 41)) :
    Eventually (step e) P (s, base + 32) := by
  have target := hc.targets ("emit_u190", 190) (by decide)
  have branch (af : Bool) : Eventually (step e) P (descriptorTested s af, base + 35) := by
    have hnext := next af
    emit_step 14 using hc
    simp only [target]
    split <;> rename_i condition
    all_goals simp_all (config := {instances := true})
      [descriptorTested, StatusFlags.from_result, Effects.All]
  emit_step 13 using hc
  exact ⟨branch false, branch true⟩

private theorem sub_zero_iff {w : Nat} (a b : BitVec w) :
    a - b = 0#w ↔ a = b := by
  constructor
  · intro h
    have sum := congrArg (fun v : BitVec w => v + b) h
    simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using sum
  · rintro rfl
    exact BitVec.sub_self _

/-- UInt is selected by its descriptor before any indirect table lookup. -/
theorem descriptor_one_branch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      (descriptorCompared s, if s.regs.rax.toBitVec.take 32 == 1#32 then base + 50 else base + 228)) :
    Eventually (step e) P (s, base + 41) := by
  have target := hc.targets ("emit_u228", 228) (by decide)
  have branch : Eventually (step e) P (descriptorCompared s, base + 44) := by
    emit_step 16 using hc
    simp only [descriptorCompared, Memcmp.subFlags, StatusFlags.from_result] at *
    simp only [target]
    by_cases equal : s.regs.rax.toBitVec.take 32 = 1#32
    · simpa [equal, Effects.All] using next
    · have nonzero : s.regs.rax.toBitVec.take 32 - 1#32 ≠ 0#32 :=
        fun zero => equal ((sub_zero_iff _ _).mp zero)
      simpa [equal, nonzero, Effects.All] using next
  emit_step 15 using hc
  simpa [descriptorCompared, Memcmp.subFlags, BitVec.take, BitVec.signed] using branch

def indexedState (s : MachineData) (kind : TableKind) : MachineData :=
  {s with
    regs := {s.regs with rcx := UInt64.ofNat kind.index}
    status := Memcmp.subFlags (BitVec.ofNat 32 kind.index) 3#32}

/-- Actual ADD -2/CMP3/JA guards the table index computed from Value's tag. -/
theorem value_index_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (kind : TableKind) (P : MachineState → Prop)
    (tag : s.regs.rcx = UInt64.ofNat (kind.index + 2))
    (next : Eventually (step e) P (indexedState s kind, base + 240)) :
    Eventually (step e) P (s, base + 228) := by
  have borrow0 : (4294967293#32).unsigned ≠ (0#32).unsigned - (3#32).unsigned := by decide
  have borrow1 : (4294967294#32).unsigned ≠ (1#32).unsigned - (3#32).unsigned := by decide
  have borrow2 : (4294967295#32).unsigned ≠ (2#32).unsigned - (3#32).unsigned := by decide
  cases kind <;>
    emit_step 50 using hc <;>
    simp only [tag, TableKind.index] <;>
    emit_step 51 using hc <;>
    emit_step 52 using hc <;>
    simp_all [indexedState, TableKind.index, Memcmp.subFlags, StatusFlags.from_result,
      BitVec.take, BitVec.signed, Effects.All]

end SszX86.Emit
