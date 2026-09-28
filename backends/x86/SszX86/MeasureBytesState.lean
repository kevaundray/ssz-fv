import SszX86.MeasureOwned
import SszX86.ByteViewList

namespace SszX86.Measure.Bytes
open Kraken.X64.Parser UintCodec SszNative.Limbs

/-- The read-only byte comparison changes only these five registers and flags.
RAX is the original physical byte length throughout both inlined comparisons. -/
def state (s : MachineData) (a c si x y : BitVec 64) (fl : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rcx := UInt64.ofBitVec a
      rdx := UInt64.ofBitVec c
      rsi := UInt64.ofBitVec si
      rdi := UInt64.ofBitVec x
      r8 := UInt64.ofBitVec y}
    status := fl}

def Frame (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧ t.zmms = s.zmms ∧
    ∀ r, r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 →
      t.regs.get64 r = s.regs.get64 r

theorem state_frame (s : MachineData) (a c si x y : BitVec 64) (fl : StatusFlags) :
    Frame s (state s a c si x y fl) := by
  refine ⟨rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [state, Reg64s.get64]

macro "measure_bytes_step " k:num " using " hc:term : tactic => `(tactic|
  (simp (config := {failIfUnchanged := false}) only [state]
   measure_step $k using $hc
   all_goals simp (config := {instances := true, failIfUnchanged := false}) only
     [Width.bytes, Width.bits, BitVec.setWidth_append_eq_right]))

theorem load_cast (v : BitVec 64) :
    BitVec.ofInt 64 (v.toNat : Int) = v := by bv_omega

macro "measure_bytes_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), load_cast])

@[simp] theorem register_nat (n : Nat) :
    ({toBitVec := BitVec.ofNat 64 n} : UInt64) = UInt64.ofNat n := by
  apply UInt64.toBitVec_inj.1
  rfl

@[simp] theorem register_zero : ({toBitVec := 0#64} : UInt64) = 0 := by
  apply UInt64.toBitVec_inj.1
  rfl

@[simp] theorem register_one : ({toBitVec := 1#64} : UInt64) = 1 := by
  apply UInt64.toBitVec_inj.1
  rfl

end SszX86.Measure.Bytes
