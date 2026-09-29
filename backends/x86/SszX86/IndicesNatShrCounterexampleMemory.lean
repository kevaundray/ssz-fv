import SszX86.BoolMemory
import SszNatShift

namespace SszX86.IndicesNatShr.Counterexample

open SszNative BoolCodec

/-- The borrowed two-limb operand is deliberately not restricted to one word. -/
def operand : NatOperand := .large 8192#64 [5#64, 2#64]

theorem source_bit_length : NatShift.bitLength operand = 66 := by decide

theorem source_result :
    NatShift.shr operand 64 0 0 0 = NatArithmetic.unchanged 0 (.ok (.small 2#64)) := by
  decide

theorem source_value : (NatOperand.small 2#64).value = 2 := by decide

/-- Only original mapped loads are assumed. Output padding remains opaque. -/
structure InitialMemory (m : DataMem) : Prop where
  low : Mem.loadInt m 8192#64 8 = some 5
  high : Mem.loadInt m 8200#64 8 = some 2
  returnAddress : Mem.loadInt m 16384#64 8 = some 32768
  scratch0 : ∃ old, Mem.loadInt m 16368#64 8 = some old
  scratch1 : ∃ old, Mem.loadInt m 16376#64 8 = some old
  outputPointer : ∃ old, Mem.loadInt m 4096#64 8 = some old
  outputPayload : ∃ old, Mem.loadInt m 4104#64 8 = some old
  outputTag : ∃ old, Mem.loadInt m 4160#64 4 = some old

/-- Literal-address version of the existing byte-disjoint store rule. -/
theorem load_store_separate (m : DataMem) (a b n k : Nat) (v : Int)
    (ha : a + n < 2^64) (hb : b + k < 2^64)
    (h : a + n ≤ b ∨ b + k ≤ a) :
    Mem.loadInt (Mem.storeInt m (BitVec.ofNat 64 b) k v) (BitVec.ofNat 64 a) n =
      Mem.loadInt m (BitVec.ofNat 64 a) n := by
  apply load_store_disjoint
  intro i hi j hj he
  have hai : a + i < 2^64 := by omega
  have hbj : b + j < 2^64 := by omega
  have he' := congrArg BitVec.toNat he
  simp only [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hai,
    Nat.mod_eq_of_lt hbj] at he'
  omega

def scratchMem (m : DataMem) : DataMem :=
  Mem.storeInt (Mem.storeInt m 16368#64 8 0) 16376#64 8 12288

def returnedMem (m : DataMem) : DataMem :=
  Mem.storeInt (Mem.storeInt (Mem.storeInt (scratchMem m) 4096#64 8 0)
    4104#64 8 7) 4160#64 4 0

macro "shr_counter_memory" : tactic => `(tactic|
  simp (disch := decide) [scratchMem, returnedMem, load_store_separate,
    load_store_same, Int.take])

theorem scratch_low (m : DataMem) (h : InitialMemory m) :
    Mem.loadInt (scratchMem m) 8192#64 8 = some 5 := by
  simpa (disch := decide) [scratchMem, load_store_separate] using h.low

theorem scratch_high (m : DataMem) (h : InitialMemory m) :
    Mem.loadInt (scratchMem m) 8200#64 8 = some 2 := by
  simpa (disch := decide) [scratchMem, load_store_separate] using h.high

theorem scratch_saved0 (m : DataMem) :
    Mem.loadInt (scratchMem m) 16368#64 8 = some 0 := by shr_counter_memory

theorem scratch_saved1 (m : DataMem) :
    Mem.loadInt (scratchMem m) 16376#64 8 = some 12288 := by shr_counter_memory

theorem returned_address (m : DataMem) (h : InitialMemory m) :
    Mem.loadInt (returnedMem m) 16384#64 8 = some 32768 := by
  simpa (disch := decide) [returnedMem, scratchMem, load_store_separate] using h.returnAddress

theorem returned_pointer (m : DataMem) :
    Mem.loadInt (returnedMem m) 4096#64 8 = some 0 := by shr_counter_memory

theorem returned_payload (m : DataMem) :
    Mem.loadInt (returnedMem m) 4104#64 8 = some 7 := by shr_counter_memory

theorem returned_tag (m : DataMem) :
    Mem.loadInt (returnedMem m) 4160#64 4 = some 0 := by shr_counter_memory

/-- The eight hypotheses above are simultaneously satisfiable, over any ambient memory. -/
def witnessMem (m : DataMem) : DataMem :=
  let m := Mem.storeInt m 8192#64 8 5
  let m := Mem.storeInt m 8200#64 8 2
  let m := Mem.storeInt m 16384#64 8 32768
  let m := Mem.storeInt m 16368#64 8 0
  let m := Mem.storeInt m 16376#64 8 0
  let m := Mem.storeInt m 4096#64 8 0
  let m := Mem.storeInt m 4104#64 8 0
  Mem.storeInt m 4160#64 4 0

theorem witness_initial (m : DataMem) : InitialMemory (witnessMem m) := by
  constructor
  all_goals simp (disch := decide) [witnessMem, load_store_separate,
    load_store_same, Int.take]

end SszX86.IndicesNatShr.Counterexample
