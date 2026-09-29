import SszX86.CodecEmitImpl
import SszX86.MemmoveMemory

namespace SszX86.CodecEmit

/-- The second emitter table is indexed by the five Seq descriptor tags minus
seven, unlike the first table which is indexed by Value's tag minus two. -/
inductive PartsKind where
  | vector | list | progressiveList | container | progressiveContainer
  deriving DecidableEq

def PartsKind.index : PartsKind → Nat
  | .vector => 0
  | .list => 1
  | .progressiveList => 2
  | .container => 3
  | .progressiveContainer => 4

def PartsKind.entry : PartsKind → Nat
  | .vector | .list => 337
  | .progressiveList => 1191
  | .container => 1216
  | .progressiveContainer => 1184

theorem parts_table_load (m : DataMem) (base : Int64) (h : Table1At m base)
    (kind : PartsKind) :
    Mem.loadInt m (table1Address base + BitVec.ofNat 64 (4 * kind.index)) 4 =
      some ((92784 + kind.entry : Nat) : Int) := by
  let bytes := (table1Bytes.drop (4 * kind.index)).take 4
  have length : bytes.length = 4 := by cases kind <;> decide
  have loaded := memmove_loadInt_of_lookup m
    (table1Address base + BitVec.ofNat 64 (4 * kind.index)) bytes (by
      intro i hi
      have hi4 : i < 4 := by simpa only [length] using hi
      have index : 4 * kind.index + i < table1Bytes.length := by
        cases kind <;> simp only [PartsKind.index, table1Bytes, List.length_cons, List.length_nil] <;> omega
      have byte := h (4 * kind.index + i) index
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at byte
      have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases choices with rfl | rfl | rfl | rfl <;>
        cases kind <;> simpa [bytes, PartsKind.index, table1Bytes] using byte)
  rw [length] at loaded
  have encoded : Int.ofBytes bytes = ((92784 + kind.entry : Nat) : Int) := by
    cases kind <;> decide
  rw [encoded] at loaded
  exact loaded

theorem parts_table_signed (kind : PartsKind) :
    (BitVec.ofInt 32 (92784 + kind.entry : Nat)).signExtend 64 =
      BitVec.ofNat 64 (92784 + kind.entry) := by
  cases kind <;> decide

theorem parts_table_target (base : Int64) (kind : PartsKind) :
    table1Address base + BitVec.ofNat 64 (92784 + kind.entry) =
      (base + Int64.ofNat kind.entry).toBitVec := by
  change (base.toBitVec + BitVec.ofInt 64 (-92784)) +
    BitVec.ofNat 64 (92784 + kind.entry) = base.toBitVec + BitVec.ofNat 64 kind.entry
  cases kind <;> simp only [PartsKind.entry] <;> bv_omega

end SszX86.CodecEmit
