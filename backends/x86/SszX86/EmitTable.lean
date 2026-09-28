import SszX86.EmitCore
import SszX86.MemmoveMemory

namespace SszX86.Emit

/-- These are Value tags minus two, not descriptor discriminants. -/
inductive TableKind where
  | bytes | bits | seq | union
  deriving DecidableEq

def TableKind.index : TableKind → Nat
  | .bytes => 0 | .bits => 1 | .seq => 2 | .union => 3

def TableKind.entry : TableKind → Nat
  | .bytes => 256 | .bits => 414 | .seq => 307 | .union => 347

theorem table_load (m : DataMem) (base : Int64) (h : TableAt m base) (kind : TableKind) :
    Mem.loadInt m (tableAddress base + BitVec.ofNat 64 (4 * kind.index)) 4 =
      some ((92800 + kind.entry : Nat) : Int) := by
  let bytes := (tableBytes.drop (4 * kind.index)).take 4
  have length : bytes.length = 4 := by cases kind <;> decide
  have loaded := memmove_loadInt_of_lookup m
    (tableAddress base + BitVec.ofNat 64 (4 * kind.index)) bytes (by
      intro i hi
      have hi4 : i < 4 := by simpa only [length] using hi
      have index : 4 * kind.index + i < tableBytes.length := by
        cases kind <;> simp only [TableKind.index, tableBytes, List.length_cons, List.length_nil] <;> omega
      have byte := h (4 * kind.index + i) index
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at byte
      have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases choices with rfl | rfl | rfl | rfl <;>
        cases kind <;> simpa [bytes, TableKind.index, tableBytes] using byte)
  rw [length] at loaded
  have encoded : Int.ofBytes bytes = ((92800 + kind.entry : Nat) : Int) := by
    cases kind <;> decide
  rw [encoded] at loaded
  exact loaded

theorem table_signed (kind : TableKind) :
    (BitVec.ofInt 32 (92800 + kind.entry : Nat)).signExtend 64 =
      BitVec.ofNat 64 (92800 + kind.entry) := by
  cases kind <;> decide

theorem table_target (base : Int64) (kind : TableKind) :
    tableAddress base + BitVec.ofNat 64 (92800 + kind.entry) =
      (base + Int64.ofNat kind.entry).toBitVec := by
  change (base.toBitVec - 92800) + BitVec.ofNat 64 (92800 + kind.entry) =
    base.toBitVec + BitVec.ofNat 64 kind.entry
  cases kind <;> simp only [TableKind.entry] <;> bv_omega

end SszX86.Emit
