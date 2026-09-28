import SszX86.DispatchImpl
import SszX86.MemmoveMemory

namespace SszX86.Dispatch

/-- Each four-byte load is obtained from the actual linked byte array. The
subsequent MOVSLQ still performs the ISA's signed extension. -/
theorem table_load (m : DataMem) (base : Int64) (h : TableAt m base) (kind : Kind) :
    Mem.loadInt m (tableAddress base + BitVec.ofNat 64 (4 * kind.tag)) 4 =
      some ((106520 + kind.entry : Nat) : Int) := by
  let bytes := (tableBytes.drop (4 * kind.tag)).take 4
  have length : bytes.length = 4 := by cases kind <;> decide
  have loaded := memmove_loadInt_of_lookup m
    (tableAddress base + BitVec.ofNat 64 (4 * kind.tag)) bytes (by
      intro i hi
      have hi4 : i < 4 := by simpa only [length] using hi
      have index : 4 * kind.tag + i < tableBytes.length := by
        cases kind <;> simp only [Kind.tag, tableBytes, List.length_cons, List.length_nil] <;> omega
      have byte := h (4 * kind.tag + i) index
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at byte
      have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases choices with rfl | rfl | rfl | rfl <;>
        cases kind <;> simpa [bytes, Kind.tag, tableBytes] using byte)
  rw [length] at loaded
  have encoded : Int.ofBytes bytes = ((106520 + kind.entry : Nat) : Int) := by
    cases kind <;> decide
  rw [encoded] at loaded
  exact loaded

theorem table_signed (kind : Kind) :
    (BitVec.ofInt 32 (106520 + kind.entry : Nat)).signExtend 64 =
      BitVec.ofNat 64 (106520 + kind.entry) := by
  cases kind <;> decide

theorem table_target (base : Int64) (kind : Kind) :
    tableAddress base + BitVec.ofNat 64 (106520 + kind.entry) =
      (base + Int64.ofNat kind.entry).toBitVec := by
  change (base.toBitVec - 106520) + BitVec.ofNat 64 (106520 + kind.entry) =
    base.toBitVec + BitVec.ofNat 64 kind.entry
  cases kind <;> simp only [Kind.entry] <;> bv_omega

end SszX86.Dispatch
