import SszX86.MeasureCore
import SszX86.MemmoveMemory

namespace SszX86.Measure
open SszNative.Serialize

theorem descriptor_table_index (desc : Desc) : descTag desc < 7 := by
  cases desc <;> dsimp only [descTag, Emit.descTag] <;> decide

/-- Primitive descriptor tags select only the first seven genuine table slots. -/
theorem table_load (m : DataMem) (base : Int64) (h : TableAt m base) (desc : Desc) :
    Mem.loadInt m (tableAddress base + BitVec.ofNat 64 (4 * descTag desc)) 4 =
      some ((89316 + bodyEntry desc : Nat) : Int) := by
  let bytes := (tableBytes.drop (4 * descTag desc)).take 4
  have length : bytes.length = 4 := by
    cases desc <;> dsimp only [bytes, descTag, Emit.descTag] <;> decide
  have loaded := memmove_loadInt_of_lookup m
    (tableAddress base + BitVec.ofNat 64 (4 * descTag desc)) bytes (by
      intro i hi
      have hi4 : i < 4 := by simpa only [length] using hi
      have index : 4 * descTag desc + i < tableBytes.length := by
        have tag := descriptor_table_index desc
        have count : tableBytes.length = 52 := by decide
        rw [count]
        omega
      have byte := h (4 * descTag desc + i) index
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at byte
      have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases choices with rfl | rfl | rfl | rfl <;>
        cases desc <;> simpa [bytes, descTag, Emit.descTag, tableBytes] using byte)
  rw [length] at loaded
  have encoded : Int.ofBytes bytes = ((89316 + bodyEntry desc : Nat) : Int) := by
    cases desc <;> dsimp only [bytes, descTag, Emit.descTag, bodyEntry] <;> decide
  rw [encoded] at loaded
  exact loaded

theorem table_signed (desc : Desc) :
    (BitVec.ofInt 32 (89316 + bodyEntry desc : Nat)).signExtend 64 =
      BitVec.ofNat 64 (89316 + bodyEntry desc) := by
  cases desc <;> dsimp only [bodyEntry] <;> decide

theorem table_target (base : Int64) (desc : Desc) :
    tableAddress base + BitVec.ofNat 64 (89316 + bodyEntry desc) =
      (base + Int64.ofNat (bodyEntry desc)).toBitVec := by
  change (base.toBitVec - 89316) + BitVec.ofNat 64 (89316 + bodyEntry desc) =
    base.toBitVec + BitVec.ofNat 64 (bodyEntry desc)
  cases desc <;> simp only [bodyEntry] <;> bv_omega

end SszX86.Measure
