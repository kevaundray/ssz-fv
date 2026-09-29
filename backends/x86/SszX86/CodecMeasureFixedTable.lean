import SszX86.CodecMeasureFixedImpl
import SszX86.MemmoveMemory

namespace SszX86.CodecMeasureFixed

/-- The actual twelve-slot dispatch reached after the PC20 unsigned tag guard. -/
def tableEntry (tag : Nat) : Nat := tableDestinations[tag]?.getD 0

private theorem tag_cases (tag : Nat) (bound : tag < 12) :
    tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨
    tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ tag = 9 ∨ tag = 10 ∨ tag = 11 := by omega

/-- No semantic constructor is assigned an invented direct branch: the actual
signed word is read from the linked table, including all recursive destinations. -/
theorem table_load (m : DataMem) (base : Int64) (stored : TableAt m base)
    (tag : Nat) (bound : tag < 12) :
    Mem.loadInt m (tableAddress base + BitVec.ofNat 64 (4 * tag)) 4 =
      some ((116208 + tableEntry tag : Nat) : Int) := by
  let bytes := (tableBytes.drop (4 * tag)).take 4
  have length : bytes.length = 4 := by
    rcases tag_cases tag bound with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have loaded := memmove_loadInt_of_lookup m
    (tableAddress base + BitVec.ofNat 64 (4 * tag)) bytes (by
      intro i hi
      have hi4 : i < 4 := by simpa only [length] using hi
      have index : 4 * tag + i < tableBytes.length := by
        have count : tableBytes.length = 48 := by rfl
        rw [count]
        omega
      have byte := stored (4 * tag + i) index
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at byte
      have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases choices with rfl | rfl | rfl | rfl <;>
        rcases tag_cases tag bound with rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [bytes, tableBytes] using byte)
  rw [length] at loaded
  have encoded : Int.ofBytes bytes = ((116208 + tableEntry tag : Nat) : Int) := by
    rcases tag_cases tag bound with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [encoded] at loaded
  exact loaded

theorem table_signed (tag : Nat) (bound : tag < 12) :
    (BitVec.ofInt 32 (116208 + tableEntry tag : Nat)).signExtend 64 =
      BitVec.ofNat 64 (116208 + tableEntry tag) := by
  rcases tag_cases tag bound with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem table_target (base : Int64) (tag : Nat) :
    tableAddress base + BitVec.ofNat 64 (116208 + tableEntry tag) =
      (base + Int64.ofNat (tableEntry tag)).toBitVec := by
  generalize tableEntry tag = destination
  change (base.toBitVec + BitVec.ofInt 64 (-116208)) +
      BitVec.ofNat 64 (116208 + destination) =
    base.toBitVec + BitVec.ofNat 64 destination
  rw [BitVec.ofNat_add]
  bv_omega

end SszX86.CodecMeasureFixed
