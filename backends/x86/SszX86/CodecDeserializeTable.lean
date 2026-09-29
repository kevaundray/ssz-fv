import SszX86.DispatchTable
import SszX86.CodecStorage

set_option autoImplicit false

namespace SszX86.CodecDeserialize
open SszNative

/-- Targets read from all thirteen words of the original deserialize jump table. -/
def dispatchEntry (tag : Nat) : Nat :=
  match tag with
  | 0 => 45 | 1 => 1131 | 2 => 750 | 3 => 824 | 4 => 115
  | 5 => 1192 | 6 => 1240 | 7 => 937 | 8 => 1522 | 9 => 708
  | 10 => 1275 | 11 => 86 | _ => 294

private theorem tag_cases (tag : Nat) (bound : tag < 13) :
    tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨
    tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ tag = 9 ∨ tag = 10 ∨ tag = 11 ∨ tag = 12 := by
  omega

/-- The table relation is the existing actual linked byte relation, not a list
of assumed destinations. Raw descriptor tags require no schema validation. -/
theorem table_load (m : DataMem) (base : Int64) (stored : Dispatch.TableAt m base)
    (tag : Nat) (bound : tag < 13) :
    Mem.loadInt m (Dispatch.tableAddress base + BitVec.ofNat 64 (4 * tag)) 4 =
      some ((106520 + dispatchEntry tag : Nat) : Int) := by
  let bytes := (Dispatch.tableBytes.drop (4 * tag)).take 4
  have length : bytes.length = 4 := by
    rcases tag_cases tag bound with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have loaded := memmove_loadInt_of_lookup m
    (Dispatch.tableAddress base + BitVec.ofNat 64 (4 * tag)) bytes (by
      intro i hi
      have hi4 : i < 4 := by simpa only [length] using hi
      have index : 4 * tag + i < Dispatch.tableBytes.length := by
        have count : Dispatch.tableBytes.length = 52 := by rfl
        rw [count]
        omega
      have byte := stored (4 * tag + i) index
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at byte
      have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases choices with rfl | rfl | rfl | rfl <;>
        rcases tag_cases tag bound with rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [bytes, Dispatch.tableBytes] using byte)
  rw [length] at loaded
  have encoded : Int.ofBytes bytes = ((106520 + dispatchEntry tag : Nat) : Int) := by
    rcases tag_cases tag bound with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [encoded] at loaded
  exact loaded

theorem table_signed (tag : Nat) (bound : tag < 13) :
    (BitVec.ofInt 32 (106520 + dispatchEntry tag : Nat)).signExtend 64 =
      BitVec.ofNat 64 (106520 + dispatchEntry tag) := by
  rcases tag_cases tag bound with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem table_target (base : Int64) (tag : Nat) :
    Dispatch.tableAddress base + BitVec.ofNat 64 (106520 + dispatchEntry tag) =
      (base + Int64.ofNat (dispatchEntry tag)).toBitVec := by
  change (base.toBitVec - 106520) + BitVec.ofNat 64 (106520 + dispatchEntry tag) =
    base.toBitVec + BitVec.ofNat 64 (dispatchEntry tag)
  rw [BitVec.ofNat_add]
  bv_omega

theorem descTag_bound (desc : SszNative.Codec.Desc) : Codec.descTag desc < 13 := by
  cases desc with
  | primitive shape => cases shape <;> decide
  | _ => decide

/-- The actual MOVSLQ observation for every raw recursive descriptor. -/
theorem descriptor_table_load (m : DataMem) (base : Int64)
    (stored : Dispatch.TableAt m base) (desc : SszNative.Codec.Desc) :
    Mem.loadInt m (Dispatch.tableAddress base + BitVec.ofNat 64 (4 * Codec.descTag desc)) 4 =
      some ((106520 + dispatchEntry (Codec.descTag desc) : Nat) : Int) :=
  table_load m base stored _ (descTag_bound desc)

end SszX86.CodecDeserialize
