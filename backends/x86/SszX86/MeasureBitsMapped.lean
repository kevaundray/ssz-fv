import SszX86.MeasureBitsMemory
import SszX86.MeasureBitsListModel

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

/-- Actual stores never remove a mapped byte. This is independent of readonly
preservation: scratch writes may change byte values while retaining ownership. -/
def MappedExtension (before after : DataMem) : Prop :=
  ∀ pointer byteCount, Large.Mapped before pointer byteCount → Large.Mapped after pointer byteCount

theorem mapped_extension_refl (m : DataMem) : MappedExtension m m := by
  intro pointer byteCount hm
  exact hm

theorem mapped_extension_trans (a b c : DataMem)
    (first : MappedExtension a b) (second : MappedExtension b c) : MappedExtension a c := by
  intro pointer byteCount hm
  exact second pointer byteCount (first pointer byteCount hm)

theorem mapped_extension_store (m : DataMem) (pointer : BitVec 64) (byteCount : Nat) (v : Int) :
    MappedExtension m (Mem.storeInt m pointer byteCount v) := by
  intro dst n hm
  exact Large.mapped_store _ _ _ _ _ _ hm

theorem disjoint_apart (p q : BitVec 64) (n k : Nat)
    (apart : Large.Disjoint p q n k) : Body.Apart p.toNat n q.toNat k := by
  by_cases separated : Body.Apart p.toNat n q.toNat k
  · exact separated
  have overlap := separated
  exfalso
  simp only [Body.Apart, not_or] at overlap
  let a := max p.toNat q.toNat
  have pa : p.toNat ≤ a := Nat.le_max_left _ _
  have qa : q.toNat ≤ a := Nat.le_max_right _ _
  have pi : a - p.toNat < n := by dsimp only [a]; omega
  have qi : a - q.toNat < k := by dsimp only [a]; omega
  apply apart (a - p.toNat) pi (a - q.toNat) qi
  calc
    p + BitVec.ofNat 64 (a - p.toNat) = BitVec.ofNat 64 (p.toNat + (a - p.toNat)) := by
      simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    _ = BitVec.ofNat 64 a := by congr 1; omega
    _ = BitVec.ofNat 64 (q.toNat + (a - q.toNat)) := by congr 1; omega
    _ = q + BitVec.ofNat 64 (a - q.toNat) := by
      simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem body_work_mapped (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (off byteCount : Nat) (within : off + byteCount ≤ 216) :
    Large.Mapped s.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) byteCount := by
  have hm := Delimited.Reservation.mapped_subrange s.dmem
    (s.regs.rsp.toBitVec - 16) 232 (16 + off) byteCount owned.localMapped (by omega)
  have same : s.regs.rsp.toBitVec - 16 + BitVec.ofNat 64 (16 + off) =
      s.regs.rsp.toBitVec + BitVec.ofNat 64 off := by
    rw [BitVec.ofNat_add]
    bv_omega
  simpa only [same] using hm

theorem body_stack_header_apart (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used) :
    Body.Apart (s.regs.rsp.toNat - 16) 288 s.regs.rcx.toNat 24 := by
  have same : (s.regs.rsp.toBitVec - 16).toNat = s.regs.rsp.toNat - 16 := by
    have low := owned.stackLow
    rw [← UInt64.toNat_toBitVec] at low ⊢
    bv_omega
  simpa only [same, UInt64.toNat_toBitVec] using
    (disjoint_apart _ _ _ _ owned.headerStack).symm

theorem body_stack_output_apart (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used) :
    Body.Apart (s.regs.rsp.toNat - 16) 288 s.regs.rbx.toNat 72 := by
  have same : (s.regs.rsp.toBitVec - 16).toNat = s.regs.rsp.toNat - 16 := by
    have low := owned.stackLow
    rw [← UInt64.toNat_toBitVec] at low ⊢
    bv_omega
  simpa only [same, UInt64.toNat_toBitVec] using
    (disjoint_apart _ _ _ _ owned.resultStack).symm

end SszX86.Measure.Bits
