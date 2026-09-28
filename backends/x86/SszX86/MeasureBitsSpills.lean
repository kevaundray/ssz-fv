import SszX86.MeasureBitsStored
import SszX86.MeasureBitsCountCommit
import SszX86.MeasureBitsListCommit
import SszX86.MeasureBitsProgressiveCompare

namespace SszX86.Measure.Bits
open UintCodec

def spillMem (m : DataMem) (sp header payload : BitVec 64) : DataMem :=
  Mem.storeInt (Mem.storeInt m (sp + 8) 8 header.toInt) (sp + 16) 8 payload.toInt

theorem spill_frame (s : MachineData) (m : DataMem) (header payload : BitVec 64) :
    MemoryFrame m (spillMem m s.regs.rsp.toBitVec header payload)
      (fun a => InSpan a (s.regs.rsp.toBitVec - 16) 232) := by
  intro a safe
  unfold spillMem
  rw [store_frame _ _ _ _ a (by
    intro inside
    exact safe (body_local_span s 16 8 (by decide) a inside))]
  exact store_frame _ _ _ _ a (by
    intro inside
    exact safe (body_local_span s 8 8 (by decide) a inside))

theorem spill_mapped (m : DataMem) (sp header payload : BitVec 64) :
    MappedExtension m (spillMem m sp header payload) := by
  intro p n hm
  unfold spillMem
  repeat' first | exact hm | apply Large.mapped_store

theorem spill_reads (m : DataMem) (sp header payload : BitVec 64) :
    Mem.loadInt (spillMem m sp header payload) (sp + 8) 8 = some (header.toNat : Int) ∧
      Mem.loadInt (spillMem m sp header payload) (sp + 16) 8 = some (payload.toNat : Int) := by
  constructor
  · unfold spillMem
    rw [BoolCodec.load_store_disjoint _ _ _ 8 8 _ (by
      intro i hi j hj equal
      bv_omega)]
    exact stored_word_load _ _ _
  · exact stored_word_load _ _ _

theorem call_spill_read (s : MachineData) (ra : BitVec 64) (off : Nat)
    (within : 8 ≤ off ∧ off + 8 ≤ 24) :
    Mem.loadInt (callState s ra).dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 =
      Mem.loadInt s.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj equal
  bv_omega

theorem list_commit_form (s : MachineData)
    (apart : Large.Disjoint (s.regs.rcx.toBitVec + 16) (s.regs.rsp.toBitVec + 16) 8 8) :
    ListReservation.commitMem s =
      NatFromU128.commitMem (smallListMem s) s.regs.rcx.toBitVec
        (s.regs.rax.toBitVec + s.regs.r8.toBitVec) s.regs.rsi.toBitVec
        s.regs.r15.toBitVec s.regs.r14.toBitVec := by
  unfold ListReservation.commitMem smallListMem NatFromU128.commitMem
  dsimp only
  rw [store_commute _ (s.regs.rcx.toBitVec + 16#64) (s.regs.rsp.toBitVec + 16#64)
    8 8 _ _ (by decide) (by decide) (by with_unfolding_all exact apart)]

end SszX86.Measure.Bits
