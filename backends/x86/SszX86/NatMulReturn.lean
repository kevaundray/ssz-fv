import SszX86.NatMulStack
import SszX86.NatMulOwnership

namespace SszX86.NatMul

theorem return_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (ra : BitVec 64)
    (stack : t.regs.rsp = s.regs.rsp - 88)
    (saved : SavedAt t.dmem (s.regs.rsp.toBitVec - 48) s)
    (simd : t.zmms = s.zmms)
    (returnSlot : Mem.loadInt t.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (P : MachineState → Prop)
    (next : ∀ u, u.dmem = t.dmem → Returned s ra (u, Int64.ofBitVec ra) → P (u, Int64.ofBitVec ra)) :
    Eventually (step e) P (t, base + 228) := by
  apply unlocal_return_cps e base hc
  intro flags
  have sp : (unlocalState t flags).regs.rsp.toBitVec = s.regs.rsp.toBitVec - 48 := by
    simp only [unlocalState, stack, UInt64.toBitVec_add, UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  apply restore_return_cps e base hc _ s
  · rw [sp]
    simpa only [unlocalState] using saved
  have restoredSp : (restoredState (unlocalState t flags) s).regs.rsp.toBitVec = s.regs.rsp.toBitVec := by
    simp only [restoredState, NatAdd.restoredState, UInt64.toBitVec_ofBitVec, sp]
    bv_omega
  apply ret_cps e base hc _ ra
  · rw [restoredSp]
    simpa only [restoredState, NatAdd.restoredState, unlocalState] using returnSlot
  apply next
  · rfl
  · refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, simd, returnSlot⟩
    simp only [Delimited.retState, restoredSp]

end SszX86.NatMul
