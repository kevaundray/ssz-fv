import SszX86.NatMulDispatch
import SszX86.NatMulMemoryTailcall

namespace SszX86.NatMul
open SszNative

theorem tailcall_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor : BitVec 64)
    (memory : t.dmem = pushedMem s)
    (output : t.regs.rdi = s.regs.rdi)
    (stack : t.regs.rsp = s.regs.rsp - 88)
    (arena : t.regs.r9 = s.regs.r9)
    (pointer : t.regs.rsi.toBitVec = operand.pointer)
    (payload : t.regs.rdx.toBitVec = operand.payload)
    (scalar : t.regs.rcx.toBitVec = factor)
    (simd : t.zmms = s.zmms)
    (P : MachineState → Prop)
    (next : ∀ u, TailState s u operand factor →
      Eventually (step e) P (u, base + Int64.ofNat wordOffset)) :
    Eventually (step e) P (t, base + 184) := by
  apply helper_arena_cps e base hc
  apply unlocal_tail_cps e base hc
  intro flags
  have sp : (unlocalState (helperArenaState t) flags).regs.rsp.toBitVec =
      s.regs.rsp.toBitVec - 48 := by
    simp only [unlocalState, helperArenaState, stack, UInt64.toBitVec_add,
      UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  apply restore_tail_cps e base hc _ s
  · rw [sp]
    simpa only [unlocalState, helperArenaState, memory] using NatAdd.pushed_saved s
  apply word_tail_cps e base hc
  apply next
  constructor
  · exact memory
  · exact output
  · apply UInt64.toBitVec_inj.1
    simp only [restoredState, NatAdd.restoredState, UInt64.toBitVec_ofBitVec, sp]
    bv_omega
  · exact arena
  · exact pointer
  · exact payload
  · exact scalar
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact simd

end SszX86.NatMul
