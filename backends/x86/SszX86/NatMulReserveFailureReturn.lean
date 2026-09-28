import SszX86.NatMulReserveCps
import SszX86.NatMulFailureReturn

namespace SszX86.NatMul
open SszNative

theorem reservation_failure_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s current : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (memory : current.dmem = pushedMem s) (output : current.regs.rdi = s.regs.rdi)
    (stack : current.regs.rsp = s.regs.rsp - 88) (simd : current.zmms = s.zmms)
    (t : MachineState) (failed : Reservation.Failed current base address capacity used t)
    (outcome : SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.unchanged used.toNat (.error .scratchExhausted)) :
    Eventually (step e) (Post s left right address capacity used ra) t := by
  rcases t with ⟨t, pc⟩
  have failure : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result =
      .error .scratchExhausted := by rw [outcome]; rfl
  have out : t.regs.rdi = s.regs.rdi :=
    (failed.1.2 .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans output
  have sp : t.regs.rsp = s.regs.rsp - 88 :=
    (failed.1.2 .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans stack
  have mem : t.dmem = pushedMem s := failed.2.1.trans memory
  have vectors : t.zmms = s.zmms := failed.1.1.trans simd
  rcases failed.2.2 with ⟨overflow, pcEq⟩ | ⟨bound, exhausted, pcEq⟩
  · dsimp only at pcEq
    rw [pcEq]
    exact count_error_finish_cps e base hc s t left right address capacity used ra owned
      failure mem out sp vectors
  · dsimp only at pcEq
    rw [pcEq]
    exact error_finish_cps e base hc s t left right address capacity used ra owned
      failure mem out sp vectors

end SszX86.NatMul
