import SszX86.NatMulPrepare
import SszX86.NatMulMemoryStack

namespace SszX86.NatMul
open SszNative

def bodyState (s : MachineData) : MachineData := localState (pushedState s) s.status

theorem body_stack (s : MachineData) : (bodyState s).regs.rsp = s.regs.rsp - 88 := by
  apply UInt64.toBitVec_inj.1
  simp only [bodyState, localState, pushedState, NatAdd.pushedState, Delimited.pushedState,
    UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
  bv_omega

theorem entry_prepares (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra) :
    Eventually (step e) (Prepared (bodyState s) left right base) (s, base) := by
  apply pushes_cps e base hc s owned.push_mapped
  apply locals_cps e base hc
  intro flags
  have originals := pushed_operands s left right address capacity used ra owned
  have phase := prepare_runs e base hc (localState (pushedState s) flags) left right
    owned.left_pointer owned.left_payload owned.right_pointer owned.right_payload
    originals.1 originals.2
  exact eventually_weaken _ _ _ _
    (fun _ prepared => Prepared.rebase ⟨rfl, rfl, rfl, rfl, rfl⟩ prepared) phase

end SszX86.NatMul
