import SszX86.DispatchTransport

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

theorem apart_left {p n q k : Nat} (h : Body.Apart p n q k)
    (off count : Nat) (within : off + count ≤ n) : Body.Apart (p + off) count q k := by
  unfold Body.Apart at h ⊢
  omega

/-- Embed a body-SP-relative work region in the original mapped activation,
without unfolding the register-file construction while transporting equality. -/
theorem body_interval (s : MachineData) (base : Int64) (kind : Kind)
    (low : 472 ≤ s.regs.rsp.toNat) (p n : Nat)
    (apart : Body.Apart p n (stackStart s) 480)
    (before after count : Nat) (below : before ≤ 112)
    (above : after + count ≤ 368 + before) :
    Body.Apart p n ((bodyState s base kind).regs.rsp.toNat - before + after) count := by
  have old : Body.Apart p n (s.regs.rsp.toNat - 472) 480 := apart
  have region : Body.Apart p n (s.regs.rsp.toNat - 360 - before + after) count := by
    unfold Body.Apart at old ⊢
    omega
  exact Eq.mpr (congrArg (fun q : Nat => Body.Apart p n (q - before + after) count)
    (body_spNat s base kind low)) region

end SszX86.Dispatch
