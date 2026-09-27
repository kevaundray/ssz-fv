import SszX86.DelimitedCore
import SszX86.NatCompareProofs

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- The real CALL has exactly one stack store; the comparison allocates no frame. -/
def callState (s : MachineData) (base : Int64) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8
      (base + 429).toBitVec.toInt}

/-- Keep the eight-byte encoding proof opaque to the complete call state. -/
theorem stored_return_load (m : DataMem) (address value : BitVec 64) :
    Mem.loadInt (Mem.storeInt m address 8 value.toInt) address 8 =
      some (Int.ofBytes (wordBytes value)) := by
  rw [wordBytes, ← registerBytes_eq_uintBytes, ofBytes_toBytes]
  exact BoolCodec.load_store_same m address 8 value.toInt (by decide)

theorem call_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (hp : Eventually (step e) P (callState s base, base + Int64.ofInt compareOffset)) :
    Eventually (step e) P (s, base + 424) := by
  delimited_step 99 using hc
  apply store_cps
  · simpa using hm
  · simpa [callState, compareOffset, Effects.All, Int64.add_assoc] using hp

/-- Composition invokes the checked, linked comparison body, not a comparison
oracle. Its Pair premises concern the state after the caller's return-slot store. -/
theorem compare_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hcompare : NatCompare.CodeAt e (base + Int64.ofInt compareOffset))
    (s : MachineData) (lhs rhs : Nat) (P : MachineState → Prop)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (hl : SszNative.NatMemory.Pair (UintCodec.widthLoad (callState s base).dmem)
      s.regs.rdi.toBitVec s.regs.rsi.toBitVec lhs)
    (hr : SszNative.NatMemory.Pair (UintCodec.widthLoad (callState s base).dmem)
      s.regs.rdx.toBitVec s.regs.rcx.toBitVec rhs)
    (hp : ∀ t, NatCompare.Returned (callState s base) (base + 429).toBitVec
      (compare lhs rhs) t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 424) := by
  apply call_runs e base hc s P hm
  apply eventually_trans (step e)
    (NatCompare.Returned (callState s base) (base + 429).toBitVec (compare lhs rhs))
    P _
  · apply NatCompare.program_correct e (base + Int64.ofInt compareOffset) hcompare
      (callState s base) lhs rhs (base + 429).toBitVec hl hr
    exact stored_return_load s.dmem (s.regs.rsp.toBitVec - 8) (base + 429).toBitVec
  · exact hp
end SszX86.Delimited
