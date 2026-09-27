import SszArm.ByteViewMemory

namespace SszArm.ByteView.Tail

open BoolCodec
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

@[simp] theorem success_ready_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (successReady s base) = r (.GPR 31#5) s := by
  byte_tail_expand
  try simp [BitVec.sub_add_cancel]

@[simp] theorem limit_ready_sp (s : ArmState) :
    r (.GPR 31#5) (limitReady s) = r (.GPR 31#5) s := by
  byte_tail_expand
  try simp [BitVec.sub_add_cancel]

theorem success_correct (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hc : CodeAt s base) (hp : read_pc s = base + 4492#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) (hs : Separated s)
    (hi : Input s data) :
    Returned s (run 21 s) ∧ read_err (run 21 s) = .None ∧
    SszNative.ByteView.ResultAt (widthLoad (run 21 s))
      (r (.GPR 0#5) s).toNat (.ok (.bytes data)) ∧
    widthLoad (run 21 s) ((r (.GPR 0#5) s).toNat + 24) 8 =
      some (r (.GPR 2#5) s).toNat := by
  rw [success_run s base hc hp he ha]
  refine ⟨returned_contract s _ hs (success_ready_sp s base) (success_ready_frame s base hs), ?_, ?_⟩
  · have hb : read_err (successReady s base) = .None :=
      (afterJump_error tagStores (block (successOps.map Prod.snd) s) base 4732).trans
        ((block_error _ s).trans he)
    simpa [returned, state_simp_rules] using hb
  · rw [UintCodec.Tail.returned_load]
    exact success_ready_result s base data hs hi

theorem scope_correct (s : ArmState) (base : BitVec 64) (expected : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + 4544#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) (hs : Separated s)
    (hn : NatPair s (r (.GPR 8#5) s) (r (.GPR 9#5) s) expected) :
    Returned s (run 55 s) ∧ read_err (run 55 s) = .None ∧
    SszNative.ByteView.ResultAt (widthLoad (run 55 s))
      (r (.GPR 0#5) s).toNat (.error (.scope expected (r (.GPR 3#5) s).toNat)) := by
  rw [UintCodec.Tail.scope_run s base (uint_codeAt hc) hp he ha]
  refine ⟨returned_contract s _ hs (UintCodec.Tail.scope_ready_sp s) (scope_ready_frame s hs), ?_, ?_⟩
  · have hb : read_err (UintCodec.Tail.block (UintCodec.Tail.scopeOps.map Prod.snd) s) = .None :=
      (UintCodec.Tail.block_error _ s).trans he
    simpa [returned, UintCodec.Tail.scopeReady, tagsStored, reasonStored, tagInitialized,
      state_simp_rules] using hb
  · rw [UintCodec.Tail.returned_load]
    exact scope_ready_result s expected hs hn

theorem limit_correct (s : ArmState) (base : BitVec 64) (expected : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + 3576#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) (hs : Separated s)
    (hn : NatPair s (r (.GPR 8#5) s) (r (.GPR 9#5) s) expected) :
    Returned s (run 48 s) ∧ read_err (run 48 s) = .None ∧
    SszNative.ByteView.ResultAt (widthLoad (run 48 s))
      (r (.GPR 0#5) s).toNat (.error (.overLimit expected (r (.GPR 3#5) s).toNat)) := by
  rw [limit_run s base hc hp he ha]
  refine ⟨returned_contract s _ hs (limit_ready_sp s) (limit_ready_frame s hs), ?_, ?_⟩
  · have hb : read_err (block (limitOps.map Prod.snd) s) = .None := (block_error _ s).trans he
    simpa [returned, limitReady, tagsStored, reasonStored, tagInitialized, state_simp_rules] using hb
  · rw [UintCodec.Tail.returned_load]
    exact limit_ready_result s expected hs hn

end SszArm.ByteView.Tail
