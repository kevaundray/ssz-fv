import SszArm.ByteViewTailExec
import SszByteView

namespace SszArm.ByteView.Tail

open BoolCodec
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- All tail accesses are nonwrapping. Output is disjoint from both the lowering
slot and the original saved activation. The gap between them remains framed. -/
structure Separated (s : ArmState) : Prop where
  stackLow : 16 ≤ (r (.GPR 31#5) s).toNat
  stackHigh : (r (.GPR 31#5) s).toNat + 368 ≤ 2^64
  outputHigh : (r (.GPR 0#5) s).toNat + 80 ≤ 2^64
  working : (r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat
  activation : (r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat + 272 ∨
    (r (.GPR 31#5) s).toNat + 368 ≤ (r (.GPR 0#5) s).toNat

/-- The only writable locations are the result and the lowering slot, never the
saved x19--x30 activation. -/
def Frame (s t : ArmState) : Prop :=
  ∀ a : BitVec 64,
    (a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat) →
    (a.toNat < (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) →
    t.mem a = s.mem a

/-- A native Nat carried in registers, with either a Small payload or a borrowed
or newly allocated Large slice. Empty and noncanonical Large slices are allowed.
Separation protects the limb array through every output and lowering-stack store. -/
def NatPair (s : ArmState) (pointer count : BitVec 64) (value : Nat) : Prop :=
  (pointer = 0#64 ∧ count.toNat = value) ∨
  ∃ words : List (BitVec 64),
    0 < pointer.toNat ∧ pointer.toNat % 8 = 0 ∧
    pointer.toNat + 8 * words.length ≤ 2^64 ∧ count.toNat = words.length ∧
    SszNative.NatMemory.wordsAt (widthLoad s) pointer.toNat words ∧
    SszNative.Limbs.value words = value ∧
    (words = [] ∨
      ((pointer.toNat + 8 * words.length ≤ (r (.GPR 0#5) s).toNat ∨
        (r (.GPR 0#5) s).toNat + 76 ≤ pointer.toNat) ∧
       (pointer.toNat + 8 * words.length ≤ (r (.GPR 31#5) s).toNat - 16 ∨
        (r (.GPR 31#5) s).toNat ≤ pointer.toNat)))

theorem frame_activation (s t : ArmState) (hs : Separated s) (hf : Frame s t) :
    ActivationPreserved s t := by
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  intro i hi
  change t.mem (r (.GPR 31#5) s + BitVec.ofNat 64 (272 + i)) =
    s.mem (r (.GPR 31#5) s + BitVec.ofNat 64 (272 + i))
  apply hf <;> bv_omega

theorem frame_words (s t : ArmState) (pointer : BitVec 64) (words : List (BitVec 64))
    (hf : Frame s t) (hrange : pointer.toNat + 8 * words.length ≤ 2^64)
    (hout : pointer.toNat + 8 * words.length ≤ (r (.GPR 0#5) s).toNat ∨
      (r (.GPR 0#5) s).toNat + 76 ≤ pointer.toNat)
    (hstack : pointer.toNat + 8 * words.length ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ pointer.toNat)
    (hm : SszNative.NatMemory.wordsAt (widthLoad s) pointer.toNat words) :
    SszNative.NatMemory.wordsAt (widthLoad t) pointer.toNat words := by
  intro i
  have heq : read_mem_bytes 8 (BitVec.ofNat 64 (pointer.toNat + 8 * i.val)) t =
      read_mem_bytes 8 (BitVec.ofNat 64 (pointer.toNat + 8 * i.val)) s := by
    apply read_bytes_congr
    intro j hj
    have hi := i.isLt
    apply hf <;> bv_omega
  simpa only [widthLoad, heq] using hm i

theorem nat_at (s t : ArmState) (pointer count : BitVec 64) (value address : Nat)
    (hf : Frame s t) (hn : NatPair s pointer count value)
    (hp : widthLoad t address 8 = some pointer.toNat)
    (hc : widthLoad t (address + 8) 8 = some count.toNat) :
    SszNative.NatMemory.At (widthLoad t) address value := by
  rcases hn with ⟨rfl, hv⟩ | ⟨words, hpos, halign, hspace, hcount, hm, hv, hsep⟩
  · exact Or.inl ⟨⟨hp, by simpa only [hv] using hc⟩, hv ▸ count.isLt⟩
  · refine Or.inr ⟨pointer.toNat, words, ?_, hv⟩
    refine ⟨hpos, pointer.isLt, halign, hspace, hp, by simpa only [hcount] using hc, ?_⟩
    rcases hsep with rfl | ⟨hout, hstack⟩
    · intro i
      exact Fin.elim0 i
    · exact frame_words s t pointer words hf hspace hout hstack hm

/-- A returned tail restores every one of the twelve saved integer registers,
the saved return PC, and the caller's SP, while retaining the memory frame. -/
structure Returned (s t : ArmState) : Prop where
  pc : read_pc t = read_mem_bytes 8 (r (.GPR 31#5) s + 280#64) s
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s + 368#64
  registers : ∀ reg offset, (reg, offset) ∈ savedRegisters →
    r (.GPR reg) t = read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) s
  activation : ActivationPreserved s t
  frame : Frame s t

theorem returned_contract (s t : ArmState) (hs : Separated s)
    (hsp : r (.GPR 31#5) t = r (.GPR 31#5) s) (hf : Frame s t) :
    Returned s (returned t) := by
  have hact := frame_activation s t hs hf
  have hmem : ∀ n a, read_mem_bytes n a (returned t) = read_mem_bytes n a t := by
    intro n a
    simp [returned, state_simp_rules]
  refine ⟨returned_pc_of_activation s t hsp hact, ?_, ?_, ?_, ?_⟩
  · rw [returned_sp, hsp]
  · intro reg offset hr
    rw [returned_register t reg offset hr, hsp, hmem]
    have hb := savedRegister_bounds reg offset hr
    have hword := activation_word s t (offset - 272) hact (by omega)
    change read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 (272 + (offset - 272))) t =
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 (272 + (offset - 272))) s at hword
    simpa only [show 272 + (offset - 272) = offset by omega] using hword
  · intro i hi
    simpa only [read_mem, returned_mem] using hact i hi
  · intro a ha hb
    rw [returned_mem]
    exact hf a ha hb


macro "byte_tail_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [successReady, limitReady, successOps, limitOps, block, List.map_cons, List.map_nil,
     Prod.snd, Op.effect, UintCodec.Tail.scopeReady, UintCodec.Tail.scopeOps,
     UintCodec.Tail.block, UintCodec.Tail.Op.effect, UintCodec.Tail.next,
     UintCodec.Tail.put, afterJump, tagStores, storeBlock,
     List.foldl_cons, List.foldl_nil, StoreOp.effect, tagsStored, reasonStored,
     tagInitialized, state_simp_rules, ArmState.mem_w_eq_mem,
     write_pair_ones, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.add_assoc])

theorem success_ready_frame (s : ArmState) (base : BitVec 64) (hs : Separated s) :
    Frame s (successReady s base) := by
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  intro a ha hb
  byte_tail_expand
  simp (disch := tail_side)
    [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem scope_ready_frame (s : ArmState) (hs : Separated s) :
    Frame s (UintCodec.Tail.scopeReady s) := by
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  intro a ha hb
  byte_tail_expand
  tail_reads
  simp (disch := tail_side)
    [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem limit_ready_frame (s : ArmState) (hs : Separated s) :
    Frame s (limitReady s) := by
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  intro a ha hb
  byte_tail_expand
  tail_reads
  simp (disch := tail_side)
    [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem scope_ready_result (s : ArmState) (expected : Nat)
    (hs : Separated s) (hn : NatPair s (r (.GPR 8#5) s) (r (.GPR 9#5) s) expected) :
    SszNative.ByteView.ResultAt (widthLoad (UintCodec.Tail.scopeReady s))
      (r (.GPR 0#5) s).toNat (.error (.scope expected (r (.GPR 3#5) s).toNat)) := by
  have hf := scope_ready_frame s hs
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  change SszNative.UintCodec.errorAt _ _ _ _ _
  refine ⟨?_, ?_, ?_, nat_at s (UintCodec.Tail.scopeReady s) _ _ _ _ hf hn ?_ ?_,
    Or.inl ⟨⟨?_, ?_⟩, (r (.GPR 3#5) s).isLt⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    byte_tail_expand
    tail_reads
    try rfl

theorem limit_ready_result (s : ArmState) (expected : Nat)
    (hs : Separated s) (hn : NatPair s (r (.GPR 8#5) s) (r (.GPR 9#5) s) expected) :
    SszNative.ByteView.ResultAt (widthLoad (limitReady s))
      (r (.GPR 0#5) s).toNat (.error (.overLimit expected (r (.GPR 3#5) s).toNat)) := by
  have hf := limit_ready_frame s hs
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  change SszNative.UintCodec.errorAt _ _ _ _ _
  refine ⟨?_, ?_, ?_, nat_at s (limitReady s) _ _ _ _ hf hn ?_ ?_,
    Or.inl ⟨⟨?_, ?_⟩, (r (.GPR 3#5) s).isLt⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    byte_tail_expand
    tail_reads
    try rfl

/-- The borrowed input can be empty anywhere or occupy already-used arena bytes.
Only actual stores, not unused activation-local space, require separation. -/
structure Input (s : ArmState) (data : Ssz.Bytes) : Prop where
  size : (r (.GPR 3#5) s).toNat = data.size
  high : (r (.GPR 2#5) s).toNat + data.size ≤ 2^64
  bytes : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 2#5) s).toNat data
  separated : data.size = 0 ∨
    (((r (.GPR 2#5) s).toNat + data.size ≤ (r (.GPR 0#5) s).toNat ∨
      (r (.GPR 0#5) s).toNat + 76 ≤ (r (.GPR 2#5) s).toNat) ∧
     ((r (.GPR 2#5) s).toNat + data.size ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (r (.GPR 2#5) s).toNat))

theorem frame_bytes (s t : ArmState) (data : Ssz.Bytes)
    (hf : Frame s t) (hi : Input s data) :
    SszNative.ByteView.BytesAt (widthLoad t) (r (.GPR 2#5) s).toNat data := by
  intro i hb
  have heq : widthLoad t ((r (.GPR 2#5) s).toNat + i) 1 =
      widthLoad s ((r (.GPR 2#5) s).toNat + i) 1 := by
    unfold widthLoad
    congr 1
    congr 1
    apply read_bytes_congr
    intro j hj
    have hh := hi.high
    rcases hi.separated with hz | ⟨hout, hstack⟩
    · omega
    · apply hf <;> bv_omega
  rw [heq]
  exact hi.bytes i hb

theorem success_ready_result (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hs : Separated s) (hi : Input s data) :
    SszNative.ByteView.ResultAt (widthLoad (successReady s base))
      (r (.GPR 0#5) s).toNat (.ok (.bytes data)) ∧
    widthLoad (successReady s base) ((r (.GPR 0#5) s).toNat + 24) 8 =
      some (r (.GPR 2#5) s).toNat := by
  have hf := success_ready_frame s base hs
  have hb := frame_bytes s (successReady s base) data hf hi
  have hn := hi.size
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  refine ⟨⟨?_, ?_, (r (.GPR 2#5) s).toNat, ?_, ?_, hb⟩, ?_⟩
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    byte_tail_expand
    tail_reads
    try rfl
    try exact congrArg some hn

end SszArm.ByteView.Tail
