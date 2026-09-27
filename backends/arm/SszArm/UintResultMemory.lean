import SszArm.UintTailExec
import SszArm.UintWidthMemory
import SszUint

namespace SszArm.UintCodec.Tail

open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- All tail accesses are nonwrapping. Output is disjoint from both the working
stack and the original saved activation. The gap between them remains framed. -/
structure Separated (s : ArmState) : Prop where
  stackLow : 16 ≤ (r (.GPR 31#5) s).toNat
  stackHigh : (r (.GPR 31#5) s).toNat + 368 ≤ 2^64
  outputHigh : (r (.GPR 0#5) s).toNat + 80 ≤ 2^64
  working : (r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat + 192 ≤ (r (.GPR 0#5) s).toNat
  activation : (r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat + 272 ∨
    (r (.GPR 31#5) s).toNat + 368 ≤ (r (.GPR 0#5) s).toNat

/-- The only writable locations are the result and the working stack, never the
saved x19--x30 activation. -/
def Frame (s t : ArmState) : Prop :=
  ∀ a : BitVec 64,
    (a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat) →
    (a.toNat < (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat + 192 ≤ a.toNat) →
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
        (r (.GPR 31#5) s).toNat + 192 ≤ pointer.toNat)))

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
      (r (.GPR 31#5) s).toNat + 192 ≤ pointer.toNat)
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

/-- Splitting a real STP is a memory identity, not a replacement instruction. -/
theorem write_pair_words (s : ArmState) (address lo hi : BitVec 64)
    (hspace : address.toNat + 16 ≤ 2^64) :
    write_mem_bytes 16 address (hi ++ lo) s =
      write_mem_bytes 8 (address + 8#64) hi (write_mem_bytes 8 address lo s) := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    simp only [state_simp_rules]
  · simp only [state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    funext a
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes]
    by_cases hbefore : a.toNat < address.toNat
    · rw [Memory.write_bytes_eq_of_le hbefore hspace,
        Memory.write_bytes_eq_of_le (by bv_omega) (by bv_omega),
        Memory.write_bytes_eq_of_le hbefore (by omega)]
    · by_cases hafter : address.toNat + 16 ≤ a.toNat
      · rw [Memory.write_bytes_eq_of_ge hafter hspace,
          Memory.write_bytes_eq_of_ge (by bv_omega) (by bv_omega),
          Memory.write_bytes_eq_of_ge (by omega) (by omega)]
      · rw [Memory.write_bytes_eq_extractLsByte (by omega) (by omega) hspace]
        by_cases hlow : a.toNat < address.toNat + 8
        · rw [Memory.write_bytes_eq_of_le (by bv_omega) (by bv_omega),
            Memory.write_bytes_eq_extractLsByte (by omega) hlow (by omega)]
          simp only [BitVec.extractLsByte_def]
          exact BitVec.extractLsb'_append_eq_of_add_le (by bv_omega)
        · rw [Memory.write_bytes_eq_extractLsByte (by bv_omega) (by bv_omega) (by bv_omega)]
          simp only [BitVec.extractLsByte_def]
          rw [BitVec.extractLsb'_append_eq_of_le (by bv_omega)]
          congr 1
          bv_omega

def successReady (s : ArmState) (base : BitVec 64) : ArmState :=
  afterJump tagStores (block (successOps.map Prod.snd) s) base 4732

def scopeReady (s : ArmState) : ArmState :=
  tagsStored (reasonStored (tagInitialized (block (scopeOps.map Prod.snd) s)))

/-- Optional simplifier conditions must fail without the recovery performed by
`all_goals`. This is the same bitvector-to-Nat arithmetic as `bv_omega`, sequenced
on its single condition rather than using that tactic's `<;>` combinator. -/
macro "tail_side" : tactic => `(tactic|
  first
  | assumption
  | omega
  | (try simp -implicitDefEqProofs only [bitvec_to_nat] at *
     omega))

macro "tail_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [successReady, scopeReady, successOps, scopeOps, block, List.map_cons, List.map_nil,
     Prod.snd, Op.effect, next, put, afterJump, tagStores, storeBlock,
     List.foldl_cons, List.foldl_nil, StoreOp.effect, tagsStored, reasonStored,
     tagInitialized, state_simp_rules, ArmState.mem_w_eq_mem,
     write_pair_ones, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.add_assoc])

macro "tail_reads" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    (disch := tail_side) only
    [state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.setWidth_ofNat_of_le,
     BitVec.sub_add_cancel, BitVec.add_sub_cancel, write_pair_words,
     read_mem_bytes_write_mem_bytes_same, read_mem_bytes_write_mem_bytes_disjoint])

theorem success_ready_frame (s : ArmState) (base : BitVec 64) (hs : Separated s) :
    Frame s (successReady s base) := by
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  intro a ha hb
  tail_expand
  simp (disch := tail_side)
    [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem scope_ready_frame (s : ArmState) (hs : Separated s) :
    Frame s (scopeReady s) := by
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  intro a ha hb
  tail_expand
  tail_reads
  simp (disch := tail_side)
    [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem success_ready_result (s : ArmState) (base : BitVec 64) (value : Nat)
    (hs : Separated s) (hn : NatPair s (r (.GPR 12#5) s) (r (.GPR 10#5) s) value) :
    SszNative.UintCodec.ResultAt (widthLoad (successReady s base))
      (r (.GPR 0#5) s).toNat (.ok (.uint value)) := by
  have hf := success_ready_frame s base hs
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  refine ⟨?_, ?_, nat_at s (successReady s base) _ _ _ _ hf hn ?_ ?_⟩
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    tail_expand
    tail_reads
    try rfl

theorem scope_ready_result (s : ArmState) (expected : Nat)
    (hs : Separated s) (hn : NatPair s (r (.GPR 8#5) s) (r (.GPR 9#5) s) expected) :
    SszNative.UintCodec.ResultAt (widthLoad (scopeReady s))
      (r (.GPR 0#5) s).toNat (.error (.scope expected (r (.GPR 3#5) s).toNat)) := by
  have hf := scope_ready_frame s hs
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  change SszNative.UintCodec.errorAt _ _ _ _ _
  refine ⟨?_, ?_, ?_, nat_at s (scopeReady s) _ _ _ _ hf hn ?_ ?_,
    Or.inl ⟨⟨?_, ?_⟩, (r (.GPR 3#5) s).isLt⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    tail_expand
    tail_reads
    try rfl

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

end SszArm.UintCodec.Tail
