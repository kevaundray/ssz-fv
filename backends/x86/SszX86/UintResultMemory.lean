import SszX86.UintWidth
import SszX86.BoolProofs
import SszUint

namespace SszX86.UintCodec.Tail

open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Ordinary caller-owned mapping of the complete activation, including the
six local words actually initialized by the scratch-failure path. -/
def ActivationMapped (m : DataMem) (sp : BitVec 64) : Prop :=
  ∀ i < 368, ∃ byte, m.get? (sp + BitVec.ofNat 64 i) = some byte

structure Separated (s : MachineData) : Prop where
  outputHigh : s.regs.rdi.toBitVec.toNat + 80 ≤ 2^64
  stackHigh : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64
  disjoint : s.regs.rdi.toBitVec.toNat + 80 ≤ s.regs.rsp.toBitVec.toNat ∨
    s.regs.rsp.toBitVec.toNat + 368 ≤ s.regs.rdi.toBitVec.toNat

/-- Exactly the result's first 76 bytes and the six scratch words may change. -/
def Frame (s t : MachineData) : Prop :=
  ∀ a : BitVec 64,
    (a.toNat < s.regs.rdi.toBitVec.toNat ∨ s.regs.rdi.toBitVec.toNat + 76 ≤ a.toNat) →
    (a.toNat < s.regs.rsp.toBitVec.toNat + 120 ∨ s.regs.rsp.toBitVec.toNat + 168 ≤ a.toNat) →
    t.dmem.get? a = s.dmem.get? a

/-- Register-carried native Nat. Large limbs need not be canonical or nonempty;
borrowed storage is protected from both the result and the six scratch words. -/
def NatPair (s : MachineData) (pointer payload : BitVec 64) (value : Nat) : Prop :=
  (pointer = 0#64 ∧ payload.toNat = value) ∨
  ∃ words : List (BitVec 64),
    0 < pointer.toNat ∧ pointer.toNat % 8 = 0 ∧
    pointer.toNat + 8 * words.length ≤ 2^64 ∧ payload.toNat = words.length ∧
    SszNative.NatMemory.wordsAt (widthLoad s.dmem) pointer.toNat words ∧
    SszNative.Limbs.value words = value ∧
    (words = [] ∨
      ((pointer.toNat + 8 * words.length ≤ s.regs.rdi.toBitVec.toNat ∨
        s.regs.rdi.toBitVec.toNat + 76 ≤ pointer.toNat) ∧
       (pointer.toNat + 8 * words.length ≤ s.regs.rsp.toBitVec.toNat + 120 ∨
        s.regs.rsp.toBitVec.toNat + 168 ≤ pointer.toNat)))

def successMem (m : DataMem) (out pointer payload : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 1 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 pointer.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 payload.toInt
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 0

def scopeMem (m : DataMem) (out pointer payload length : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 64) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 pointer.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 payload.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 length.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 72) 4 3
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1

/-- These are stores, not an assumption about preinitialized stack locals. -/
def zeroMem (m : DataMem) (sp : BitVec 64) : DataMem :=
  let work := sp + 120#64
  let m := Mem.storeInt m (work + BitVec.ofNat 64 0) 8 0
  let m := Mem.storeInt m (work + BitVec.ofNat 64 8) 8 0
  let m := Mem.storeInt m (work + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (work + BitVec.ofNat 64 24) 8 0
  let m := Mem.storeInt m (work + BitVec.ofNat 64 32) 8 0
  Mem.storeInt m (work + BitVec.ofNat 64 40) 8 0

def scratchCopyMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 64) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 72) 4 32768
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1

def successReady (s : MachineData) : MachineData :=
  {s with dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.r9.toBitVec s.regs.r8.toBitVec}

def scopeReady (s : MachineData) : MachineData :=
  {s with
    dmem := scopeMem s.dmem s.regs.rdi.toBitVec s.regs.rax.toBitVec
      s.regs.rcx.toBitVec s.regs.r14.toBitVec}

def scratchReady (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rax := 0, rcx := 0}
    dmem := scratchCopyMem (zeroMem s.dmem s.regs.rsp.toBitVec) s.regs.rdi.toBitVec}

theorem success_mem_frame (m : DataMem) (out pointer payload address : BitVec 64)
    (ha : ∀ i < 76, address ≠ out + BitVec.ofNat 64 i) :
    (successMem m out pointer payload).get? address = m.get? address := by
  simp (disch := first | assumption | omega | decide) only
    [successMem, store_frame (limit := 76)]

theorem scope_mem_frame (m : DataMem) (out pointer payload length address : BitVec 64)
    (ha : ∀ i < 76, address ≠ out + BitVec.ofNat 64 i) :
    (scopeMem m out pointer payload length).get? address = m.get? address := by
  simp (disch := first | assumption | omega | decide) only
    [scopeMem, store_frame (limit := 76)]

theorem zero_mem_frame (m : DataMem) (sp address : BitVec 64)
    (ha : ∀ i < 48, address ≠ sp + 120#64 + BitVec.ofNat 64 i) :
    (zeroMem m sp).get? address = m.get? address := by
  simp (disch := first | assumption | omega | decide) only
    [zeroMem, store_frame (limit := 48)]

theorem scratch_copy_frame (m : DataMem) (out address : BitVec 64)
    (ha : ∀ i < 76, address ≠ out + BitVec.ofNat 64 i) :
    (scratchCopyMem m out).get? address = m.get? address := by
  simp (disch := first | assumption | omega | decide) only
    [scratchCopyMem, store_frame (limit := 76)]

theorem success_frame (s : MachineData) (hs : Separated s) : Frame s (successReady s) := by
  intro a ha _
  apply success_mem_frame
  intro i hi
  have := hs.outputHigh
  bv_omega

theorem scope_frame (s : MachineData) (hs : Separated s) : Frame s (scopeReady s) := by
  intro a ha _
  apply scope_mem_frame
  intro i hi
  have := hs.outputHigh
  bv_omega

theorem scratch_frame (s : MachineData) (hs : Separated s) : Frame s (scratchReady s) := by
  intro a ha hb
  change (scratchCopyMem _ _).get? a = _
  rw [scratch_copy_frame]
  · apply zero_mem_frame
    intro i hi
    have := hs.stackHigh
    bv_omega
  · intro i hi
    have := hs.outputHigh
    bv_omega

theorem frame_saved (s t : MachineData) (saved : Saved) (hs : Separated s)
    (hf : Frame s t) (hm : SavedAt s.dmem s.regs.rsp.toBitVec saved) :
    SavedAt t.dmem s.regs.rsp.toBitVec saved := by
  apply savedAt_congr s.dmem t.dmem s.regs.rsp.toBitVec saved _ hm
  intro i hi
  apply hf
  · have := hs.outputHigh
    have := hs.stackHigh
    have := hs.disjoint
    bv_omega
  · have := hs.stackHigh
    bv_omega

theorem frame_words (s t : MachineData) (pointer : BitVec 64) (words : List (BitVec 64))
    (hf : Frame s t) (hrange : pointer.toNat + 8 * words.length ≤ 2^64)
    (hout : pointer.toNat + 8 * words.length ≤ s.regs.rdi.toBitVec.toNat ∨
      s.regs.rdi.toBitVec.toNat + 76 ≤ pointer.toNat)
    (hstack : pointer.toNat + 8 * words.length ≤ s.regs.rsp.toBitVec.toNat + 120 ∨
      s.regs.rsp.toBitVec.toNat + 168 ≤ pointer.toNat)
    (hm : SszNative.NatMemory.wordsAt (widthLoad s.dmem) pointer.toNat words) :
    SszNative.NatMemory.wordsAt (widthLoad t.dmem) pointer.toNat words := by
  intro i
  have heq : Mem.loadInt t.dmem (BitVec.ofNat 64 (pointer.toNat + 8 * i.val)) 8 =
      Mem.loadInt s.dmem (BitVec.ofNat 64 (pointer.toNat + 8 * i.val)) 8 := by
    apply memmove_loadInt_congr
    intro j hj
    have hi := i.isLt
    apply hf <;> bv_omega
  simpa only [widthLoad, heq] using hm i

theorem nat_at (s t : MachineData) (pointer payload : BitVec 64) (value address : Nat)
    (hf : Frame s t) (hn : NatPair s pointer payload value)
    (hp : widthLoad t.dmem address 8 = some pointer.toNat)
    (hc : widthLoad t.dmem (address + 8) 8 = some payload.toNat) :
    SszNative.NatMemory.At (widthLoad t.dmem) address value := by
  rcases hn with ⟨rfl, hv⟩ | ⟨words, hpos, halign, hspace, hcount, hm, hv, hsep⟩
  · exact Or.inl ⟨⟨hp, by simpa only [hv] using hc⟩, hv ▸ payload.isLt⟩
  · refine Or.inr ⟨pointer.toNat, words, ?_, hv⟩
    refine ⟨hpos, pointer.isLt, halign, hspace, hp, by simpa only [hcount] using hc, ?_⟩
    rcases hsep with rfl | ⟨hout, hstack⟩
    · intro i
      exact Fin.elim0 i
    · exact frame_words s t pointer words hf hspace hout hstack hm

private theorem observe_same (m : DataMem) (out : BitVec 64)
    (offset byteCount : Nat) (value : Int) (hb : byteCount ≤ 2^64) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 offset) byteCount value) out offset byteCount =
      some (value.take (8 * byteCount)).toNat := by
  rw [observe, load_store_same m _ byteCount value hb]
  rfl

private theorem observe_disjoint (m : DataMem) (out : BitVec 64)
    (hb : out.toNat + 80 ≤ 2^64) (a n b k : Nat) (value : Int)
    (ha : a + n ≤ 80) (hb' : b + k ≤ 80) (hs : a + n ≤ b ∨ b + k ≤ a) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 b) k value) out a n =
      observe m out a n := by
  simp only [observe, load_store_offset_disjoint m out hb a n b k value ha hb' hs]

private theorem signed64_nat (value : BitVec 64) :
    (value.toInt.take 64).toNat = value.toNat := by
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := value))
  simp only [BitVec.toNat_ofInt] at h
  simpa [Int.take] using h

private theorem load_observe (m : DataMem) (out : BitVec 64) (offset byteCount : Nat) :
    widthLoad m (out.toNat + offset) byteCount = observe m out offset byteCount := by
  simp only [widthLoad, observe, width_address]

private theorem load_observe_zero (m : DataMem) (out : BitVec 64) (byteCount : Nat) :
    widthLoad m out.toNat byteCount = observe m out 0 byteCount := by
  simp only [widthLoad, observe, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero]

macro "uint_result_reads" : tactic => `(tactic|
  (try simp only [Nat.add_assoc]
   simp (disch := first | assumption | omega | decide) only
     [successReady, scopeReady, scratchReady, successMem, scopeMem, scratchCopyMem,
      load_observe, load_observe_zero, observe_disjoint, observe_store64, observe_same,
      Nat.reduceAdd, Nat.reduceMul, signed64_nat]
   try decide))

theorem success_result (s : MachineData) (value : Nat) (hs : Separated s)
    (hn : NatPair s s.regs.r9.toBitVec s.regs.r8.toBitVec value) :
    SszNative.UintCodec.ResultAt (widthLoad (successReady s).dmem) s.regs.rdi.toBitVec.toNat
      (.ok (.uint value)) := by
  have hb := hs.outputHigh
  refine ⟨?_, ?_, nat_at s (successReady s) _ _ _ _ (success_frame s hs) hn ?_ ?_⟩
  all_goals uint_result_reads

theorem scope_result (s : MachineData) (expected : Nat) (hs : Separated s)
    (hn : NatPair s s.regs.rax.toBitVec s.regs.rcx.toBitVec expected) :
    SszNative.UintCodec.ResultAt (widthLoad (scopeReady s).dmem) s.regs.rdi.toBitVec.toNat
      (.error (.scope expected s.regs.r14.toBitVec.toNat)) := by
  have hb := hs.outputHigh
  change SszNative.UintCodec.errorAt _ _ _ _ _
  refine ⟨?_, ?_, ?_, nat_at s (scopeReady s) _ _ _ _ (scope_frame s hs) hn ?_ ?_,
    Or.inl ⟨⟨?_, ?_⟩, s.regs.r14.toBitVec.isLt⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals uint_result_reads

theorem scratch_result (s : MachineData) (hs : Separated s) :
    SszNative.UintCodec.scratchExhaustedAt (widthLoad (scratchReady s).dmem)
      s.regs.rdi.toBitVec.toNat := by
  have hb := hs.outputHigh
  change SszNative.UintCodec.errorAt _ _ _ _ _
  refine ⟨?_, ?_, ?_, Or.inl ⟨⟨?_, ?_⟩, by decide⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals uint_result_reads

end SszX86.UintCodec.Tail
