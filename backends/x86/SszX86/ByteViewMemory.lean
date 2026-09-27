import SszX86.ByteViewVector
import SszByteView

namespace SszX86.ByteView
open Kraken.X64.Parser
open UintCodec BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def successMem (m : DataMem) (out pointer length : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 1 2
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 pointer.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 length.toInt
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 0

def limitMem (m : DataMem) (out pointer payload length : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 64) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 pointer.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 payload.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 length.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 72) 4 2
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1

def successReady (s : MachineData) : MachineData :=
  {s with dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.rdx.toBitVec s.regs.r14.toBitVec}

def limitReady (s : MachineData) : MachineData :=
  {s with
    dmem := limitMem s.dmem s.regs.rdi.toBitVec s.regs.rax.toBitVec
      s.regs.rcx.toBitVec s.regs.r14.toBitVec}

def Frame (s : MachineData) (m : DataMem) : Prop :=
  ∀ a : BitVec 64, UintCodec.Body.Outside a.toNat s.regs.rdi.toNat 76 →
    m.get? a = s.dmem.get? a

theorem success_frame (s : MachineData) (hb : s.regs.rdi.toNat + 80 ≤ 2^64) :
    Frame s (successReady s).dmem := by
  intro a ha
  have h : ∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i := by
    intro i hi
    have ha' := ha
    unfold UintCodec.Body.Outside at ha'
    simp only [← UInt64.toNat_toBitVec] at hb ha'
    bv_omega
  simp (disch := first | assumption | omega | decide) only
    [successReady, successMem, store_frame (limit := 76)]

theorem limit_frame (s : MachineData) (hb : s.regs.rdi.toNat + 80 ≤ 2^64) :
    Frame s (limitReady s).dmem := by
  intro a ha
  have h : ∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i := by
    intro i hi
    have ha' := ha
    unfold UintCodec.Body.Outside at ha'
    simp only [← UInt64.toNat_toBitVec] at hb ha'
    bv_omega
  simp (disch := first | assumption | omega | decide) only
    [limitReady, limitMem, store_frame (limit := 76)]

theorem scope_frame (s : MachineData) (hb : s.regs.rdi.toNat + 80 ≤ 2^64) :
    Frame s (Tail.scopeReady s).dmem := by
  intro a ha
  apply Tail.scope_mem_frame
  intro i hi
  unfold UintCodec.Body.Outside at ha
  simp only [← UInt64.toNat_toBitVec] at hb ha
  bv_omega

theorem frame_tail {s : MachineData} {m : DataMem} (hf : Frame s m) :
    Tail.Frame s {s with dmem := m} := fun a ha _ => hf a ha

structure Protected (s : MachineData) (p n : Nat) : Prop where
  bound : p + n ≤ 2^64
  output : UintCodec.Body.Apart p n s.regs.rdi.toNat 76

def Pair (s : MachineData) (pointer payload : BitVec 64) (value : Nat) : Prop :=
  (pointer = 0#64 ∧ payload.toNat = value) ∨
  ∃ words : List (BitVec 64),
    0 < pointer.toNat ∧ pointer.toNat % 8 = 0 ∧
    pointer.toNat + 8 * words.length ≤ 2^64 ∧ payload.toNat = words.length ∧
    SszNative.NatMemory.wordsAt (widthLoad s.dmem) pointer.toNat words ∧
    SszNative.Limbs.value words = value ∧
    UintCodec.Body.Apart pointer.toNat (8 * words.length) s.regs.rdi.toNat 76

theorem nat_at (s : MachineData) (m : DataMem) (pointer payload : BitVec 64)
    (value address : Nat) (hf : Frame s m) (hn : Pair s pointer payload value)
    (hp : widthLoad m address 8 = some pointer.toNat)
    (hc : widthLoad m (address + 8) 8 = some payload.toNat) :
    SszNative.NatMemory.At (widthLoad m) address value := by
  rcases hn with ⟨rfl, hv⟩ | ⟨words, hpos, halign, hspace, hcount, hm, hv, hsep⟩
  · exact Or.inl ⟨⟨hp, by simpa only [hv] using hc⟩, hv ▸ payload.isLt⟩
  · refine Or.inr ⟨pointer.toNat, words, ?_, hv⟩
    refine ⟨hpos, pointer.isLt, halign, hspace, hp, by simpa only [hcount] using hc, ?_⟩
    intro i
    have eq : Mem.loadInt m (BitVec.ofNat 64 (pointer.toNat + 8 * i.val)) 8 =
        Mem.loadInt s.dmem (BitVec.ofNat 64 (pointer.toNat + 8 * i.val)) 8 := by
      apply memmove_loadInt_congr
      intro j hj
      apply hf
      have hi := i.isLt
      unfold UintCodec.Body.Apart at hsep
      unfold UintCodec.Body.Outside
      bv_omega
    simpa only [widthLoad, eq] using hm i

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

macro "view_result_reads" : tactic => `(tactic|
  (simp only [← UInt64.toNat_toBitVec] at *
   try simp only [Nat.add_assoc]
   simp (disch := first | assumption | omega | decide) only
     [successReady, limitReady, Tail.scopeReady, successMem, limitMem, Tail.scopeMem,
      load_observe, load_observe_zero, observe_disjoint, observe_store64, observe_same,
      Nat.reduceAdd, Nat.reduceMul, signed64_nat]
   try decide))

theorem success_result (s : MachineData) (data : Ssz.Bytes)
    (hb : s.regs.rdi.toNat + 80 ≤ 2^64)
    (hn : data.size = s.regs.r14.toNat)
    (hm : SszNative.ByteView.BytesAt (widthLoad s.dmem) s.regs.rdx.toNat data)
    (hsource : Protected s s.regs.rdx.toNat data.size) :
    SszNative.ByteView.ResultAt (widthLoad (successReady s).dmem) s.regs.rdi.toNat
      (.ok (.bytes data)) ∧
    widthLoad (successReady s).dmem (s.regs.rdi.toNat + 24) 8 = some s.regs.rdx.toNat := by
  have hf := success_frame s hb
  have bytes : SszNative.ByteView.BytesAt (widthLoad (successReady s).dmem)
      s.regs.rdx.toNat data := by
    intro i hi
    have he : Mem.loadInt (successReady s).dmem (BitVec.ofNat 64 (s.regs.rdx.toNat + i)) 1 =
        Mem.loadInt s.dmem (BitVec.ofNat 64 (s.regs.rdx.toNat + i)) 1 := by
      apply memmove_loadInt_congr
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simp only [BitVec.add_zero]
      apply hf
      have bound := hsource.bound
      have apart := hsource.output
      unfold UintCodec.Body.Outside UintCodec.Body.Apart at *
      bv_omega
    simpa only [widthLoad, he] using hm i hi
  constructor
  · refine ⟨?_, ?_, s.regs.rdx.toNat, ?_, ?_, bytes⟩
    all_goals try rw [hn]
    all_goals view_result_reads
  · view_result_reads

theorem limit_result (s : MachineData) (expected : Nat)
    (hb : s.regs.rdi.toNat + 80 ≤ 2^64)
    (hn : Pair s s.regs.rax.toBitVec s.regs.rcx.toBitVec expected) :
    SszNative.ByteView.ResultAt (widthLoad (limitReady s).dmem) s.regs.rdi.toNat
      (.error (.overLimit expected s.regs.r14.toNat)) := by
  change SszNative.UintCodec.errorAt _ _ _ _ _
  refine ⟨?_, ?_, ?_, nat_at s (limitReady s).dmem _ _ _ _ (limit_frame s hb) hn ?_ ?_,
    Or.inl ⟨⟨?_, ?_⟩, s.regs.r14.toBitVec.isLt⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals view_result_reads

theorem scope_result (s : MachineData) (expected : Nat)
    (hb : s.regs.rdi.toNat + 80 ≤ 2^64)
    (hn : Pair s s.regs.rax.toBitVec s.regs.rcx.toBitVec expected) :
    SszNative.ByteView.ResultAt (widthLoad (Tail.scopeReady s).dmem) s.regs.rdi.toNat
      (.error (.scope expected s.regs.r14.toNat)) := by
  change SszNative.UintCodec.errorAt _ _ _ _ _
  refine ⟨?_, ?_, ?_, nat_at s (Tail.scopeReady s).dmem _ _ _ _ (scope_frame s hb) hn ?_ ?_,
    Or.inl ⟨⟨?_, ?_⟩, s.regs.r14.toBitVec.isLt⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals view_result_reads

end SszX86.ByteView
