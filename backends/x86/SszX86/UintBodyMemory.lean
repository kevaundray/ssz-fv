import SszX86.UintSmall
import SszX86.UintArena
import SszX86.UintLarge
import SszX86.UintTails

namespace SszX86.UintCodec.Body
open Kraken.X64.Parser
open SszNative BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Half-open physical regions. An empty span is disjoint from every span,
including spans containing its otherwise irrelevant pointer. -/
def Apart (p n q k : Nat) : Prop := n = 0 ∨ k = 0 ∨ p + n ≤ q ∨ q + k ≤ p

def Outside (a p n : Nat) : Prop := a < p ∨ p + n ≤ a

theorem Apart.symm {p n q k : Nat} (h : Apart p n q k) : Apart q k p n := by
  unfold Apart at *
  omega

theorem Apart.nonempty {p n q k : Nat} (h : Apart p n q k) (hn : 0 < n) (hk : 0 < k) :
    p + n ≤ q ∨ q + k ≤ p := by
  unfold Apart at h
  omega

theorem apart_bytes (p q : BitVec 64) (n k : Nat)
    (hp : p.toNat + n ≤ 2^64) (hq : q.toNat + k ≤ 2^64)
    (h : Apart p.toNat n q.toNat k) : Large.Disjoint p q n k := by
  intro i hi j hj
  unfold Apart at h
  bv_omega

theorem outside_byte (p a : BitVec 64) (n i : Nat)
    (hp : p.toNat + n ≤ 2^64) (ha : Outside a.toNat p.toNat n) (hi : i < n) :
    a ≠ p + BitVec.ofNat 64 i := by
  unfold Outside at ha
  bv_omega

/-- The body preserves these two anchors until the common RET. -/
structure Anchors (s t : MachineData) : Prop where
  out : t.regs.rdi = s.regs.rdi
  sp : t.regs.rsp = s.regs.rsp

theorem Anchors.refl (s : MachineData) : Anchors s s := ⟨rfl, rfl⟩

theorem Anchors.trans {s t u : MachineData} (h : Anchors s t) (g : Anchors t u) :
    Anchors s u := ⟨g.out.trans h.out, g.sp.trans h.sp⟩

theorem width_reg {s t : MachineData} (h : WidthFrame s t)
    (r : Reg64) (ha : r ≠ .rax) (hc : r ≠ .rcx) (hsi : r ≠ .rsi)
    (h8 : r ≠ .r8) (h10 : r ≠ .r10) : t.regs.get64 r = s.regs.get64 r :=
  h.2.2 r ha hc hsi h8 h10

theorem width_anchors {s t : MachineData} (h : WidthFrame s t) : Anchors s t := by
  constructor
  · apply UInt64.toBitVec_inj.1
    exact h.2.2 .rdi (by decide) (by decide) (by decide) (by decide) (by decide)
  · apply UInt64.toBitVec_inj.1
    exact h.2.2 .rsp (by decide) (by decide) (by decide) (by decide) (by decide)

theorem small_anchors {s t : MachineData} (h : Small.Frame s t) : Anchors s t :=
  ⟨h.rdi, h.rsp⟩

theorem arena_anchors {s t : MachineData} (h : Arena.Frame s t) : Anchors s t :=
  ⟨h.1, h.2.2.1⟩

theorem large_anchors {s t : MachineData} (h : Large.Fixed s t) : Anchors s t :=
  ⟨h.rdi, h.rsp⟩

/-- Ordinary initial mappings and the original saved activation. -/
structure TailOwned (s : MachineData) (saved : Saved) : Prop where
  output : BoolCodec.Mapped s.dmem s.regs.rdi.toBitVec
  stack : Tail.ActivationMapped s.dmem s.regs.rsp.toBitVec
  savedAt : SavedAt s.dmem s.regs.rsp.toBitVec saved
  separated : Tail.Separated s

theorem TailOwned.transport {s t : MachineData} {saved : Saved}
    (h : TailOwned s saved) (ha : Anchors s t)
    (hout : ∀ i < 80, t.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i))
    (hstack : ∀ i < 368, t.dmem.get? (s.regs.rsp.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rsp.toBitVec + BitVec.ofNat 64 i)) : TailOwned t saved := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [ha.out, hout i hi]
    exact h.output i hi
  · intro i hi
    rw [ha.sp, hstack i hi]
    exact h.stack i hi
  · rw [ha.sp]
    apply savedAt_congr s.dmem t.dmem s.regs.rsp.toBitVec saved
    · intro i hi
      exact hstack (312 + i) (by omega)
    · exact h.savedAt
  · rcases h.separated with ⟨ho, hs, hd⟩
    exact ⟨by simpa only [ha.out] using ho, by simpa only [ha.sp] using hs,
      by simpa only [ha.out, ha.sp] using hd⟩

theorem TailOwned.same_memory {s t : MachineData} {saved : Saved}
    (h : TailOwned s saved) (ha : Anchors s t) (hm : t.dmem = s.dmem) :
    TailOwned t saved :=
  h.transport ha (fun _ _ => by rw [hm]) (fun _ _ => by rw [hm])

/-- A read-only region is separated from every possible body write. The arena
condition covers only the available suffix; immutable inputs and handles may
reside in the already-used prefix. These are initial physical ownership facts. -/
structure Protected (s : MachineData) (address capacity used : BitVec 64)
    (p n : Nat) : Prop where
  bound : p + n ≤ 2^64
  output : Apart p n s.regs.rdi.toNat 76
  work : Apart p n (s.regs.rsp.toNat + 120) 48
  cursor : Apart p n (s.regs.rbx.toNat + 16) 8
  arena : Apart p n (address.toNat + used.toNat) (capacity.toNat - used.toNat)

/-- Initial caller-owned state. Capacity may be zero (with a null arena pointer)
or insufficient. The ABI's used≤capacity invariant does not assume reserve fits. -/
structure Owned (s : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) : Prop where
  tail : TailOwned s saved
  width_bound : s.regs.rbp.toNat + 24 ≤ 2^64
  width_at : NatMemory.At (widthLoad s.dmem) (s.regs.rbp.toNat + 8) expectedWidth
  length : data.size = s.regs.r14.toNat
  size : data.size < 2^63
  source : Small.BytesAt s data
  source_owned : Protected s address capacity used s.regs.rdx.toNat data.size
  descriptor : Protected s address capacity used s.regs.rbp.toNat 24
  borrowed : ∀ p words,
    NatMemory.largeAt (widthLoad s.dmem) (s.regs.rbp.toNat + 8) p words →
    words = [] ∨ Protected s address capacity used p (8 * words.length)
  header : Arena.Header s address capacity used
  arena_bound : address.toNat + capacity.toNat ≤ 2^64
  used_bound : used.toNat ≤ capacity.toNat
  arena_nonzero : 0 < capacity.toNat → 0 < address.toNat
  arena_mapped : Large.Mapped s.dmem address capacity.toNat
  arena_output : Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat) s.regs.rdi.toNat 80
  arena_stack : Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat) s.regs.rsp.toNat 368
  arena_header : Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat) s.regs.rbx.toNat 24
  header_output : Apart s.regs.rbx.toNat 24 s.regs.rdi.toNat 80
  header_stack : Apart s.regs.rbx.toNat 24 s.regs.rsp.toNat 368

/-- Actual reservation, if this invocation reaches and passes reserve. -/
def allocation (expectedWidth : Nat) (data : Ssz.Bytes) (address capacity used : BitVec 64) :
    Option SszNative.Arena.Reservation :=
  if expectedWidth = data.size ∧ 8 < WordDecode.significantBytes data data.size then
    SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
      (SszNative.Arena.wordsForBytes (WordDecode.significantBytes data data.size))
  else none

def Exhausted (expectedWidth : Nat) (data : Ssz.Bytes) (address capacity used : BitVec 64) : Prop :=
  expectedWidth = data.size ∧ 8 < WordDecode.significantBytes data data.size ∧
    SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
      (SszNative.Arena.wordsForBytes (WordDecode.significantBytes data data.size)) = none

instance (expectedWidth : Nat) (data : Ssz.Bytes) (address capacity used : BitVec 64) :
    Decidable (Exhausted expectedWidth data address capacity used) := by
  unfold Exhausted
  infer_instance

/-- Only output, six work words, and (on actual reservation success) the cursor
and exactly the reserved limb bytes may change. No whole-arena write allowance. -/
def Frame (s : MachineData) (m : DataMem) (count : Nat)
    (r : Option SszNative.Arena.Reservation) : Prop :=
  ∀ a : BitVec 64,
    Outside a.toNat s.regs.rdi.toNat 76 →
    Outside a.toNat (s.regs.rsp.toNat + 120) 48 →
    (∀ v, r = some v →
      (∀ j < 8, a ≠ s.regs.rbx.toBitVec + 16#64 + BitVec.ofNat 64 j) ∧
      (∀ j < 8 * SszNative.Arena.wordsForBytes count,
        a ≠ BitVec.ofNat 64 v.pointer + BitVec.ofNat 64 j)) →
    m.get? a = s.dmem.get? a

/-- RET is tied to the original activation, not to a late stage's register file. -/
structure Returned (s : MachineData) (saved : Saved) (t : MachineState) : Prop where
  pc : t.2 = Int64.ofBitVec saved.rip
  returnSlot : (Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 360#64) 8).map
    (fun value => Int64.ofBitVec (BitVec.ofInt 64 value)) = some t.2
  sp : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 368#64
  rbx : t.1.regs.rbx.toBitVec = saved.rbx
  r12 : t.1.regs.r12.toBitVec = saved.r12
  r13 : t.1.regs.r13.toBitVec = saved.r13
  r14 : t.1.regs.r14.toBitVec = saved.r14
  r15 : t.1.regs.r15.toBitVec = saved.r15
  rbp : t.1.regs.rbp.toBitVec = saved.rbp
  activation : SavedAt t.1.dmem s.regs.rsp.toBitVec saved

theorem returned_original {s u : MachineData} {saved : Saved} {t : MachineState}
    (hs : SavedAt s.dmem s.regs.rsp.toBitVec saved) (ha : Anchors s u)
    (h : Tail.Returned u t saved) : Returned s saved t := by
  refine ⟨h.pc, ?_, ?_, h.rbx, h.r12, h.r13, h.r14, h.r15, h.rbp, ?_⟩
  · rcases hs with ⟨_, _, _, _, _, _, hr⟩
    simp only [hr, Option.map_some, SszX86.ofBytes_wordBytes, h.pc]
  · simpa only [ha.sp] using h.sp
  · simpa only [ha.sp] using h.activation

theorem tail_frame {s u : MachineData} {t : MachineState} {saved : Saved}
    (ha : Anchors s u) (h : Tail.Returned u t saved) (count : Nat)
    (r : Option SszNative.Arena.Reservation) (hf : Frame s u.dmem count r) :
    Frame s t.1.dmem count r := by
  intro a ho hw hr
  exact (h.frame a (by simpa only [Outside, ha.out, UInt64.toNat_toBitVec] using ho)
    (by simpa only [Outside, ha.sp, UInt64.toNat_toBitVec, Nat.add_assoc, Nat.reduceAdd] using hw)).trans
      (hf a ho hw hr)

theorem frame_same {s u : MachineData} (hm : u.dmem = s.dmem) (count : Nat)
    (r : Option SszNative.Arena.Reservation) : Frame s u.dmem count r := by
  intro a _ _ _
  rw [hm]

/-- Width rejection's register pair is derived from the original mapped Nat;
large slices are neither canonicalized nor restricted to nonempty values. -/
theorem scope_pair (s t : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (hf : WidthFrame s t)
    (hp : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (t.regs.rax.toNat : Int))
    (hn : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 = some (t.regs.rcx.toNat : Int)) :
    Tail.NatPair t t.regs.rax.toBitVec t.regs.rcx.toBitVec expectedWidth := by
  have ha := width_anchors hf
  have lp : widthLoad s.dmem (s.regs.rbp.toNat + 8) 8 = some t.regs.rax.toNat := by
    change widthLoad s.dmem (s.regs.rbp.toBitVec.toNat + 8) 8 = _
    simp only [widthLoad, width_address, hp, Option.map_some, Int.toNat_natCast]
  have ln : widthLoad s.dmem (s.regs.rbp.toNat + 8 + 8) 8 = some t.regs.rcx.toNat := by
    change widthLoad s.dmem (s.regs.rbp.toBitVec.toNat + 16) 8 = _
    simp only [widthLoad, width_address, hn, Option.map_some, Int.toNat_natCast]
  rcases h.width_at with ⟨⟨hp0, hn0⟩, _⟩ | ⟨p, words, hw, hv⟩
  · have hz : t.regs.rax.toNat = 0 := Option.some.inj (lp.symm.trans hp0)
    have hv : t.regs.rcx.toNat = expectedWidth := Option.some.inj (ln.symm.trans hn0)
    exact Or.inl ⟨BitVec.eq_of_toNat_eq (by simpa using hz), hv⟩
  · have hp' : t.regs.rax.toNat = p := Option.some.inj (lp.symm.trans hw.2.2.2.2.1)
    have hn' : t.regs.rcx.toNat = words.length :=
      Option.some.inj (ln.symm.trans hw.2.2.2.2.2.1)
    refine Or.inr ⟨words, ?_, ?_, ?_, hn', ?_, hv, ?_⟩
    · simpa only [UInt64.toNat_toBitVec, hp'] using hw.1
    · simpa only [UInt64.toNat_toBitVec, hp'] using hw.2.2.1
    · simpa only [UInt64.toNat_toBitVec, hp'] using hw.2.2.2.1
    · simpa only [hf.1, UInt64.toNat_toBitVec, hp'] using hw.2.2.2.2.2.2
    · rcases h.borrowed p words hw with hz | hs
      · exact Or.inl hz
      · by_cases hz : words = []
        · exact Or.inl hz
        · have hpos : 0 < 8 * words.length := by
            cases words with
            | nil => contradiction
            | cons limb rest => simp only [List.length_cons]; omega
          exact Or.inr
            ⟨by simpa only [ha.out, UInt64.toNat_toBitVec, hp'] using
                hs.output.nonempty hpos (by decide),
              by simpa only [ha.sp, UInt64.toNat_toBitVec, hp', Nat.add_assoc, Nat.reduceAdd] using
                hs.work.nonempty hpos (by decide)⟩

/-- The successful reservation's exact committed cursor. -/
def Cursor (s : MachineData) (m : DataMem)
    (r : Option SszNative.Arena.Reservation) : Prop :=
  ∀ v, r = some v → widthLoad m (s.regs.rbx.toNat + 16) 8 = some v.used

theorem cursor_none (s : MachineData) (m : DataMem) : Cursor s m none := by
  intro v hv
  contradiction

theorem tail_cursor (s u : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (ha : Anchors s u) (t : MachineState) (ht : Tail.Returned u t saved)
    (r : Option SszNative.Arena.Reservation) (hc : Cursor s u.dmem r) : Cursor s t.1.dmem r := by
  intro v hv
  have eq : Mem.loadInt t.1.dmem (BitVec.ofNat 64 (s.regs.rbx.toNat + 16)) 8 =
      Mem.loadInt u.dmem (BitVec.ofNat 64 (s.regs.rbx.toNat + 16)) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    apply ht.frame
    · rw [ha.out]
      have hd := h.header_output
      have hb := h.header.nonwrap
      unfold Apart at hd
      simp only [← UInt64.toNat_toBitVec] at hd hb ⊢
      bv_omega
    · rw [ha.sp]
      have hd := h.header_stack
      have hb := h.header.nonwrap
      unfold Apart at hd
      simp only [← UInt64.toNat_toBitVec] at hd hb ⊢
      bv_omega
  simpa only [widthLoad, eq] using hc v hv

end SszX86.UintCodec.Body
