import SszX86.ByteViewTails
import SszX86.ByteViewList

namespace SszX86.ByteView
open Kraken.X64.Parser UintCodec BoolCodec SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Initial physical ownership only. The capacity is an unrestricted native Nat;
immutable spans may share one another, including empty and redundant Large
descriptors. No arena mapping or successful reservation is needed: neither
byte-view body accesses the arena or writes activation work slots. -/
structure Owned (s : MachineData) (saved : Saved) (capacity : Nat) (data : Ssz.Bytes) : Prop where
  output : Mapped s.dmem s.regs.rdi.toBitVec
  savedAt : SavedAt s.dmem s.regs.rsp.toBitVec saved
  separated : Tail.Separated s
  capacity_at : NatMemory.At (widthLoad s.dmem) (s.regs.rbp.toNat + 8) capacity
  length : data.size = s.regs.r14.toNat
  source : SszNative.ByteView.BytesAt (widthLoad s.dmem) s.regs.rdx.toNat data
  source_owned : Protected s s.regs.rdx.toNat data.size
  descriptor : Protected s s.regs.rbp.toNat 24
  borrowed : ∀ p words,
    NatMemory.largeAt (widthLoad s.dmem) (s.regs.rbp.toNat + 8) p words →
    Protected s p (8 * words.length)

structure Fixed (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  out : t.regs.rdi = s.regs.rdi
  sp : t.regs.rsp = s.regs.rsp
  source : t.regs.rdx = s.regs.rdx
  length : t.regs.r14 = s.regs.r14

theorem vector_fixed {s t : MachineData} (h : WidthFrame s t) : Fixed s t := by
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  all_goals apply UInt64.toBitVec_inj.1
  · exact h.2.2 .rdi (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.2.2 .rsp (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.2.2 .rdx (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.2.2 .r14 (by decide) (by decide) (by decide) (by decide) (by decide)

theorem list_fixed {s t : MachineData} (h : ListCompare.Frame s t) : Fixed s t := by
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  all_goals apply UInt64.toBitVec_inj.1
  · exact h.2.2 .rdi (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.2.2 .rsp (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.2.2 .rdx (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.2.2 .r14 (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Complete native observation at the original RET. Every byte outside the
result's first 76 bytes is unchanged, and success publishes the original RDX
source pointer rather than a copied or freshly allocated byte buffer. -/
structure Post (s : MachineData) (saved : Saved) (result : Except Ssz.Err Ssz.Value)
    (t : MachineState) : Prop where
  observed : SszNative.ByteView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat result
  returned : UintCodec.Body.Returned s saved t
  frame : Frame s t.1.dmem
  aliases : ∀ data, result = .ok (.bytes data) →
    widthLoad t.1.dmem (s.regs.rdi.toNat + 24) 8 = some s.regs.rdx.toNat

theorem original_frame {s u : MachineData} {m : DataMem} (hf : Fixed s u)
    (h : Frame u m) : Frame s m := by
  intro a ha
  rw [← hf.memory]
  exact h a (by simpa only [hf.out] using ha)

theorem pair (s u : MachineData) (saved : Saved) (capacity : Nat) (data : Ssz.Bytes)
    (h : Owned s saved capacity data) (hf : Fixed s u)
    (hp : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (u.regs.rax.toNat : Int))
    (hn : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 = some (u.regs.rcx.toNat : Int)) :
    Pair u u.regs.rax.toBitVec u.regs.rcx.toBitVec capacity := by
  have lp : widthLoad s.dmem (s.regs.rbp.toNat + 8) 8 = some u.regs.rax.toNat := by
    change widthLoad s.dmem (s.regs.rbp.toBitVec.toNat + 8) 8 = _
    simp only [widthLoad, width_address, hp, Option.map_some, Int.toNat_natCast]
  have ln : widthLoad s.dmem (s.regs.rbp.toNat + 8 + 8) 8 = some u.regs.rcx.toNat := by
    change widthLoad s.dmem (s.regs.rbp.toBitVec.toNat + 16) 8 = _
    simp only [widthLoad, width_address, hn, Option.map_some, Int.toNat_natCast]
  rcases h.capacity_at with ⟨⟨hp0, hn0⟩, _⟩ | ⟨p, words, hw, hv⟩
  · have hz : u.regs.rax.toNat = 0 := Option.some.inj (lp.symm.trans hp0)
    have hv : u.regs.rcx.toNat = capacity := Option.some.inj (ln.symm.trans hn0)
    exact Or.inl ⟨BitVec.eq_of_toNat_eq (by simpa using hz), hv⟩
  · have hp' : u.regs.rax.toNat = p := Option.some.inj (lp.symm.trans hw.2.2.2.2.1)
    have hn' : u.regs.rcx.toNat = words.length := Option.some.inj (ln.symm.trans hw.2.2.2.2.2.1)
    refine Or.inr ⟨words, ?_, ?_, ?_, hn', ?_, hv, ?_⟩
    · simpa only [UInt64.toNat_toBitVec, hp'] using hw.1
    · simpa only [UInt64.toNat_toBitVec, hp'] using hw.2.2.1
    · simpa only [UInt64.toNat_toBitVec, hp'] using hw.2.2.2.1
    · simpa only [hf.memory, UInt64.toNat_toBitVec, hp'] using hw.2.2.2.2.2.2
    · simpa only [hf.out, UInt64.toNat_toBitVec, hp'] using (h.borrowed p words hw).output

theorem success_cont (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (saved : Saved) (capacity : Nat) (data : Ssz.Bytes)
    (h : Owned s saved capacity data) (hf : Fixed s u) :
    Eventually (step e) (Post s saved (.ok (.bytes data))) (u, base + 2759) := by
  have hm : Mapped u.dmem u.regs.rdi.toBitVec := by simpa only [hf.memory, hf.out] using h.output
  have ha : SavedAt u.dmem u.regs.rsp.toBitVec saved := by simpa only [hf.memory, hf.sp] using h.savedAt
  have hs : Tail.Separated u := ⟨by simpa only [hf.out] using h.separated.outputHigh,
    by simpa only [hf.sp] using h.separated.stackHigh,
    by simpa only [hf.out, hf.sp] using h.separated.disjoint⟩
  apply success_runs e base hc u saved hm ha hs
  have fr := success_frame u hs.outputHigh
  have res := success_result u data hs.outputHigh
    (by simpa only [hf.length] using h.length)
    (by simpa only [hf.memory, hf.source] using h.source)
    ⟨by simpa only [hf.source] using h.source_owned.bound,
      by simpa only [hf.source, hf.out] using h.source_owned.output⟩
  refine ⟨?_, ?_, original_frame hf fr, ?_⟩
  · simpa only [returned, hf.out] using res.1
  · exact UintCodec.Body.returned_original h.savedAt ⟨hf.out, hf.sp⟩
      (Tail.returned_contract u (successReady u) saved hs ha rfl (frame_tail fr))
  · intro d hd
    simpa only [returned, hf.out, hf.source] using res.2

theorem scope_cont (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (saved : Saved) (capacity : Nat) (data : Ssz.Bytes)
    (h : Owned s saved capacity data) (hf : Fixed s u)
    (hp : Pair u u.regs.rax.toBitVec u.regs.rcx.toBitVec capacity) :
    Eventually (step e) (Post s saved (.error (.scope capacity data.size))) (u, base + 2851) := by
  have hm : Mapped u.dmem u.regs.rdi.toBitVec := by simpa only [hf.memory, hf.out] using h.output
  have ha : SavedAt u.dmem u.regs.rsp.toBitVec saved := by simpa only [hf.memory, hf.sp] using h.savedAt
  have hs : Tail.Separated u := ⟨by simpa only [hf.out] using h.separated.outputHigh,
    by simpa only [hf.sp] using h.separated.stackHigh,
    by simpa only [hf.out, hf.sp] using h.separated.disjoint⟩
  apply Tail.scope_runs e base (uint_codeAt e base hc) u saved hm ha hs
  have fr := scope_frame u hs.outputHigh
  refine ⟨?_, ?_, original_frame hf fr, ?_⟩
  · simpa only [returned, hf.out, hf.length, ← h.length] using scope_result u capacity hs.outputHigh hp
  · exact UintCodec.Body.returned_original h.savedAt ⟨hf.out, hf.sp⟩
      (Tail.returned_contract u (Tail.scopeReady u) saved hs ha rfl (frame_tail fr))
  · intro d hd
    contradiction

theorem limit_cont (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (saved : Saved) (capacity : Nat) (data : Ssz.Bytes)
    (h : Owned s saved capacity data) (hf : Fixed s u)
    (hp : Pair u u.regs.rax.toBitVec u.regs.rcx.toBitVec capacity) :
    Eventually (step e) (Post s saved (.error (.overLimit capacity data.size))) (u, base + 2591) := by
  have hm : Mapped u.dmem u.regs.rdi.toBitVec := by simpa only [hf.memory, hf.out] using h.output
  have ha : SavedAt u.dmem u.regs.rsp.toBitVec saved := by simpa only [hf.memory, hf.sp] using h.savedAt
  have hs : Tail.Separated u := ⟨by simpa only [hf.out] using h.separated.outputHigh,
    by simpa only [hf.sp] using h.separated.stackHigh,
    by simpa only [hf.out, hf.sp] using h.separated.disjoint⟩
  apply limit_runs e base hc u saved hm ha hs
  have fr := limit_frame u hs.outputHigh
  refine ⟨?_, ?_, original_frame hf fr, ?_⟩
  · simpa only [returned, hf.out, hf.length, ← h.length] using limit_result u capacity hs.outputHigh hp
  · exact UintCodec.Body.returned_original h.savedAt ⟨hf.out, hf.sp⟩
      (Tail.returned_contract u (limitReady u) saved hs ha rfl (frame_tail fr))
  · intro d hd
    contradiction

/-- Complete ByteVector postdispatch decoding through the original RET. -/
theorem vector_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved) (capacity : Nat) (data : Ssz.Bytes)
    (h : Owned s saved capacity data) :
    Eventually (step e) (Post s saved (Ssz.deserialize (.byteVector capacity) data))
      (s, base + 750) := by
  rw [← SszNative.ByteView.vector_outcome_eq_deserialize]
  apply eventually_trans (step e) (Vector.Post s base capacity) _ _
    (Vector.runs e base hc s capacity h.capacity_at)
  rintro ⟨u, pc⟩ ⟨fr, exit, hp, hn⟩
  have hf := vector_fixed fr
  by_cases he : capacity = data.size
  · have he' : capacity = s.regs.r14.toNat := he.trans h.length
    simp only [he', ↓reduceIte] at exit
    subst pc
    simpa only [SszNative.ByteView.vectorOutcome, he.symm, ↓reduceIte] using
      success_cont e base hc s u saved capacity data h hf
  · have he' : capacity ≠ s.regs.r14.toNat := fun hx => he (hx.trans h.length.symm)
    simp only [he', ↓reduceIte] at exit
    subst pc
    simpa only [SszNative.ByteView.vectorOutcome, Ne.symm he, ↓reduceIte] using
      scope_cont e base hc s u saved capacity data h hf (pair s u saved capacity data h hf hp hn)

/-- Complete ByteList postdispatch decoding for unrestricted native Nat limits. -/
theorem list_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved) (capacity : Nat) (data : Ssz.Bytes)
    (h : Owned s saved capacity data) :
    Eventually (step e) (Post s saved (Ssz.deserialize (.byteList capacity) data))
      (s, base + 824) := by
  rw [← SszNative.ByteView.list_outcome_eq_deserialize]
  apply eventually_trans (step e) (ListCompare.Post s base capacity) _ _
    (ListCompare.runs e base hc s capacity h.capacity_at)
  rintro ⟨u, pc⟩ ⟨fr, exit, hp, hn⟩
  have hf := list_fixed fr
  by_cases he : data.size ≤ capacity
  · have he' : s.regs.r14.toNat ≤ capacity := h.length ▸ he
    simp only [he', ↓reduceIte] at exit
    subst pc
    simpa only [SszNative.ByteView.listOutcome, he, ↓reduceIte] using
      success_cont e base hc s u saved capacity data h hf
  · have he' : ¬ s.regs.r14.toNat ≤ capacity := by simpa only [h.length] using he
    simp only [he', ↓reduceIte] at exit
    subst pc
    simpa only [SszNative.ByteView.listOutcome, he, ↓reduceIte] using
      limit_cont e base hc s u saved capacity data h hf (pair s u saved capacity data h hf hp hn)

theorem preserves_region (s : MachineData) (saved : Saved) (result : Except Ssz.Err Ssz.Value)
    (t : MachineState) (post : Post s saved result t) (p n : Nat) (hp : Protected s p n) :
    ∀ i < n, t.1.dmem.get? (BitVec.ofNat 64 (p+i)) = s.dmem.get? (BitVec.ofNat 64 (p+i)) := by
  intro i hi
  apply post.frame
  have bound := hp.bound
  have apart := hp.output
  unfold UintCodec.Body.Outside UintCodec.Body.Apart at *
  bv_omega

theorem source_preserved (s : MachineData) (saved : Saved) (capacity : Nat) (data : Ssz.Bytes)
    (h : Owned s saved capacity data) (result : Except Ssz.Err Ssz.Value)
    (t : MachineState) (post : Post s saved result t) :
    ∀ i < data.size, t.1.dmem.get? (s.regs.rdx.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rdx.toBitVec + BitVec.ofNat 64 i) := by
  intro i hi
  simpa only [← UInt64.toNat_toBitVec, width_address] using
    preserves_region s saved result t post _ _ h.source_owned i hi

theorem descriptor_preserved (s : MachineData) (saved : Saved) (capacity : Nat) (data : Ssz.Bytes)
    (h : Owned s saved capacity data) (result : Except Ssz.Err Ssz.Value)
    (t : MachineState) (post : Post s saved result t) :
    ∀ i < 24, t.1.dmem.get? (s.regs.rbp.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rbp.toBitVec + BitVec.ofNat 64 i) := by
  intro i hi
  simpa only [← UInt64.toNat_toBitVec, width_address] using
    preserves_region s saved result t post _ _ h.descriptor i hi

theorem borrowed_preserved (s : MachineData) (saved : Saved) (capacity : Nat) (data : Ssz.Bytes)
    (h : Owned s saved capacity data) (result : Except Ssz.Err Ssz.Value)
    (t : MachineState) (post : Post s saved result t) (p : Nat) (words : List (BitVec 64))
    (hw : NatMemory.largeAt (widthLoad s.dmem) (s.regs.rbp.toNat + 8) p words) :
    ∀ i < 8 * words.length, t.1.dmem.get? (BitVec.ofNat 64 (p+i)) =
      s.dmem.get? (BitVec.ofNat 64 (p+i)) :=
  preserves_region s saved result t post _ _ (h.borrowed p words hw)

end SszX86.ByteView
