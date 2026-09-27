import SszX86.UintBodyLarge

namespace SszX86.UintCodec.Body
open SszNative WordDecode BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The exact native split: only matched Large scratch exhaustion differs from
upstream deserialization. Both outcomes return through the original activation. -/
structure Post (s : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (t : MachineState) : Prop where
  observed : if Exhausted expectedWidth data address capacity used then
    SszNative.UintCodec.scratchExhaustedAt (widthLoad t.1.dmem) s.regs.rdi.toNat
  else SszNative.UintCodec.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (Ssz.deserialize (.uint expectedWidth) data)
  returned : Returned s saved t
  frame : Frame s t.1.dmem (significantBytes data data.size)
    (allocation expectedWidth data address capacity used)
  cursor : Cursor s t.1.dmem (allocation expectedWidth data address capacity used)

/-- Opaque success continuation, shared by Small and arbitrary-length Large. -/
private theorem success_cont (e : Executable) (base : Int64) (code : CodeAt e base)
    (s u : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (ha : Anchors s u) (ho : TailOwned u saved)
    (heq : expectedWidth = data.size)
    (hne : ¬ Exhausted expectedWidth data address capacity used)
    (hf : Frame s u.dmem (significantBytes data data.size)
      (allocation expectedWidth data address capacity used))
    (cursor : Cursor s u.dmem (allocation expectedWidth data address capacity used))
    (hp : Tail.NatPair u u.regs.r9.toBitVec u.regs.r8.toBitVec (Ssz.readUint data 0 data.size)) :
    Eventually (step e) (Post s saved expectedWidth data address capacity used) (u, base + 5502) := by
  apply eventually_weaken _ _ _ _ _
    (Tail.success_refines e base code u saved _ ho.output ho.savedAt ho.separated hp)
  intro t ht
  refine ⟨?_, returned_original h.tail.savedAt ha ht.2.1, tail_frame ha ht.2.1 _ _ hf,
    tail_cursor s u saved expectedWidth data address capacity used h ha t ht.2.1 _ cursor⟩
  simp only [hne, ↓reduceIte]
  have he : Ssz.deserialize (.uint expectedWidth) data = .ok (.uint (Ssz.readUint data 0 data.size)) := by
    rw [deserialize_uint data expectedWidth heq.symm, decode_value]
  simpa only [he, ha.out, UInt64.toNat_toBitVec] using ht.1

private theorem scratch_cont (e : Executable) (base : Int64) (code : CodeAt e base)
    (s u : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (ha : Anchors s u) (hm : u.dmem = s.dmem)
    (hex : Exhausted expectedWidth data address capacity used) :
    Eventually (step e) (Post s saved expectedWidth data address capacity used) (u, base + 2918) := by
  have ho := h.tail.same_memory ha hm
  have noalloc : allocation expectedWidth data address capacity used = none := by
    rw [allocation, ite_eq_left ⟨hex.1, hex.2.1⟩]
    exact hex.2.2
  apply eventually_weaken _ _ _ _ _
    (Tail.scratch_refines e base code u saved ho.output ho.stack ho.savedAt ho.separated)
  intro t ht
  refine ⟨?_, returned_original h.tail.savedAt ha ht.2.1,
    tail_frame ha ht.2.1 _ _ (frame_same hm _ _),
    by rw [noalloc]; exact cursor_none _ _⟩
  simpa only [hex, ↓reduceIte, ha.out, UInt64.toNat_toBitVec] using ht.1

private theorem scope_cont (e : Executable) (base : Int64) (code : CodeAt e base)
    (s u : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (hf : WidthFrame s u) (hlen : u.regs.r14 = s.regs.r14)
    (hne : expectedWidth ≠ data.size)
    (hp : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (u.regs.rax.toNat : Int))
    (hn : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 = some (u.regs.rcx.toNat : Int)) :
    Eventually (step e) (Post s saved expectedWidth data address capacity used) (u, base + 2851) := by
  have ha := width_anchors hf
  have ho := h.tail.same_memory ha hf.1
  have pair := scope_pair s u saved expectedWidth data address capacity used h hf hp hn
  have noalloc : allocation expectedWidth data address capacity used = none := by
    simp only [allocation, hne, false_and, ↓reduceIte]
  apply eventually_weaken _ _ _ _ _
    (Tail.scope_refines e base code u saved expectedWidth ho.output ho.savedAt ho.separated pair)
  intro t ht
  refine ⟨?_, returned_original h.tail.savedAt ha ht.2.1,
    tail_frame ha ht.2.1 _ _ (frame_same hf.1 _ _),
    by rw [noalloc]; exact cursor_none _ _⟩
  have hx : ¬ Exhausted expectedWidth data address capacity used := fun hx => hne hx.1
  simp only [hx, ↓reduceIte]
  have he : Ssz.deserialize (.uint expectedWidth) data = .error (.scope expectedWidth data.size) := by
    rw [← WordDecode.outcome_eq_deserialize]
    simp only [WordDecode.outcome, Ne.symm hne, ↓reduceIte]
  simpa only [he, ha.out, hlen, UInt64.toNat_toBitVec, h.length] using ht.1

/-- The complete postdispatch UInt body, PC 1131 through RET. The input Nat is
unrestricted: Small, empty Large, redundant Large, and widths above UInt64 all
use the same checked comparison contract. Initial physical ownership includes
empty/insufficient arenas and never presupposes a successful reservation.
`Eventually` quantifies every ISA undefined-flag choice in each reused block. -/
theorem runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used) :
    Eventually (step e) (Post s saved expectedWidth data address capacity used) (s, base + 1131) := by
  apply width_cps e base code s expectedWidth h.width_bound h.width_at
  rintro ⟨u, pc⟩ ⟨wf, wx⟩
  have wa := width_anchors wf
  have wr14 : u.regs.r14 = s.regs.r14 := by
    apply UInt64.toBitVec_inj.1
    exact width_reg wf .r14 (by decide) (by decide) (by decide) (by decide) (by decide)
  have wrdx : u.regs.rdx = s.regs.rdx := by
    apply UInt64.toBitVec_inj.1
    exact width_reg wf .rdx (by decide) (by decide) (by decide) (by decide) (by decide)
  have wrbx : u.regs.rbx = s.regs.rbx := by
    apply UInt64.toBitVec_inj.1
    exact width_reg wf .rbx (by decide) (by decide) (by decide) (by decide) (by decide)
  by_cases matched : expectedWidth = s.regs.r14.toNat
  · simp only [matched, ↓reduceIte] at wx
    rcases wx with ⟨rfl, wrax, wr10, wr8⟩
    have heq : expectedWidth = data.size := matched.trans h.length.symm
    have wlen : data.size = u.regs.r14.toNat := by simpa only [wr14] using h.length
    have wm : u.dmem = s.dmem := wf.1
    have wsource : Small.BytesAt u data := by
      simpa only [Small.BytesAt, wm, wrdx] using h.source
    apply Small.trim_and_pack_cps e base code u data
      (wrax.trans wr14.symm) (wr10.trans wr14.symm) wr8 wlen h.size
      (by simpa only [wrdx] using h.source_owned.bound) wsource
    rintro ⟨v, pc⟩ ⟨sf, sx⟩
    have va := wa.trans (small_anchors sf)
    have vm : v.dmem = s.dmem := sf.1.trans wf.1
    by_cases small : significantBytes data data.size ≤ 8
    · simp only [small, ↓reduceIte] at sx
      rcases sx with ⟨rfl, vr9, vr8⟩
      apply success_cont e base code s v saved expectedWidth data address capacity used h va
        (h.tail.same_memory va vm) heq
      · intro hex
        have := hex.2.1
        omega
      · exact frame_same vm _ _
      · have noalloc : allocation expectedWidth data address capacity used = none := by
          simp only [allocation, show ¬ 8 < significantBytes data data.size from by omega,
            and_false, ↓reduceIte]
        rw [noalloc]
        exact cursor_none _ _
      · exact Or.inl ⟨congrArg UInt64.toBitVec vr9, vr8⟩
    · simp only [small, ↓reduceIte] at sx
      rcases sx with ⟨rfl, vr10, vrbp, vrdx, vr14, vrbx⟩
      let count := significantBytes data data.size
      have hc : 9 ≤ count := by dsimp [count]; omega
      have hle : count ≤ data.size := significantBytes_le data data.size
      have ve : LargeEntry s v data count := by
        refine ⟨va, vm, vrbx.trans wrbx, vrdx.trans wrdx, ?_, ?_, ?_⟩
        · rw [vr14, wr14, ← h.length]
        · dsimp only [count]
          rw [← vrbp]
          simp
        · dsimp only [count]
          rw [← vr10]
          simp
      apply Arena.reservation_cps e base code v count address capacity used
        (entry_header ve h.header) hc
        (by simpa only [UInt64.toNat_toBitVec, ve.length] using hle)
        (by simpa only [UInt64.toNat_toBitVec, ve.length] using h.size)
        (by simpa only [UInt64.toNat_toBitVec, ve.source, ve.length] using h.source_owned.bound)
        ve.pred ve.hcount
      rintro ⟨w, pc⟩ ⟨af, ax⟩
      rcases ax with ⟨failed, rfl, wm⟩ | ⟨r, reserved, _, _, rfl, flags, rfl⟩
      · apply scratch_cont e base code s w saved expectedWidth data address capacity used h
          (va.trans (arena_anchors af)) (wm.trans vm)
        exact ⟨heq, by dsimp [count] at hc; omega, failed⟩
      · apply large_cps e base code s v saved expectedWidth data address capacity used h
          count hc hle ve r reserved rfl flags
        intro t anchors own frame cursor pair
        have alloc : allocation expectedWidth data address capacity used = some r := by
          rw [allocation, ite_eq_left ⟨heq, by dsimp [count] at hc; omega⟩]
          exact reserved
        apply success_cont e base code s t saved expectedWidth data address capacity used h
          anchors own heq
        · rintro ⟨_, _, failed⟩
          rw [reserved] at failed
          contradiction
        · simpa only [alloc] using frame
        · simpa only [alloc] using cursor
        · exact pair
  · simp only [matched, ↓reduceIte] at wx
    rcases wx with ⟨rfl, hp, hn, _⟩
    exact scope_cont e base code s u saved expectedWidth data address capacity used h wf wr14
      (fun he => matched (he.trans h.length)) hp hn

/-- The frame protects every initial read-only region, including the full
original source, descriptor header and all borrowed Large descriptor limbs. -/
theorem preserves_region (s : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (t : MachineState) (post : Post s saved expectedWidth data address capacity used t)
    (p n : Nat) (hp : Protected s address capacity used p n) :
    ∀ i < n, t.1.dmem.get? (BitVec.ofNat 64 (p + i)) =
      s.dmem.get? (BitVec.ofNat 64 (p + i)) := by
  intro i hi
  have hb : p + i < 2^64 := by have := hp.bound; omega
  apply post.frame
  · simp only [Outside, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    have hd := hp.output
    unfold Apart at hd
    omega
  · simp only [Outside, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    have hd := hp.work
    unfold Apart at hd
    omega
  · intro r hr
    unfold allocation at hr
    split at hr
    · rename_i matched
      have rf := reservation_facts s saved expectedWidth data address capacity used h
        (significantBytes data data.size) (by omega) r hr
      constructor
      · intro j hj
        have hd := hp.cursor
        have hh := h.header.nonwrap
        unfold Apart at hd
        simp only [← UInt64.toNat_toBitVec] at hd hh
        bv_omega
      · intro j hj
        have hd := hp.arena
        have hlo := rf.lower
        have hhi := rf.inside
        have hav := rf.available
        have ha := h.arena_bound
        have hrb := rf.pointer_bound
        unfold Apart at hd
        bv_omega
    · contradiction

theorem source_preserved (s : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (t : MachineState) (post : Post s saved expectedWidth data address capacity used t) :
    ∀ i < data.size, t.1.dmem.get? (s.regs.rdx.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rdx.toBitVec + BitVec.ofNat 64 i) := by
  intro i hi
  simpa only [← UInt64.toNat_toBitVec, width_address] using preserves_region s saved expectedWidth data address capacity used
    h t post _ _ h.source_owned i hi

theorem descriptor_preserved (s : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (t : MachineState) (post : Post s saved expectedWidth data address capacity used t) :
    ∀ i < 24, t.1.dmem.get? (s.regs.rbp.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rbp.toBitVec + BitVec.ofNat 64 i) := by
  intro i hi
  simpa only [← UInt64.toNat_toBitVec, width_address] using preserves_region s saved expectedWidth data address capacity used
    h t post _ _ h.descriptor i hi

theorem borrowed_preserved (s : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (t : MachineState) (post : Post s saved expectedWidth data address capacity used t)
    (p : Nat) (words : List (BitVec 64))
    (hw : NatMemory.largeAt (widthLoad s.dmem) (s.regs.rbp.toNat + 8) p words) :
    ∀ i < 8 * words.length, t.1.dmem.get? (BitVec.ofNat 64 (p + i)) =
      s.dmem.get? (BitVec.ofNat 64 (p + i)) := by
  rcases h.borrowed p words hw with hz | hp
  · subst words
    simp
  · exact preserves_region s saved expectedWidth data address capacity used h t post _ _ hp

end SszX86.UintCodec.Body
