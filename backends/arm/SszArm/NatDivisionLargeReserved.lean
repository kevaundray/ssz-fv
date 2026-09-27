import SszArm.NatDivisionLargePost
import SszArm.NatDivisionLargeEntry
import SszArm.NatDivisionArenaInput

namespace SszArm.NatDivision

open Delimited (MemoryFrame Protected)
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Execute every successful large reservation guard and cursor commit, then
copy, divide, normalize, serialize, restore the original activation, and RET. -/
theorem large_guard_reserved_post (original s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (reservation : SszNative.Arena.Reservation)
    (owned : Owned original (.large pointer words)) (saved : Saved original s)
    (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (arena : r (.GPR 21#5) s = r (.GPR 4#5) original)
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 168#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 (sigWords words))
    (h20 : r (.GPR 20#5) s = r (.GPR 3#5) original)
    (h22 : r (.GPR 22#5) s = BitVec.ofNat 64 (sigWords words + 1))
    (h23 : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * (sigWords words - 1)))
    (count : 2 < sigWords words)
    (reserve : SszNative.Arena.reserve (arenaOf original).base (arenaOf original).capacity
      (arenaOf original).used (sigWords words) = some reservation)
    (before : MemoryFrame (localWrites original) original s) :
    ∃ fuel, Post original (run fuel s) (.large pointer words) := by
  let address := read_mem_bytes 8 (r (.GPR 4#5) original) original
  let capacity := read_mem_bytes 8 (r (.GPR 4#5) original + 8#64) original
  let used := read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) original
  have hbase : read_mem_bytes 8 (r (.GPR 21#5) s) s = address := by
    simpa [address] using local_arena_word owned before arena 0 (by decide)
  have hcapacity : read_mem_bytes 8 (r (.GPR 21#5) s + 8#64) s = capacity := by
    simpa [capacity] using local_arena_word owned before arena 8 (by decide)
  have hused : read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) s = used := by
    simpa [used] using local_arena_word owned before arena 16 (by decide)
  have countNat : (r (.GPR 8#5) s).toNat = sigWords words := by
    rw [h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt owned.large_count_bound]
  have reserve' : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
      (r (.GPR 8#5) s).toNat = some reservation := by rw [countNat]; exact reserve
  have source := SszNative.NatDivision.phase_reserved (.large pointer words) (r (.GPR 3#5) original)
    (arenaOf original).base (arenaOf original).capacity (arenaOf original).used
    owned.divisor_nonzero owned.divisor_ne_one count reservation reserve
  have allocated : (outcome original (.large pointer words)).allocation = some reservation := by rw [source]
  have stack := owned.stackBound
  have headerBound := owned.arenaBound
  have slot : (r (.GPR 31#5) s).toNat - 16 = (r (.GPR 31#5) original).toNat - 80 := by
    rw [saved.sp]
    bv_omega
  have physical : ∀ offset ∈ [0#64, 8#64, 16#64],
      (r (.GPR 21#5) s + offset).toNat + 8 ≤ 2^64 := by
    intro offset member
    rw [arena]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> bv_omega
  have apart : (r (.GPR 4#5) original).toNat + 24 ≤ (r (.GPR 31#5) original).toNat - 80 ∨
      (r (.GPR 31#5) original).toNat ≤ (r (.GPR 4#5) original).toNat := by
    rcases owned.arenaLocal with empty | separate
    · omega
    · have h := separate ((r (.GPR 31#5) original).toNat - 80, 80) (by simp [localWrites])
      simp only [Prod.fst, Prod.snd] at h
      omega
  have headerOwned : ∀ offset ∈ [0#64, 8#64, 16#64],
      Protected [((r (.GPR 31#5) s).toNat - 16, 16)]
        (r (.GPR 21#5) s + offset).toNat 8 := by
    intro offset member
    right
    intro span present
    simp only [List.mem_singleton] at present
    subst span
    rw [arena, slot]
    simp only [Prod.fst, Prod.snd, List.mem_cons, List.not_mem_nil, or_false] at *
    rcases member with rfl | rfl | rfl <;> bv_omega
  obtain ⟨fuel, t, executed, post⟩ := arena_big_reservation_runs s base address capacity used
    hc.1 he ha hp (by rw [saved.sp]; bv_omega) (by rw [countNat]; omega)
    hbase hcapacity hused physical headerOwned
  rcases post with early | ⟨u, frame, memory, later, countU⟩
  · rw [reserve'] at early
    cases early.1
  · have header : r (.GPR 21#5) u = r (.GPR 4#5) original :=
      (frame.registers 21#5 (by decide)).trans arena
    have cursorPhysical : (r (.GPR 21#5) u + 16#64).toNat + 8 ≤ 2^64 := by
      rw [header]
      bv_omega
    have commit := arena_big_reservation_memory base address capacity used
      (r (.GPR 8#5) s).toNat later cursorPhysical
    rw [reserve'] at commit
    obtain ⟨pc, countT, zero, destination, program, error, vectors, registers⟩ :=
      arena_big_reservation_success_registers base address capacity used
        (r (.GPR 8#5) s).toNat later reservation reserve'
    have prefixBody : MemoryFrame (bodyWrites original (.large pointer words)) s u := by
      apply memory.weaken
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      simp [bodyWrites, allocated, slot]
    have cursorAddress : (r (.GPR 21#5) u + 16#64).toNat =
        (r (.GPR 4#5) original).toNat + 16 := by rw [header]; bv_omega
    have commitBody : MemoryFrame (bodyWrites original (.large pointer words)) u t := by
      apply commit.1.weaken
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      simp [bodyWrites, allocated, cursorAddress]
    have body := prefixBody.trans commitBody
    have keep (reg : BitVec 5) (outside : reg ∉ [8#5, 9#5, 10#5, 11#5, 12#5, 13#5, 24#5]) :
        r (.GPR reg) t = r (.GPR reg) s := by
      have guards : reg ∉ [8#5, 9#5, 10#5, 11#5, 12#5, 13#5] := by simp_all
      exact (registers reg outside).trans (frame.registers reg guards)
    have savedT : Saved original t := by
      apply saved.body_preserved owned body (keep 31#5 (by decide))
      · intro reg low high
        apply keep
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        bv_omega
      · intro reg low high
        exact congrArg (BitVec.setWidth 64) ((vectors reg).trans (frame.vectors reg))
    have codeT : JointCodeAt t base := by
      simpa only [JointCodeAt, CodeAt, Udivti3.CodeAt, SszArm.CodeAt, program, frame.program] using hc
    have errorT : read_err t = .None := error.trans (frame.error.trans he)
    have alignedT : CheckSPAlignment t := by
      simpa only [CheckSPAlignment, state_simp_rules, keep 31#5 (by decide)] using ha
    have cursor : (read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) t).toNat = reservation.used := by
      simpa only [header] using commit.2
    obtain ⟨more, final⟩ := large_reserved_post original t base pointer words reservation owned savedT
      ((keep 19#5 (by decide)).trans out) codeT errorT alignedT pc
      ((keep 1#5 (by decide)).trans h1) ((keep 2#5 (by decide)).trans h2)
      (countT.trans (countU.trans h8)) zero ((keep 20#5 (by decide)).trans h20)
      ((keep 22#5 (by decide)).trans h22) ((keep 23#5 (by decide)).trans h23)
      destination count reserve cursor
      ((local_frame (outcome original (.large pointer words)) before).trans
        (body_frame_full (.large pointer words) body))
    refine ⟨fuel + more, ?_⟩
    rw [run_plus, executed]
    exact final

end SszArm.NatDivision
