import SszArm.UintAllocation
import SszArm.UintLarge
import SszArm.UintPrefixCompletion

namespace SszArm.UintCodec.Allocated

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Physical ownership of the arena's available suffix. Inputs and existing
objects may occupy the used prefix. Empty available or input spans impose no
separation. These are initial address facts, not a promise that allocation fits. -/
structure Storage (s : ArmState) (data : Ssz.Bytes) : Prop where
  valid : SszNative.Arena.Valid (arenaBase s).toNat (arenaCapacity s).toNat (arenaUsed s).toNat
  source : (arenaUsed s).toNat = (arenaCapacity s).toNat ∨ data.size = 0 ∨
    (arenaBase s).toNat + (arenaCapacity s).toNat ≤ (r (.GPR 2) s).toNat ∨
    (r (.GPR 2) s).toNat + data.size ≤ (arenaBase s).toNat + (arenaUsed s).toNat
  output : (arenaUsed s).toNat = (arenaCapacity s).toNat ∨
    (arenaBase s).toNat + (arenaCapacity s).toNat ≤ (r (.GPR 0) s).toNat ∨
    (r (.GPR 0) s).toNat + 80 ≤ (arenaBase s).toNat + (arenaUsed s).toNat
  stack : (arenaUsed s).toNat = (arenaCapacity s).toNat ∨
    (arenaBase s).toNat + (arenaCapacity s).toNat ≤ (r (.GPR 31) s).toNat - 16 ∨
    (r (.GPR 31) s).toNat + 368 ≤ (arenaBase s).toNat + (arenaUsed s).toNat
  header : (arenaUsed s).toNat = (arenaCapacity s).toNat ∨
    (arenaBase s).toNat + (arenaCapacity s).toNat ≤ (r (.GPR 19) s).toNat ∨
    (r (.GPR 19) s).toNat + 24 ≤ (arenaBase s).toNat + (arenaUsed s).toNat

/-- Caller memory ownership. An empty arena needs no backing pointer or backing
separation: capacity and cursor are zero. Otherwise the ordinary `Storage`
facts apply. In particular, no successful reservation is required. The arena
header is separate from input, output and the entire stack activation. -/
structure Owned (s : ArmState) (data : Ssz.Bytes) : Prop where
  tail : Tail.Separated s
  headerHigh : (r (.GPR 19) s).toNat + 24 ≤ 2^64
  headerStack : (r (.GPR 19) s).toNat + 24 ≤ (r (.GPR 31) s).toNat - 16 ∨
    (r (.GPR 31) s).toNat + 368 ≤ (r (.GPR 19) s).toNat
  headerSource : data.size = 0 ∨
    (r (.GPR 19) s).toNat + 24 ≤ (r (.GPR 2) s).toNat ∨
    (r (.GPR 2) s).toNat + data.size ≤ (r (.GPR 19) s).toNat
  headerOutput : (r (.GPR 19) s).toNat + 24 ≤ (r (.GPR 0) s).toNat ∨
    (r (.GPR 0) s).toNat + 80 ≤ (r (.GPR 19) s).toNat
  storage : ((arenaCapacity s).toNat = 0 ∧ (arenaUsed s).toNat = 0) ∨ Storage s data

def reservation (s : ArmState) (count : Nat) : Option SszNative.Arena.Reservation :=
  SszNative.Arena.reserve (arenaBase s).toNat (arenaCapacity s).toNat
    (arenaUsed s).toNat (SszNative.Arena.wordsForBytes count)

/-- On success only the committed cursor and actual limb destination are added
to the permitted footprint. Alignment padding and unused backing stay framed. -/
def ExtraOutside (s : ArmState) (count : Nat)
    (result : Option SszNative.Arena.Reservation) (a : BitVec 64) : Prop :=
  match result with
  | none => True
  | some q =>
    (a.toNat < (r (.GPR 19) s).toNat + 16 ∨ (r (.GPR 19) s).toNat + 24 ≤ a.toNat) ∧
    (a.toNat < q.pointer ∨ q.pointer + 8 * SszNative.Arena.wordsForBytes count ≤ a.toNat)

def Frame (s t : ArmState) (count : Nat) (result : Option SszNative.Arena.Reservation) : Prop :=
  ∀ a : BitVec 64,
    (a.toNat < (r (.GPR 0) s).toNat ∨ (r (.GPR 0) s).toNat + 76 ≤ a.toNat) →
    (a.toNat < (r (.GPR 31) s).toNat - 16 ∨ (r (.GPR 31) s).toNat + 192 ≤ a.toNat) →
    ExtraOutside s count result a → t.mem a = s.mem a

/-- Return observations refer to the original activation, not the post-allocation
state. The separate frame permits precisely the successful reservation writes. -/
structure Returned (s t : ArmState) (count : Nat)
    (result : Option SszNative.Arena.Reservation) : Prop where
  pc : read_pc t = read_mem_bytes 8 (r (.GPR 31) s + 280#64) s
  sp : r (.GPR 31) t = r (.GPR 31) s + 368#64
  registers : ∀ reg offset, (reg, offset) ∈ BoolCodec.savedRegisters →
    r (.GPR reg) t = read_mem_bytes 8 (r (.GPR 31) s + BitVec.ofNat 64 offset) s
  activation : BoolCodec.ActivationPreserved s t
  frame : Frame s t count result

/-- The allocating path has an explicit resource result, not an upstream error. -/
def Observation (s t : ArmState) (data : Ssz.Bytes)
    (result : Option SszNative.Arena.Reservation) : Prop :=
  match result with
  | none => SszNative.UintCodec.scratchExhaustedAt (widthLoad t) (r (.GPR 0) s).toNat
  | some _ => SszNative.UintCodec.ResultAt (widthLoad t) (r (.GPR 0) s).toNat
      (.ok (.uint (Ssz.readUint data 0 data.size)))

theorem Owned.outside_spill {s : ArmState} {data : Ssz.Bytes} (h : Owned s data) :
    ArenaOutsideSpill s :=
  ⟨h.headerHigh, by
    have hs := h.headerStack
    change (r (.GPR 19) s).toNat + 24 ≤ (r (.GPR 31) s).toNat - 16 ∨
      (r (.GPR 31) s).toNat ≤ (r (.GPR 19) s).toNat
    omega⟩

theorem Owned.header_stable {s t : ArmState} {data : Ssz.Bytes}
    (h : Owned s data) (hs : Small.Stable s t) (offset : Nat) (ho : offset ≤ 16) :
    read_mem_bytes 8 (r (.GPR 19) t + BitVec.ofNat 64 offset) t =
      read_mem_bytes 8 (r (.GPR 19) s + BitVec.ofNat 64 offset) s := by
  rw [hs.regs 19 (by decide)]
  apply BoolCodec.read_bytes_congr
  intro i hi
  apply hs.frame
  have := h.headerHigh
  have := h.headerStack
  bv_omega

theorem Owned.arena_stable {s t : ArmState} {data : Ssz.Bytes}
    (h : Owned s data) (hs : Small.Stable s t) :
    arenaBase t = arenaBase s ∧ arenaCapacity t = arenaCapacity s ∧ arenaUsed t = arenaUsed s := by
  refine ⟨?_, h.header_stable hs 8 (by decide), h.header_stable hs 16 (by decide)⟩
  have hb := h.header_stable hs 0 (by decide)
  change read_mem_bytes 8 (r (.GPR 19) t + 0#64) t =
    read_mem_bytes 8 (r (.GPR 19) s + 0#64) s at hb
  change read_mem_bytes 8 (r (.GPR 19) t) t = read_mem_bytes 8 (r (.GPR 19) s) s
  simpa only [BitVec.add_zero] using hb

theorem Owned.stable {s t : ArmState} {data : Ssz.Bytes}
    (h : Owned s data) (hs : Small.Stable s t) : Owned t data := by
  have h0 := hs.regs 0 (by decide)
  have h2 := hs.regs 2 (by decide)
  have h19 := hs.regs 19 (by decide)
  have h31 := hs.regs 31 (by decide)
  obtain ⟨hb, hc, hu⟩ := h.arena_stable hs
  refine ⟨hs.tail_separated h.tail, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [h19] using h.headerHigh
  · simpa only [h19, h31] using h.headerStack
  · simpa only [h19, h2] using h.headerSource
  · simpa only [h19, h0] using h.headerOutput
  · rcases h.storage with he | hv
    · exact Or.inl (by simpa only [hc, hu] using he)
    · exact Or.inr ⟨by simpa only [hb, hc, hu] using hv.valid,
        by simpa only [hb, hc, hu, h2] using hv.source,
        by simpa only [hb, hc, hu, h0] using hv.output,
        by simpa only [hb, hc, hu, h31] using hv.stack,
        by simpa only [hb, hc, hu, h19] using hv.header⟩

theorem Owned.reservation_stable {s t : ArmState} {data : Ssz.Bytes}
    (h : Owned s data) (hs : Small.Stable s t) (count : Nat) :
    reservation t count = reservation s count := by
  obtain ⟨hb, hc, hu⟩ := h.arena_stable hs
  simp only [reservation, hb, hc, hu]

theorem Returned.prepend {s t u : ArmState} {data : Ssz.Bytes} {count : Nat}
    {result : Option SszNative.Arena.Reservation} (h : Owned s data)
    (hs : Small.Stable s t) (hr : Returned t u count result) : Returned s u count result := by
  have h0 := hs.regs 0 (by decide)
  have h19 := hs.regs 19 (by decide)
  have h31 := hs.regs 31 (by decide)
  have hact := Tail.frame_activation s t h.tail hs.tail_frame
  have hword (offset : Nat) (hb : offset + 8 ≤ 96) :=
    BoolCodec.activation_word s t offset hact hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.pc, h31]
    simpa only [Nat.reduceAdd] using hword 8 (by decide)
  · rw [hr.sp, h31]
  · intro reg offset hm
    rw [hr.registers reg offset hm, h31]
    have hb := BoolCodec.savedRegister_bounds reg offset hm
    have hw := hword (offset - 272) (by omega)
    simpa only [show 272 + (offset - 272) = offset by omega] using hw
  · intro i hi
    have hu := hr.activation i hi
    change read_mem (r (.GPR 31) t + BitVec.ofNat 64 (272+i)) u =
      read_mem (r (.GPR 31) t + BitVec.ofNat 64 (272+i)) t at hu
    rw [h31] at hu
    exact hu.trans (hact i hi)
  · intro a ho hw he
    exact (hr.frame a (by simpa only [h0] using ho) (by simpa only [h31] using hw)
      (by simpa only [ExtraOutside, h19] using he)).trans (hs.tail_frame a ho hw)

theorem Owned.success_storage {s : ArmState} {data : Ssz.Bytes} (h : Owned s data)
    (count : Nat) (hn : 0 < count) (q : SszNative.Arena.Reservation)
    (hq : reservation s count = some q) : Storage s data := by
  rcases h.storage with he | hv
  · have hw : 0 < SszNative.Arena.wordsForBytes count := by
      have := (SszNative.Arena.wordsForBytes_bounds count).1
      omega
    have hc := ((SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ hw q).mp hq).1
    have hf := hc.2.2.2.2.2
    dsimp [SszNative.Arena.finish] at hf
    omega
  · exact hv

/-- Memory effect of allocation alone: one lowering spill, and on success the
single cursor commit. This follows from the checked allocation effect. -/
theorem allocation_frame {s t : ArmState} {data : Ssz.Bytes} {base : BitVec 64} {count : Nat}
    (h : Owned s data) (ha : AllocationResult s t base count) :
    ∀ a : BitVec 64,
      (a.toNat < (r (.GPR 31) s).toNat - 16 ∨ (r (.GPR 31) s).toNat ≤ a.toNat) →
      (match reservation s count with
       | none => True
       | some _ => a.toNat < (r (.GPR 19) s).toNat + 16 ∨
           (r (.GPR 19) s).toNat + 24 ≤ a.toNat) → t.mem a = s.mem a := by
  intro a hs hh
  have hlo := h.tail.stackLow
  have hheader := h.headerHigh
  have heffect := ha.2.2.2.1
  change (match reservation s count with | none => _ | some _ => _) at heffect
  cases hr : reservation s count with
  | none =>
    simp only [hr] at heffect
    rw [heffect.2]
    apply BoolCodec.write_mem_bytes_frame <;> bv_omega
  | some q =>
    simp only [hr] at heffect hh
    rw [heffect.2.2.2.1]
    rw [BoolCodec.write_mem_bytes_frame (hspace := by bv_omega) (ha := by bv_omega)]
    apply BoolCodec.write_mem_bytes_frame <;> bv_omega

/-- Activation preservation follows from the exact footprint and ordinary
initial ownership, including separation of the actual successful suballocation. -/
theorem frame_activation {s t : ArmState} {data : Ssz.Bytes} {count : Nat}
    (h : Owned s data) (hn : 0 < count) (hf : Frame s t count (reservation s count)) :
    BoolCodec.ActivationPreserved s t := by
  intro i hi
  change t.mem (r (.GPR 31) s + BitVec.ofNat 64 (272+i)) =
    s.mem (r (.GPR 31) s + BitVec.ofNat 64 (272+i))
  have hhi := h.tail.stackHigh
  have hout := h.tail.activation
  apply hf
  · bv_omega
  · bv_omega
  · cases hq : reservation s count with
    | none => trivial
    | some q =>
      have hv := h.success_storage count hn q hq
      have hw : 0 < SszNative.Arena.wordsForBytes count := by
        have := (SszNative.Arena.wordsForBytes_bounds count).1
        omega
      obtain ⟨_, _, _, hused, hcapacity, hlo, _, hupper, _⟩ :=
        SszNative.Arena.success_properties _ _ _ _ hv.valid hw q hq
      have hh := h.headerStack
      have hb := hv.stack
      constructor <;> bv_omega

/-- Transport the checked tail return across allocation and fill, retaining the
entry activation. No execution or final-memory premise enters the caller API. -/
theorem returned_of_tail {s t u : ArmState} {data : Ssz.Bytes} {count : Nat}
    (h : Owned s data) (hn : 0 < count)
    (h0 : r (.GPR 0#5) t = r (.GPR 0#5) s)
    (h31 : r (.GPR 31#5) t = r (.GPR 31#5) s)
    (hf : Frame s t count (reservation s count)) (hr : Tail.Returned t u) :
    Returned s u count (reservation s count) := by
  have hact := frame_activation h hn hf
  have hword (offset : Nat) (hb : offset + 8 ≤ 96) :=
    BoolCodec.activation_word s t offset hact hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change read_pc u = read_mem_bytes 8 (r (.GPR 31#5) s + 280#64) s
    rw [hr.pc, h31]
    simpa only [BitVec.ofNat_eq_ofNat, Nat.reduceAdd] using hword 8 (by decide)
  · change r (.GPR 31#5) u = r (.GPR 31#5) s + 368#64
    rw [hr.sp, h31]
  · intro reg offset hm
    rw [hr.registers reg offset hm, h31]
    have hb := BoolCodec.savedRegister_bounds reg offset hm
    have hw := hword (offset - 272) (by omega)
    simpa only [BitVec.ofNat_eq_ofNat, show 272 + (offset - 272) = offset by omega] using hw
  · intro i hi
    have hu := hr.activation i hi
    change read_mem (r (.GPR 31#5) t + BitVec.ofNat 64 (272+i)) u =
      read_mem (r (.GPR 31#5) t + BitVec.ofNat 64 (272+i)) t at hu
    rw [h31] at hu
    exact hu.trans (hact i hi)
  · intro a ho hw he
    exact (hr.frame a (by simpa only [BitVec.ofNat_eq_ofNat, h0] using ho)
      (by simpa only [BitVec.ofNat_eq_ofNat, h31] using hw)).trans (hf a ho hw he)

end SszArm.UintCodec.Allocated
