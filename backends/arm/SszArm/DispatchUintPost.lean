import SszArm.DispatchUintOwned

namespace SszArm.Dispatch.Unsigned

open UintCodec (widthLoad)

def count (data : Ssz.Bytes) := SszNative.WordDecode.significantBytes data data.size

def reservation (s : ArmState) (width : Nat) (data : Ssz.Bytes) : Option SszNative.Arena.Reservation :=
  if UintCodec.Body.needsAllocation width data then
    SszNative.Arena.reserve (arenaBase s).toNat (arenaCapacity s).toNat (arenaUsed s).toNat
      (SszNative.Arena.wordsForBytes (count data))
  else none

theorem Owned.reservation {s : ArmState} {width : Nat} {data : Ssz.Bytes} (owned : Owned s width data) :
    UintCodec.Body.reservation (entered s .uint) width data = Unsigned.reservation s width data := by
  obtain ⟨base, capacity, used⟩ := owned.arena
  simp only [UintCodec.Body.reservation, UintCodec.Allocated.reservation,
    Unsigned.reservation, count, base, capacity, used]

def ExtraOutside (s : ArmState) (width : Nat) (data : Ssz.Bytes) (a : BitVec 64) : Prop :=
  match reservation s width data with
  | none => True
  | some q =>
    (a.toNat < (r (.GPR 4#5) s).toNat + 16 ∨ (r (.GPR 4#5) s).toNat + 24 ≤ a.toNat) ∧
    (a.toNat < q.pointer ∨ q.pointer + 8 * SszNative.Arena.wordsForBytes (count data) ≤ a.toNat)

theorem Owned.geometry {s : ArmState} {width : Nat} {data : Ssz.Bytes}
    (owned : Owned s width data) (q : SszNative.Arena.Reservation)
    (allocated : Unsigned.reservation s width data = some q) :
    (arenaBase s).toNat + (arenaUsed s).toNat ≤ q.pointer ∧
    q.pointer + 8 * SszNative.Arena.wordsForBytes (count data) ≤
      (arenaBase s).toNat + (arenaCapacity s).toNat ∧
    (arenaUsed s).toNat < (arenaCapacity s).toNat := by
  have needs : UintCodec.Body.needsAllocation width data := by
    by_cases needs : UintCodec.Body.needsAllocation width data
    · exact needs
    · simp [Unsigned.reservation, needs] at allocated
  have positive : 0 < count data := by have large := needs.2; unfold count; omega
  have wordsPositive : 0 < SszNative.Arena.wordsForBytes (count data) := by
    have bound := (SszNative.Arena.wordsForBytes_bounds (count data)).1
    omega
  have bodyAllocated : UintCodec.Allocated.reservation (entered s .uint) (count data) = some q := by
    have same := owned.reservation.trans allocated
    simpa only [UintCodec.Body.reservation, needs, ↓reduceIte, count] using same
  have storage := owned.body.success_storage (count data) positive q bodyAllocated
  obtain ⟨_, _, _, usedStrict, usedBound, low, _, high, _⟩ :=
    SszNative.Arena.success_properties _ _ _ _ storage.valid wordsPositive q bodyAllocated
  obtain ⟨base, capacity, used⟩ := owned.arena
  simp only [base, capacity, used] at usedStrict usedBound low high
  exact ⟨low, high, by omega⟩

/-- The full accepted native body result is retained (including exhaustion,
committed cursor and actual allocated extent), with original caller ABI/frame. -/
structure NativePost (s t : ArmState) (width : Nat) (data : Ssz.Bytes) : Prop where
  body : UintCodec.Body.Result (entered s .uint) t width data
  pc : read_pc t = r (.GPR 30#5) s
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg offset, (reg, offset) ∈ BoolCodec.savedRegisters → r (.GPR reg) t = r (.GPR reg) s
  cursor : read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t =
    match reservation s width data with | none => arenaUsed s | some q => BitVec.ofNat 64 q.used
  frame : ∀ a : BitVec 64,
    (a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat) →
    (a.toNat < (r (.GPR 31#5) s).toNat - 384 ∨ (r (.GPR 31#5) s).toNat - 176 ≤ a.toNat) →
    (a.toNat < (r (.GPR 31#5) s).toNat - 96 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) →
    ExtraOutside s width data a → t.mem a = s.mem a
  inputBytes : ∀ a : BitVec 64, (r (.GPR 2#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 2#5) s).toNat + data.size → t.mem a = s.mem a
  descriptorBytes : ∀ a : BitVec 64, (r (.GPR 1#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 1#5) s).toNat + 24 → t.mem a = s.mem a

theorem native_post_of_body {s t : ArmState} {width : Nat} {data : Ssz.Bytes}
    (owned : Owned s width data) (post : UintCodec.Body.Result (entered s .uint) t width data) :
    NativePost s t width data := by
  have wholeFrame : ∀ a : BitVec 64,
      (a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat) →
      (a.toNat < (r (.GPR 31#5) s).toNat - 384 ∨ (r (.GPR 31#5) s).toNat - 176 ≤ a.toNat) →
      (a.toNat < (r (.GPR 31#5) s).toNat - 96 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) →
      ExtraOutside s width data a → t.mem a = s.mem a := by
    intro a out scratch activation extra
    apply (post.returned.frame a (by simpa using out) ?_ ?_).trans
      (entered_frame s .uint owned.scalar.entry.stackLow a activation)
    · have low := owned.scalar.stackLow
      simp only [BitVec.ofNat_eq_ofNat, entered_sp, bodySP]
      bv_omega
    · cases allocated : reservation s width data <;>
        simpa [UintCodec.Allocated.ExtraOutside, ExtraOutside, count, owned.reservation, allocated] using extra
  refine ⟨post, ?_, ?_, ?_, ?_, wholeFrame, ?_, ?_⟩
  · exact post.returned.pc.trans (by
      simpa using entered_saved s .uint owned.scalar.entry.stackLow 30#5 280 (by decide))
  · simpa only [BitVec.ofNat_eq_ofNat, entered_sp, bodySP, BitVec.sub_add_cancel] using post.returned.sp
  · intro reg offset member
    exact (post.returned.registers reg offset member).trans (by
      simpa using entered_saved s .uint owned.scalar.entry.stackLow reg offset member)
  · cases allocated : reservation s width data with
    | none =>
      have cursor := post.cursor
      simp only [UintCodec.Allocated.CursorAt, owned.reservation, allocated] at cursor
      change read_mem_bytes 8 (r (.GPR 19#5) (entered s .uint) + 16#64) t =
        UintCodec.arenaUsed (entered s .uint) at cursor
      rw [owned.arena.2.2] at cursor
      simpa only [allocated, entered_arena] using cursor
    | some q =>
      simpa [UintCodec.Allocated.CursorAt, owned.reservation, allocated] using post.cursor
  · intro a low high
    apply wholeFrame a
    · have out := owned.scalar.inputOutput; omega
    · have stack := owned.scalar.inputStack; omega
    · have stack := owned.scalar.inputStack; omega
    · cases allocated : reservation s width data with
      | none => simp only [ExtraOutside, allocated]
      | some q =>
        obtain ⟨freshLow, freshHigh, notFull⟩ := owned.geometry q allocated
        simp only [ExtraOutside, allocated]
        constructor
        · have separate := owned.headerSource; omega
        · rcases owned.storage with empty | storage
          · omega
          · have separate := storage.source; omega
  · intro a low high
    apply wholeFrame a
    · have out := owned.scalar.descriptorOutput; omega
    · have stack := owned.scalar.descriptorStack; omega
    · have stack := owned.scalar.descriptorStack; omega
    · cases allocated : reservation s width data with
      | none => simp only [ExtraOutside, allocated]
      | some q =>
        obtain ⟨freshLow, freshHigh, notFull⟩ := owned.geometry q allocated
        simp only [ExtraOutside, allocated]
        constructor
        · have separate := owned.descriptorHeader; omega
        · have separate := owned.descriptorStorage; omega

end SszArm.Dispatch.Unsigned
