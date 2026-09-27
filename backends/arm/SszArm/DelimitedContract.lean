import SszArm.DelimitedOption
import SszArm.DelimitedTailMemory
import SszArm.DelimitedCalls
import SszArm.DelimitedResults
import SszDelimitedProofs

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Read the caller's three native arena words, without a signed-size restriction. -/
def arenaOf (s : ArmState) : SszNative.Delimited.ArenaState :=
  ⟨(read_mem_bytes 8 (r (.GPR 4#5) s) s).toNat,
   (read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s).toNat,
   (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s).toNat⟩

/-- ISA geometry only: alignment padding and the already-used prefix are absent. -/
def writesFor (s : ArmState) : Option SszNative.Arena.Reservation → List Span
  | none => localWrites s
  | some reservation => allocatedWrites s reservation.pointer

structure Owned (s : ArmState) (limit : Option Nat) (data : Ssz.Bytes) : Prop where
  length : (r (.GPR 3#5) s).toNat = data.size
  inputBound : (r (.GPR 2#5) s).toNat + data.size ≤ 2^64
  input : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 2#5) s).toNat data
  optionBound : (r (.GPR 1#5) s).toNat + 24 ≤ 2^64
  option : SszNative.NatMemory.OptionAt (widthLoad s) (r (.GPR 1#5) s).toNat limit
  outputBound : (r (.GPR 0#5) s).toNat + 76 ≤ 2^64
  stackBound : (activationSpan s).2 ≤ (r (.GPR 31#5) s).toNat
  outputStack : Protected [activationSpan s] (r (.GPR 0#5) s).toNat 76
  arenaBound : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64
  arenaStorage : (arenaOf s).base + (arenaOf s).capacity ≤ 2^64
  arenaNonnull : 0 < (arenaOf s).capacity → 0 < (arenaOf s).base
  arenaLocal : Protected (localWrites s) (r (.GPR 4#5) s).toNat 24
  fresh : ∀ reservation,
    SszNative.Delimited.allocation data (arenaOf s) = some reservation →
    Protected (localWrites s ++ [((r (.GPR 4#5) s).toNat, 24)]) reservation.pointer 16
  inputOwned : Protected (writesFor s (SszNative.Delimited.allocation data (arenaOf s)))
    (r (.GPR 2#5) s).toNat data.size
  optionOwned : OptionOwned (writesFor s (SszNative.Delimited.allocation data (arenaOf s)))
    s (r (.GPR 1#5) s) limit

theorem Owned.physical {s : ArmState} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s limit data) : data.size < 2^64 := by
  rw [← owned.length]
  exact (r (.GPR 3#5) s).isLt

theorem MemoryFrame.weaken {small large : List Span} {s t : ArmState}
    (frame : MemoryFrame small s t) (included : ∀ span ∈ small, span ∈ large) :
    MemoryFrame large s t := by
  intro a outside
  exact frame a (fun span member => outside span (included span member))

theorem MemoryFrame.protected_byte {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) {address bytes : Nat}
    (owned : Protected writes address bytes) (a : BitVec 64)
    (low : address ≤ a.toNat) (high : a.toNat < address + bytes) : t.mem a = s.mem a := by
  apply frame
  intro span member
  rcases owned with empty | separate
  · omega
  · have apart := separate span member
    omega

theorem local_frame {s t : ArmState} (allocation : Option SszNative.Arena.Reservation)
    (frame : MemoryFrame (localWrites s) s t) : MemoryFrame (writesFor s allocation) s t := by
  apply frame.weaken
  intro span member
  cases allocation <;> simp_all [writesFor, allocatedWrites]

/-- Original readonly observations are retained, including noncanonical cap limbs. -/
structure InputsPreserved (s t : ArmState) (limit : Option Nat) (data : Ssz.Bytes) : Prop where
  input : SszNative.ByteView.BytesAt (widthLoad t) (r (.GPR 2#5) s).toNat data
  option : SszNative.NatMemory.OptionAt (widthLoad t) (r (.GPR 1#5) s).toNat limit
  descriptor : read_mem_bytes 24 (r (.GPR 1#5) s) t = read_mem_bytes 24 (r (.GPR 1#5) s) s
  limbs : ∀ value, limit = some value →
    let pointer := read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s
    let payload := read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s
    ∀ a : BitVec 64, pointer ≠ 0#64 → pointer.toNat ≤ a.toNat →
      a.toNat < pointer.toNat + 8 * payload.toNat → t.mem a = s.mem a

theorem inputs_preserved {s t : ArmState} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s limit data)
    (frame : MemoryFrame (writesFor s (SszNative.Delimited.allocation data (arenaOf s))) s t) :
    InputsPreserved s t limit data := by
  have header : Protected (writesFor s (SszNative.Delimited.allocation data (arenaOf s)))
      (r (.GPR 1#5) s).toNat 24 := by
    cases limit with
    | none => exact owned.optionOwned
    | some value => exact owned.optionOwned.1
  refine ⟨frame.bytes _ _ owned.inputBound owned.inputOwned owned.input,
    option_preserved frame _ _ owned.optionBound owned.option owned.optionOwned,
    frame.read _ _ owned.optionBound header, ?_⟩
  intro value limitEq
  subst limit
  dsimp only
  intro a nonzero low high
  have countNonzero : read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s ≠ 0#64 := by
    intro zero
    simp only [zero, BitVec.toNat_ofNat, Nat.mul_zero, Nat.add_zero] at high
    omega
  exact frame.protected_byte (owned.optionOwned.2 nonzero countNonzero) a low high

/-- Complete callee postcondition against the single shared native algorithm. -/
structure Post (s t : ArmState) (limit : Option Nat) (data : Ssz.Bytes) : Prop where
  returned : Returned s t
  result : SszNative.Delimited.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (r (.GPR 2#5) s).toNat (r (.GPR 1#5) s).toNat data
    (SszNative.Delimited.run limit data (arenaOf s))
  prepared : (SszNative.Delimited.run limit data (arenaOf s)).PreparedAt (widthLoad t)
  cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat =
    (SszNative.Delimited.run limit data (arenaOf s)).used
  frame : MemoryFrame (writesFor s (SszNative.Delimited.run limit data (arenaOf s)).allocation) s t
  inputs : InputsPreserved s t limit data

/-- Static original-input preservation follows once the actual instruction frame
has been established; it is never an execution or codec-correctness hypothesis. -/
theorem post_of_frame (s t : ArmState) (limit : Option Nat) (data : Ssz.Bytes)
    (owned : Owned s limit data) (returned : Returned s t)
    (result : SszNative.Delimited.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
      (r (.GPR 2#5) s).toNat (r (.GPR 1#5) s).toNat data
      (SszNative.Delimited.run limit data (arenaOf s)))
    (prepared : (SszNative.Delimited.run limit data (arenaOf s)).PreparedAt (widthLoad t))
    (cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat =
      (SszNative.Delimited.run limit data (arenaOf s)).used)
    (frame : MemoryFrame (writesFor s (SszNative.Delimited.run limit data (arenaOf s)).allocation) s t) :
    Post s t limit data := by
  refine ⟨returned, result, prepared, cursor, frame, ?_⟩
  have allocation := (SszNative.Delimited.run_resources limit data (arenaOf s) owned.physical).1
  rw [allocation] at frame
  exact inputs_preserved owned frame

end SszArm.Delimited
