import SszArm.DelimitedCountPhase
import SszArm.DelimitedInvalid
import SszArm.DelimitedDispatch

namespace SszArm.Delimited

open UintCodec (widthLoad)

/-- The native from_u128 result, after reservation and before/after comparison.
The PC is intentionally supplied by each actual control-flow edge. -/
structure Ready (s t : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) (ready : SszNative.Delimited.Prepared) : Prop where
  prepared : SszNative.Delimited.prepare (arenaOf s)
    (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)) = some ready
  allocation : SszNative.Delimited.allocation data (arenaOf s) = ready.allocation
  program : t.program = s.program
  error : read_err t = .None
  aligned : CheckSPAlignment t
  saved : Saved s t
  arguments : ∀ reg : BitVec 5, reg ∈ [0#5, 2#5, 3#5, 4#5] →
    r (.GPR reg) t = r (.GPR reg) s
  preceding : r (.GPR 25#5) t = BitVec.ofNat 64 (data.size - 1)
  counter : r (.GPR 26#5) t = BitVec.ofNat 64 (7 - Ssz.highestBit data[data.size - 1]!)
  low : r (.GPR 24#5) t = ready.count.low
  high : r (.GPR 23#5) t = ready.count.high
  pointer : r (.GPR 20#5) t = BitVec.ofNat 64 ready.pointer
  payload : r (.GPR 19#5) t = BitVec.ofNat 64 ready.payload
  stored : SszNative.Delimited.PreparedAt (widthLoad t) ready
  cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat = ready.used
  frame : MemoryFrame (writesFor s ready.allocation) s t

theorem Ready.inputs {s t : ArmState} {base : BitVec 64} {limit : Option Nat}
    {data : Ssz.Bytes} {ready : SszNative.Delimited.Prepared}
    (state : Ready s t base limit data ready) (owned : Owned s limit data) :
    InputsPreserved s t limit data := by
  apply inputs_preserved owned
  simpa only [state.allocation] using state.frame

theorem Ready.pair {s t : ArmState} {base : BitVec 64} {limit : Option Nat}
    {data : Ssz.Bytes} {ready : SszNative.Delimited.Prepared}
    (state : Ready s t base limit data ready) (owned : Owned s limit data) :
    SszNative.NatMemory.Pair (widthLoad t) (r (.GPR 20#5) t)
      (r (.GPR 19#5) t) ready.count.value := by
  rw [state.pointer, state.payload]
  exact SszNative.Delimited.PreparedAt.pair (widthLoad t) (arenaOf s) _ ready
    state.prepared state.stored owned.arenaStorage owned.arenaNonnull

theorem prepared_allocation (limit : Option Nat) (data : Ssz.Bytes)
    (arena : SszNative.Delimited.ArenaState) (ready : SszNative.Delimited.Prepared)
    (physical : data.size < 2^64) (nonempty : 0 < data.size)
    (delimiter : data[data.size - 1]! ≠ 0)
    (prepared : SszNative.Delimited.prepare arena
      (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)) = some ready) :
    SszNative.Delimited.allocation data arena = ready.allocation := by
  have resource := (SszNative.Delimited.run_resources limit data arena physical).1
  rw [SszNative.Delimited.run_valid limit data arena nonempty delimiter, prepared] at resource
  exact resource.symm

theorem Saved.of_memory {entry s t : ArmState} (saved : Saved entry s)
    (memory : t.mem = s.mem) (sp : r (.GPR 31#5) t = r (.GPR 31#5) s)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64) : Saved entry t := by
  refine ⟨sp.trans saved.sp, ?_, ?_⟩
  · intro reg offset member
    rw [sp, (Memory.mem_eq_iff_read_mem_bytes_eq.mp memory) 8]
    exact saved.words reg offset member
  · intro reg low high
    exact (vectors reg low high).trans (saved.vectors reg low high)

theorem option_tag (s : ArmState) (pointer : BitVec 64) (limit : Option Nat)
    (option : SszNative.NatMemory.OptionAt (widthLoad s) pointer.toNat limit) :
    read_mem_bytes 4 pointer s = if limit.isSome then 1#32 else 0#32 := by
  cases limit with
  | none =>
    have tag := Option.some.inj option
    apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, BitVec.ofNat_toNat] using tag
  | some value =>
    have tag := Option.some.inj option.1
    apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, BitVec.ofNat_toNat] using tag

end SszArm.Delimited
