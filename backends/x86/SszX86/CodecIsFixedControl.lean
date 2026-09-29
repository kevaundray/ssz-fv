import SszX86.CodecIsFixedJump
import SszX86.CodecIsFixedReturn

namespace SszX86.CodecIsFixed
open BoolCodec UintCodec

/-- The entry and backedge copies of CMP7 route identically. The vector edge
passes through its real alignment NOP only on the original-entry copy. -/
theorem tag_guards (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rax.toBitVec = 7#64 then base + 16 else base + 29)) :
    Eventually (step e) P (s, base + 7) ∧ Eventually (step e) P (s, base + 23) := by
  have target16 := hc.targets ("codec_is_fixed_u16", 16) (by decide)
  have target29 := hc.targets ("codec_is_fixed_u29", 29) (by decide)
  constructor
  · codec_is_fixed_step 4 using hc
    codec_is_fixed_step 5 using hc
    by_cases vector : s.regs.rax.toBitVec = 7#64
    · simp [StatusFlags.from_result, vector, Effects.All]
      codec_is_fixed_step 6 using hc
      simpa only [vector, ↓reduceIte] using next _
    · simpa [StatusFlags.from_result, vector, target29, Effects.All] using next _
  · codec_is_fixed_step 9 using hc
    codec_is_fixed_step 10 using hc
    by_cases vector : s.regs.rax.toBitVec = 7#64
    · simpa [StatusFlags.from_result, vector, target16, Effects.All] using next _
    · simpa [StatusFlags.from_result, vector, Effects.All] using next _

def loadedState (s : MachineData) (tag : Nat) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat tag}}

theorem tag_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag : Nat) (P : MachineState → Prop)
    (loaded : Mem.loadInt s.dmem s.regs.rdi.toBitVec 8 = some (tag : Int))
    (next : Eventually (step e) P (loadedState s tag, base + 7)) :
    Eventually (step e) P (s, base + 4) := by
  codec_is_fixed_step 3 using hc
  simpa [MachineData.load, Effects.All, loaded, loadedState, Width.bytes, Width.bits,
    BitVec.ofInt_ofNat, UInt64.ofNat] using next

def vectorState (s : MachineData) (child : BitVec 64) (tag : Nat) : MachineData :=
  {s with regs := {s.regs with rdi := UInt64.ofBitVec child, rax := UInt64.ofNat tag}}

/-- A vector edge reads the complete child pointer and then the child's tag;
the same machine activation is reused, with no depth bound or recursive call. -/
theorem vector_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (child : BitVec 64) (tag : Nat) (P : MachineState → Prop)
    (pointer : Mem.loadInt s.dmem (s.regs.rdi.toBitVec + 24) 8 = some (child.toNat : Int))
    (childTag : Mem.loadInt s.dmem child 8 = some (tag : Int))
    (next : Eventually (step e) P (vectorState s child tag, base + 23)) :
    Eventually (step e) P (s, base + 16) := by
  codec_is_fixed_step 7 using hc
  codec_is_fixed_load pointer
  codec_is_fixed_step 8 using hc
  simpa [MachineData.load, Effects.All, childTag, vectorState, Width.bytes, Width.bits,
    BitVec.ofInt_ofNat, UInt64.ofNat] using next

theorem range_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rax.toNat ≤ 11 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 35))
    (large : 11 < s.regs.rax.toNat → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 122)) :
    Eventually (step e) P (s, base + 29) := by
  have target := hc.targets ("codec_is_fixed_u122", 122) (by decide)
  codec_is_fixed_step 11 using hc
  codec_is_fixed_step 12 using hc
  by_cases bounded : s.regs.rax.toNat ≤ 11
  · simpa [StatusFlags.from_result, Udivti3.cf_sub, bounded, Effects.All] using small bounded _
  · simpa [StatusFlags.from_result, Udivti3.cf_sub, bounded, target, Effects.All] using
      large (by omega) _

def trueState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec (s.regs.rax.toBitVec.replaceLow 1#8)}}

theorem true_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (trueState s, base + 53)) :
    Eventually (step e) P (s, base + 51) := by
  codec_is_fixed_step 17 using hc
  exact next

theorem false_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rax := 0}, status := flags}, base + 124)) :
    Eventually (step e) P (s, base + 122) := by
  codec_is_fixed_step 38 using hc
  constructor <;> simpa using next _

end SszX86.CodecIsFixed
