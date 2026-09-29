import SszX86.CodecMeasureFixedPush
import SszX86.CodecMeasureFixedJump

namespace SszX86.CodecMeasureFixed
open BoolCodec UintCodec

def taggedState (s : MachineData) (tag : Nat) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat tag}}

theorem tag_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag : Nat) (P : MachineState → Prop)
    (loaded : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (tag : Int))
    (next : Eventually (step e) P (taggedState s tag, base + 20)) :
    Eventually (step e) P (s, base + 17) := by
  codec_measure_fixed_step 8 using hc
  simpa [MachineData.load, Effects.All, loaded, taggedState, Width.bytes, Width.bits,
    BitVec.ofInt_ofNat, UInt64.ofNat] using next

def arenaStateReady (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r12 := s.regs.rdx}
    status := flags}

/-- R12 is assigned only on the in-range branch. Out-of-range tag12 returns
None without touching the arena, exactly as the linked guard orders the moves. -/
theorem tag_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rax.toNat ≤ 11 → ∀ flags,
      Eventually (step e) P (arenaStateReady s flags, base + 33))
    (large : 11 < s.regs.rax.toNat → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 680)) :
    Eventually (step e) P (s, base + 20) := by
  have target := hc.targets ("codec_measure_fixed_u680", 680) (by decide)
  codec_measure_fixed_step 9 using hc
  codec_measure_fixed_step 10 using hc
  by_cases bounded : s.regs.rax.toNat ≤ 11
  · simp [StatusFlags.from_result, Udivti3.cf_sub, bounded, Effects.All]
    codec_measure_fixed_step 11 using hc
    simpa [arenaStateReady] using small bounded _
  · simpa [StatusFlags.from_result, Udivti3.cf_sub, bounded, target, Effects.All] using
      large (by omega) _

def widthState (s : MachineData) (pointer payload : BitVec 64) : MachineData :=
  {s with regs := {s.regs with r14 := UInt64.ofBitVec pointer, r15 := UInt64.ofBitVec payload}}

/-- Uint/ByteVector copy the original unnormalized Nat pair from the descriptor. -/
theorem borrowed_width (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64) (P : MachineState → Prop)
    (pointerLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8) 8 = some (pointer.toNat : Int))
    (payloadLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16) 8 = some (payload.toNat : Int))
    (next : Eventually (step e) P (widthState s pointer payload, base + 271)) :
    Eventually (step e) P (s, base + 49) := by
  codec_measure_fixed_step 16 using hc
  codec_measure_fixed_load pointerLoad
  codec_measure_fixed_step 17 using hc
  codec_measure_fixed_load payloadLoad
  codec_measure_fixed_step 18 using hc
  simpa [widthState] using next

theorem bool_width (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({widthState s 0 1 with status := flags}, base + 271)) :
    Eventually (step e) P (s, base + 262) := by
  codec_measure_fixed_step 68 using hc
  codec_measure_fixed_step 69 using hc
  constructor <;> simpa [widthState] using next _

theorem empty_width (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({widthState s 0 0 with status := flags}, base + 271)) :
    Eventually (step e) P (s, base + 254) := by
  codec_measure_fixed_step 65 using hc
  constructor <;> codec_measure_fixed_step 66 using hc
  all_goals constructor <;> codec_measure_fixed_step 67 using hc
  all_goals simpa [widthState] using next _

end SszX86.CodecMeasureFixed
