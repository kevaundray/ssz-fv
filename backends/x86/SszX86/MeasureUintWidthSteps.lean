import SszX86.MeasureUintScan

namespace SszX86.Measure.Uint
open SszNative SszNative.Serialize UintCodec

/-- Only the width scan's four scratch registers change. RDX:RDI retain the
full 128-bit requirement, while RCX:RAX retain the original width operand. -/
def widthState (s : MachineData) (pointer payload index limb : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rcx := UInt64.ofBitVec pointer
      rax := UInt64.ofBitVec payload
      rsi := UInt64.ofBitVec index
      r8 := UInt64.ofBitVec limb}
    status := flags}

structure WidthFrame (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  vectors : t.zmms = s.zmms
  stack : t.regs.rsp = s.regs.rsp
  result : t.regs.rbx = s.regs.rbx
  requiredLow : t.regs.rdi = s.regs.rdi
  requiredHigh : t.regs.rdx = s.regs.rdx

theorem width_state_frame (s : MachineData) (p v i l : BitVec 64) (flags : StatusFlags) :
    WidthFrame s (widthState s p v i l flags) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem width_frame_trans {s t u : MachineData} (first : WidthFrame s t)
    (second : WidthFrame t u) : WidthFrame s u :=
  ⟨second.memory.trans first.memory, second.vectors.trans first.vectors,
    second.stack.trans first.stack, second.result.trans first.result,
    second.requiredLow.trans first.requiredLow, second.requiredHigh.trans first.requiredHigh⟩

/-- Width metadata is loaded once from the original descriptor. -/
theorem width_header_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64)
    (hp : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (pointer.toNat : Int))
    (hv : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (payload.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (widthState s pointer payload s.regs.rsi.toBitVec s.regs.r8.toBitVec flags,
        if pointer = 0#64 then base + 2736 else base + 2699)) :
    Eventually (step e) P (s, base + 2686) := by
  have target := hc.targets ("measure_u2736", 2736) (by decide)
  measure_step 346 using hc
  measure_uint_load hp
  measure_step 347 using hc
  measure_uint_load hv
  measure_step 348 using hc
  constructor <;> measure_step 349 using hc
  all_goals
    by_cases zero : pointer = 0#64
    · simpa [zero, target, widthState, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, widthState, StatusFlags.from_result, Effects.All] using next _

/-- LEA plus the original NOP, with no host-width assumption on the width value. -/
theorem width_begin_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rsi := UInt64.ofBitVec (s.regs.rax.toBitVec + 1)}},
        base + 2704)) :
    Eventually (step e) P (s, base + 2699) := by
  measure_step 350 using hc
  measure_step 351 using hc
  simpa [BitVec.add_comm] using next

/-- Three significant width limbs take the direct successful publication edge. -/
theorem width_count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.r8.toNat < 3 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 2755))
    (large : 3 ≤ s.regs.r8.toNat → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 3052)) :
    Eventually (step e) P (s, base + 2725) := by
  have target := hc.targets ("measure_u2755", 2755) (by decide)
  measure_step 358 using hc
  measure_step 359 using hc
  by_cases fits : s.regs.r8.toNat < 3
  · simpa [fits, target, StatusFlags.from_result, Udivti3.cf_sub, Effects.All] using small fits _
  · simp [fits, StatusFlags.from_result, Effects.All]
    measure_step 360 using hc
    simpa using large (by omega) _

/-- Small width values use their original immediate payload. -/
theorem width_small_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rsi := 0, r8 := s.regs.rax}, status := flags},
        base + 3253)) :
    Eventually (step e) P (s, base + 2736) := by
  measure_step 361 using hc
  constructor <;> measure_step 362 using hc
  all_goals
    measure_step 363 using hc
    exact next _

/-- The all-zero path still branches on physical length before any low-limb read. -/
theorem width_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags},
      if s.regs.rax.toBitVec = 0#64 then base + 3248 else base + 2755)) :
    Eventually (step e) P (s, base + 2746) := by
  have target := hc.targets ("measure_u3248", 3248) (by decide)
  measure_step 364 using hc
  constructor <;> measure_step 365 using hc
  all_goals
    by_cases zero : s.regs.rax.toBitVec = 0#64
    · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, StatusFlags.from_result, Effects.All] using next _

/-- Large [] has zero low/high values; its original pointer/payload still survive. -/
theorem width_empty_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rsi := 0, r8 := 0}, status := flags}, base + 3253)) :
    Eventually (step e) P (s, base + 3248) := by
  measure_step 454 using hc
  constructor <;> measure_step 455 using hc
  all_goals constructor <;> exact next _

/-- Original physical length governs whether the second limb is read. -/
theorem width_borrowed_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (lo hi : BitVec 64)
    (hlo : Mem.loadInt s.dmem s.regs.rcx.toBitVec 8 = some (lo.toNat : Int))
    (hhi : 2 ≤ s.regs.rax.toNat →
      Mem.loadInt s.dmem (s.regs.rcx.toBitVec + 8#64) 8 = some (hi.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with
          r8 := UInt64.ofBitVec lo
          rsi := UInt64.ofBitVec (if s.regs.rax.toNat < 2 then 0 else hi)}
        status := flags},
        base + 3253)) :
    Eventually (step e) P (s, base + 2755) := by
  have target := hc.targets ("measure_u2773", 2773) (by decide)
  measure_step 366 using hc
  measure_uint_load hlo
  measure_step 367 using hc
  measure_step 368 using hc
  by_cases short : s.regs.rax.toNat < 2
  · simp [short, target, StatusFlags.from_result, Effects.All]
    measure_step 371 using hc
    constructor <;> measure_step 372 using hc
    all_goals simpa [short] using next _
  · simp [short, StatusFlags.from_result, Effects.All]
    measure_step 369 using hc
    measure_uint_load (hhi (by omega))
    measure_step 370 using hc
    simpa [short] using next _

/-- Exact carry predicate for subtract-with-borrow, including the high-word zero boundary. -/
theorem cf_sbb (left right : BitVec 64) (borrow : Bool) :
    ((left - right - BitVec.ofNat 64 borrow.toNat).unsigned !=
      left.unsigned - right.unsigned - (borrow.toNat : Int)) =
      decide (left.toNat < right.toNat + borrow.toNat) := by
  apply Bool.eq_iff_iff.mpr
  cases borrow <;>
    simp [BitVec.unsigned, BitVec.toNat_sub, BitVec.toNat_ofNat] <;>
    have := left.isLt <;> have := right.isLt <;> omega

/-- The CMP/SBB carry is exactly unsigned 128-bit ordering, not truncated comparison. -/
theorem pair_borrow (lo hi requiredLo requiredHi : BitVec 64) :
    (hi.toNat < requiredHi.toNat + (decide (lo.toNat < requiredLo.toNat)).toNat) ↔
      hi.toNat * 2 ^ 64 + lo.toNat < requiredHi.toNat * 2 ^ 64 + requiredLo.toNat := by
  have := lo.isLt
  have := hi.isLt
  have := requiredLo.isLt
  have := requiredHi.isLt
  by_cases lower : lo.toNat < requiredLo.toNat <;> simp [lower] <;> omega

private theorem width_low_cmp_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, flags.cf = decide (s.regs.r8.toNat < s.regs.rdi.toNat) →
      Eventually (step e) P ({s with status := flags}, base + 3256)) :
    Eventually (step e) P (s, base + 3253) := by
  measure_step 456 using hc
  apply next
  simp [StatusFlags.from_result]

private def widthSbbState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsi := UInt64.ofBitVec
        (s.regs.rsi.toBitVec - s.regs.rdx.toBitVec - BitVec.ofNat 64 s.status.cf.toNat)}
    status := flags}

private theorem width_sbb_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags,
      flags.cf = decide (s.regs.rsi.toNat < s.regs.rdx.toNat + s.status.cf.toNat) →
      Eventually (step e) P (widthSbbState s flags, base + 3259)) :
    Eventually (step e) P (s, base + 3256) := by
  simp only [widthSbbState] at next
  measure_step 457 using hc
  apply next
  simp [StatusFlags.from_result, cf_sbb]

private theorem width_jae_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      (s, if s.status.cf = false then base + 3052 else base + 3265)) :
    Eventually (step e) P (s, base + 3259) := by
  have target := hc.targets ("measure_u3052", 3052) (by decide)
  measure_step 458 using hc
  cases carry : s.status.cf <;> simpa [carry, target, Effects.All] using next

/-- The final comparison leaves RCX:RAX untouched on both actual outcomes. -/
theorem width_compare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with
          rsi := UInt64.ofBitVec
            (s.regs.rsi.toBitVec - s.regs.rdx.toBitVec -
              BitVec.ofNat 64 (decide (s.regs.r8.toNat < s.regs.rdi.toNat)).toNat)}
        status := flags},
        if s.regs.rdx.toNat * 2 ^ 64 + s.regs.rdi.toNat ≤
            s.regs.rsi.toNat * 2 ^ 64 + s.regs.r8.toNat
          then base + 3052 else base + 3265)) :
    Eventually (step e) P (s, base + 3253) := by
  apply width_low_cmp_cps e base hc
  intro lowFlags lowCarry
  apply width_sbb_cps e base hc
  intro highFlags highCarry
  simp only [lowCarry] at highCarry
  apply width_jae_cps e base hc
  have predicate := pair_borrow s.regs.r8.toBitVec s.regs.rsi.toBitVec
    s.regs.rdi.toBitVec s.regs.rdx.toBitVec
  simp only [UInt64.toNat_toBitVec] at predicate
  by_cases fits : s.regs.rdx.toNat * 2 ^ 64 + s.regs.rdi.toNat ≤
      s.regs.rsi.toNat * 2 ^ 64 + s.regs.r8.toNat
  · have borrow : ¬ s.regs.rsi.toNat < s.regs.rdx.toNat +
        (decide (s.regs.r8.toNat < s.regs.rdi.toNat)).toNat := by
      intro bad
      have := predicate.mp bad
      omega
    simpa [widthSbbState, lowCarry, highCarry, fits, borrow] using next highFlags
  · have borrow : s.regs.rsi.toNat < s.regs.rdx.toNat +
        (decide (s.regs.r8.toNat < s.regs.rdi.toNat)).toNat :=
      predicate.mpr (by omega)
    simpa [widthSbbState, lowCarry, highCarry, fits, borrow] using next highFlags

end SszX86.Measure.Uint
