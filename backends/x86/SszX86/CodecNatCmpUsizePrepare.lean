import SszX86.CodecNatCmpUsizeExec

namespace SszX86.CodecNatCmpUsize
open SszNative.Limbs SszNative.NatABI

/-- The second load depends on the physical count, including retained zero limbs. -/
theorem borrowed_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c lo hi : BitVec 64) (flags : StatusFlags)
    (hlo : Mem.loadInt s.dmem s.regs.rdi.toBitVec 8 = some (lo.toNat : Int))
    (hhi : 2 ≤ s.regs.rsi.toNat →
      Mem.loadInt s.dmem (s.regs.rdi.toBitVec + 8#64) 8 = some (hi.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (state s lo (if s.regs.rsi.toNat < 2 then 0 else hi) lo flags, base + 81)) :
    Eventually (step e) P (state s a c s.regs.rsi.toBitVec flags, base + 55) := by
  have target := hc.targets ("codec_nat_cmp_usize_u70", 70) (by decide)
  codec_usize_step 18 using hc
  codec_usize_load hlo
  codec_usize_step 19 using hc
  codec_usize_step 20 using hc
  by_cases short : s.regs.rsi.toNat < 2
  · simp [short, target, StatusFlags.from_result, Effects.All]
    codec_usize_step 23 using hc
    constructor <;> codec_usize_step 24 using hc
    all_goals codec_usize_step 25 using hc
    all_goals simpa [state, short] using next _
  · simp [short, StatusFlags.from_result, Effects.All]
    codec_usize_step 21 using hc
    codec_usize_load (hhi (by omega))
    codec_usize_step 22 using hc
    codec_usize_step 24 using hc
    codec_usize_step 25 using hc
    simpa [state, short] using next _

theorem zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (empty : s.regs.rsi.toBitVec = 0 → ∀ flags, Eventually (step e) P
      (state s a 0 0 flags, base + 81))
    (nonempty : s.regs.rsi.toBitVec ≠ 0 → ∀ flags, Eventually (step e) P
      (state s a c s.regs.rsi.toBitVec flags, base + 55)) :
    Eventually (step e) P (state s a c s.regs.rsi.toBitVec flags, base + 50) := by
  have target := hc.targets ("codec_nat_cmp_usize_u77", 77) (by decide)
  codec_usize_step 16 using hc
  constructor <;> codec_usize_step 17 using hc
  all_goals
    by_cases hz : s.regs.rsi.toBitVec = 0#64
    · simp [StatusFlags.from_result, hz, target, Effects.All]
      codec_usize_step 26 using hc
      constructor <;> codec_usize_step 27 using hc
      all_goals constructor <;> simpa [state] using empty hz _
    · simpa [StatusFlags.from_result, hz, state, Effects.All] using nonempty hz _

theorem count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (small : c.toNat < 3 → ∀ flags, Eventually (step e) P
      (state s a c s.regs.rsi.toBitVec flags, base + 55))
    (large : 3 ≤ c.toNat → ∀ flags, Eventually (step e) P
      (state s (a.replaceLow 1#8) c s.regs.rsi.toBitVec flags, base + 45)) :
    Eventually (step e) P (state s a c s.regs.rsi.toBitVec flags, base + 37) := by
  have target := hc.targets ("codec_nat_cmp_usize_u55", 55) (by decide)
  codec_usize_step 10 using hc
  codec_usize_step 11 using hc
  by_cases hs : c.toNat < 3
  · simpa [hs, target, StatusFlags.from_result, NatCompare.cf_sub, state, Effects.All]
      using small hs _
  · simp [hs, StatusFlags.from_result, NatCompare.cf_sub, Effects.All]
    codec_usize_step 12 using hc
    simpa [state, BitVec.replaceLow, BitVec.drop] using large (by omega) _

theorem entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rdi.toBitVec = 0 → ∀ flags, Eventually (step e) P
      (state s s.regs.rax.toBitVec 0 s.regs.rsi.toBitVec flags, base + 81))
    (large : s.regs.rdi.toBitVec ≠ 0 → ∀ flags, Eventually (step e) P
      (state s (s.regs.rsi.toBitVec + 1) s.regs.rcx.toBitVec s.regs.rsi.toBitVec flags,
        base + 16)) :
    Eventually (step e) P (s, base) := by
  have target := hc.targets ("codec_nat_cmp_usize_u46", 46) (by decide)
  rw [← Int64.add_zero base]
  codec_usize_step 0 using hc
  constructor <;> codec_usize_step 1 using hc
  all_goals
    by_cases hz : s.regs.rdi.toBitVec = 0#64
    · simp [StatusFlags.from_result, hz, target, Effects.All]
      codec_usize_step 14 using hc
      constructor <;> codec_usize_step 15 using hc
      all_goals simpa [state] using small hz _
    · simp [StatusFlags.from_result, hz, Effects.All]
      codec_usize_step 2 using hc
      simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
      codec_usize_step 3 using hc
      simpa [state] using large hz _

end SszX86.CodecNatCmpUsize
