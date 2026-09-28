import SszX86.BitVectorConstructMath
import SszX86.BitVectorSuccess
import SszX86.BitVectorDecode

namespace SszX86.BitVector
open Kraken.X64.Parser

/-- The Some tag is tested as a byte, not as an assumed control-flow edge. -/
theorem construct_some_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (tag : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 1 = some 1)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 5260)) :
    Eventually (step e) P (s, base + 5249) := by
  bitvector_decoded_step 172 at 5249 size 5 code parse("testb $0x1,0x10(%rsp)") using hc
  bitvector_load tag
  constructor <;> bitvector_decoded_step 173 at 5254 size 6 code parse("je bitVector_u6345") using hc
  all_goals simpa [StatusFlags.from_result, Effects.All] using next _

def constructLoaded (s : MachineData) (count : BitVec 128) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec (constructLow count)
    rcx := UInt64.ofBitVec (constructHigh count)}}

/-- NatToU128's payload is at result+16/+24, hence body SP+32/+40. -/
theorem construct_loads_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : BitVec 128)
    (low : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 32#64) 8 =
      some ((constructLow count).toNat : Int))
    (high : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 40#64) 8 =
      some ((constructHigh count).toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (constructLoaded s count, base + 5270)) :
    Eventually (step e) P (s, base + 5260) := by
  have lowBits : BitVec.ofInt 64 ((constructLow count).toNat : Int) =
      constructLow count := by
    simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have highBits : BitVec.ofInt 64 ((constructHigh count).toNat : Int) =
      constructHigh count := by
    simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  change BitVec.ofInt 64 ((count.toNat : Int) % 18446744073709551616) =
    constructLow count at lowBits
  change BitVec.ofInt 64 (((count.toNat : Int) >>> 64) % 18446744073709551616) =
    constructHigh count at highBits
  bitvector_decoded_step 174 at 5260 size 5 code parse("movq 0x20(%rsp),%rax") using hc
  bitvector_load low
  bitvector_decoded_step 175 at 5265 size 5 code parse("movq 0x28(%rsp),%rcx") using hc
  bitvector_load high
  simpa only [constructLoaded, lowBits, highBits] using next

theorem construct_shr_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : BitVec 128)
    (high : s.regs.rcx.toBitVec = constructHigh count)
    (bound : count.toNat < 2^67) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rdx := 0}, status := flags}, base + 5277)) :
    Eventually (step e) P (s, base + 5270) := by
  have shifted := construct_high_shift count bound
  have shiftedReg : s.regs.rcx >>> (3 : UInt64) = 0 := by
    apply UInt64.toBitVec_inj.mp
    change s.regs.rcx.toBitVec >>> (3 : Nat) = 0#64
    rw [high]
    exact shifted
  bitvector_decoded_step 176 at 5270 size 3 code parse("movq %rcx,%rdx") using hc
  bitvector_decoded_step 177 at 5273 size 4 code parse("shrq $0x3,%rdx") using hc
  simp (config := {instances := true}) [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
    ConstExpr.interp, BitVec.take, Effects.All]
  constructor <;> constructor
  all_goals simpa only [shiftedReg] using next _

theorem construct_shld_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : BitVec 128)
    (low : s.regs.rax.toBitVec = constructLow count)
    (high : s.regs.rcx.toBitVec = constructHigh count)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with rsi := UInt64.ofBitVec (constructQuotient count)}
        status := flags}, base + 5285)) :
    Eventually (step e) P (s, base + 5277) := by
  bitvector_decoded_step 178 at 5277 size 3 code parse("movq %rcx,%rsi") using hc
  bitvector_decoded_step 179 at 5280 size 5 code parse("shldq $0x3d,%rax,%rsi") using hc
  simp (config := {instances := true}) [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
    ConstExpr.interp, BitVec.take, Effects.All]
  constructor <;> constructor
  all_goals simpa [low, high, constructQuotient, StatusFlags.from_result, Effects.All] using next _

private theorem construct_set_byte (b : Bool) :
    0#56 ++ BitVec.ofNat 8 b.toNat = BitVec.ofNat 64 b.toNat := by
  cases b <;> decide

theorem construct_bump_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : BitVec 128)
    (low : s.regs.rax.toBitVec = constructLow count) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with rdi := UInt64.ofBitVec (constructBump count)}
        status := flags}, base + 5293)) :
    Eventually (step e) P (s, base + 5285) := by
  bitvector_decoded_step 180 at 5285 size 2 code parse("xorl %edi,%edi") using hc
  constructor <;> bitvector_decoded_step 181 at 5287 size 2 code parse("testb $0x7,%al") using hc
  all_goals constructor <;> bitvector_decoded_step 182 at 5289 size 4 code parse("setne %dil") using hc
  all_goals simpa [low, constructBump, construct_set_byte,
    StatusFlags.from_result, Effects.All] using next _

def constructAdded (s : MachineData) (count : BitVec 128) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdi := UInt64.ofBitVec (constructQuotient count + constructBump count)
      rdx := UInt64.ofBitVec (BitVec.ofNat 64
        (SszX86.Udivti3.addFlags (constructQuotient count) (constructBump count)).cf.toNat)}
    status := flags}

private theorem construct_numeral (n : Nat) :
    (OfNat.ofNat n : UInt64) = UInt64.ofBitVec (BitVec.ofNat 64 n) := rfl

private theorem construct_zero_add (value : UInt64) :
    UInt64.ofBitVec 0#64 + value = value := UInt64.zero_add value

/-- ADD computes the low word; ADC consumes its actual carry flag. -/
theorem construct_add_adc_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : BitVec 128)
    (quotient : s.regs.rsi.toBitVec = constructQuotient count)
    (bump : s.regs.rdi.toBitVec = constructBump count)
    (zero : s.regs.rdx = 0) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (constructAdded s count flags, base + 5300)) :
    Eventually (step e) P (s, base + 5293) := by
  have quotientReg : s.regs.rsi = UInt64.ofBitVec (constructQuotient count) :=
    UInt64.toBitVec_inj.mp quotient
  have bumpReg : s.regs.rdi = UInt64.ofBitVec (constructBump count) :=
    UInt64.toBitVec_inj.mp bump
  have quotientNat : s.regs.rsi.toNat = (constructQuotient count).toNat :=
    congrArg BitVec.toNat quotient
  have bumpNat : s.regs.rdi.toNat = (constructBump count).toNat :=
    congrArg BitVec.toNat bump
  bitvector_decoded_step 183 at 5293 size 3 code parse("addq %rsi,%rdi") using hc
  bitvector_decoded_step 184 at 5296 size 4 code parse("adcq $0x0,%rdx") using hc
  simp only [construct_numeral, quotientReg, bumpReg, zero]
  simpa (config := {instances := true}) [constructAdded, construct_numeral, construct_zero_add,
    quotientReg, bumpReg, quotientNat, bumpNat, zero, SszX86.Udivti3.addFlags,
    StatusFlags.from_result, BitVec.take, BitVec.signed, Effects.All,
    UInt64.toNat_ofBitVec, -UInt64.ofBitVec_ofNat] using next _

/-- XOR with the scope length and OR with the ADC high word both produce zero.
The subsequent MOV does not overwrite flags, so JNE cannot enter error 6550. -/
theorem construct_guard_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (out : BitVec 64)
    (equal : s.regs.rdi = s.regs.r14) (zero : s.regs.rdx = 0)
    (cached : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (out.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rdi := 0, rdx := UInt64.ofBitVec out}, status := flags},
        base + 5317)) :
    Eventually (step e) P (s, base + 5300) := by
  bitvector_decoded_step 185 at 5300 size 3 code parse("xorq %r14,%rdi") using hc
  constructor <;> bitvector_decoded_step 186 at 5303 size 3 code parse("orq %rdx,%rdi") using hc
  all_goals constructor <;> bitvector_decoded_step 187 at 5306 size 5 code parse("movq 0x8(%rsp),%rdx") using hc
  all_goals bitvector_load cached
  all_goals bitvector_decoded_step 188 at 5311 size 6 code parse("jne bitVector_u6550") using hc
  all_goals simpa [equal, zero, StatusFlags.from_result, Effects.All] using next _

/-- Exact physical register state immediately before the six success stores.
All other integer registers, SIMD registers, and memory are unchanged. -/
def constructReady (s : MachineData) (count : BitVec 128) (out : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (constructLow count)
      rcx := UInt64.ofBitVec (constructHigh count)
      rdx := UInt64.ofBitVec out
      rsi := UInt64.ofBitVec (constructQuotient count)
      rdi := 0}
    status := flags}

/-- Actual post-NatToU128 execution. The only mathematical premises are scope's
bounded narrowing and exact byte length; neither native branch is assumed. -/
theorem construct_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : BitVec 128) (out : BitVec 64)
    (bound : count.toNat < 2^67)
    (scope : s.regs.r14.toBitVec.toNat = (count.toNat + 7) / 8)
    (tag : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 1 = some 1)
    (low : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 32#64) 8 =
      some ((constructLow count).toNat : Int))
    (high : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 40#64) 8 =
      some ((constructHigh count).toNat : Int))
    (cached : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (out.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (constructReady s count out flags, base + 5317)) :
    Eventually (step e) P (s, base + 5249) := by
  obtain ⟨rounded, carry⟩ := construct_rounding count s.regs.r14.toBitVec bound scope
  apply construct_some_cps e base hc s tag P
  intro f0
  apply construct_loads_cps e base hc {s with status := f0} count low high P
  refine construct_shr_cps e base hc _ count ?_ bound P ?_
  · simp [constructLoaded]
  intro f1
  refine construct_shld_cps e base hc _ count ?_ ?_ P ?_
  · simp [constructLoaded]
  · simp [constructLoaded]
  intro f2
  refine construct_bump_cps e base hc _ count ?_ P ?_
  · simp [constructLoaded]
  intro f3
  refine construct_add_adc_cps e base hc _ count ?_ ?_ ?_ P ?_
  · simp
  · simp
  · rfl
  intro f4
  apply construct_guard_cps e base hc _ out
  · simp [constructAdded, rounded, constructLoaded]
  · change UInt64.ofBitVec (BitVec.ofNat 64
      (SszX86.Udivti3.addFlags (constructQuotient count) (constructBump count)).cf.toNat) = 0
    rw [carry]
    rfl
  · exact cached
  intro f5
  simpa [constructReady, constructAdded, constructLoaded] using next f5

end SszX86.BitVector
