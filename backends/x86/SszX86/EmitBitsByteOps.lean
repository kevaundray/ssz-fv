import SszX86.EmitBitsPrepare
import SszX86.UintByteOps

namespace SszX86.Emit.Bits
open BoolCodec UintCodec
open UintCodec.Small (put putF low8 low32 replace8)

inductive ShiftSite where
  | listMask | delimiter | vectorMask

def ShiftSite.pc : ShiftSite → Nat
  | .listMask => 556 | .delimiter => 566 | .vectorMask => 783

def ShiftSite.next : ShiftSite → Nat
  | .listMask => 558 | .delimiter => 568 | .vectorMask => 785


@[simp] private theorem take8 (v : BitVec 64) :
    v.extractLsb' 0 8 = v.setWidth 8 := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]

@[simp] private theorem restore_low (v : BitVec 64) :
    v.extractLsb' 8 56 ++ v.setWidth 8 = v := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
  exact BitVec.extractLsb'_append_extractLsb'

/-- Variable SHL writes only DL. Its count is the actual low CL, whose bound is
established from the packed count remainder before this internal lemma is used. -/
theorem shift_byte (e : Executable) (base : Int64) (hc : CodeAt e base)
    (site : ShiftSite) (s : MachineData) (remainder : Nat)
    (small : remainder < 8) (count : low8 (UintCodec.Small.get s .rcx) = BitVec.ofNat 8 remainder)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (putF s .rdx (replace8 (UintCodec.Small.get s .rdx) (low8 (UintCodec.Small.get s .rdx) <<< remainder)) flags,
        base + Int64.ofNat site.next)) :
    Eventually (step e) P (s, base + Int64.ofNat site.pc) := by
  have choices : remainder = 0 ∨ remainder = 1 ∨ remainder = 2 ∨ remainder = 3 ∨
      remainder = 4 ∨ remainder = 5 ∨ remainder = 6 ∨ remainder = 7 := by omega
  simp only [low8, UintCodec.Small.get, Reg64s.get64] at count
  cases site
  · emit_step 104 using hc
    rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp (config := {instances := true}) [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
        BitVec.take, Effects.All, count]
      repeat' first | apply And.intro | intro
      all_goals simpa [putF, put, replace8, UintCodec.Small.get, low8, Reg64s.set64, Reg64s.get64,
        BitVec.replaceLow, BitVec.take, BitVec.drop, ShiftSite.next] using next _
  · emit_step 109 using hc
    rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp (config := {instances := true}) [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
        BitVec.take, Effects.All, count]
      repeat' first | apply And.intro | intro
      all_goals simpa [putF, put, replace8, UintCodec.Small.get, low8, Reg64s.set64, Reg64s.get64,
        BitVec.replaceLow, BitVec.take, BitVec.drop, ShiftSite.next] using next _
  · emit_step 164 using hc
    rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp (config := {instances := true}) [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
        BitVec.take, Effects.All, count]
      repeat' first | apply And.intro | intro
      all_goals simpa [putF, put, replace8, UintCodec.Small.get, low8, Reg64s.set64, Reg64s.get64,
        BitVec.replaceLow, BitVec.take, BitVec.drop, ShiftSite.next] using next _

def maskSeed (s : MachineData) : MachineData :=
  put s .rdx (replace8 (UintCodec.Small.get s .rdx) 255#8)

def maskInverted (s : MachineData) : MachineData :=
  put s .rdx (replace8 (UintCodec.Small.get s .rdx) (~~~(low8 (UintCodec.Small.get s .rdx))))

def maskApplied (s : MachineData) (flags : StatusFlags) : MachineData :=
  putF s .rax (replace8 (UintCodec.Small.get s .rax) (low8 (UintCodec.Small.get s .rax) &&& low8 (UintCodec.Small.get s .rdx))) flags

theorem mask_seed (e : Executable) (base : Int64) (hc : CodeAt e base)
    (list : Bool) (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (maskSeed s, base + if list then 556 else 783)) :
    Eventually (step e) P (s, base + if list then 554 else 781) := by
  cases list
  · emit_step 163 using hc
    simpa [maskSeed, put, replace8, UintCodec.Small.get, Reg64s.set64, Reg64s.get64,
      BitVec.replaceLow, BitVec.take, BitVec.drop, Effects.All] using next
  · emit_step 103 using hc
    simpa [maskSeed, put, replace8, UintCodec.Small.get, Reg64s.set64, Reg64s.get64,
      BitVec.replaceLow, BitVec.take, BitVec.drop, Effects.All] using next

theorem mask_not (e : Executable) (base : Int64) (hc : CodeAt e base)
    (list : Bool) (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (maskInverted s, base + if list then 560 else 787)) :
    Eventually (step e) P (s, base + if list then 558 else 785) := by
  cases list
  · emit_step 165 using hc
    simpa [maskInverted, put, replace8, low8, UintCodec.Small.get, Reg64s.set64, Reg64s.get64,
      BitVec.replaceLow, BitVec.take, BitVec.drop, Effects.All] using next
  · emit_step 105 using hc
    simpa [maskInverted, put, replace8, low8, UintCodec.Small.get, Reg64s.set64, Reg64s.get64,
      BitVec.replaceLow, BitVec.take, BitVec.drop, Effects.All] using next

theorem mask_and (e : Executable) (base : Int64) (hc : CodeAt e base)
    (list : Bool) (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (maskApplied s flags, base + if list then 562 else 789)) :
    Eventually (step e) P (s, base + if list then 560 else 787) := by
  cases list
  · emit_step 166 using hc
    constructor
    all_goals simpa [maskApplied, putF, put, replace8, low8, UintCodec.Small.get, Reg64s.set64, Reg64s.get64,
      BitVec.replaceLow, BitVec.take, BitVec.drop, Effects.All] using next _
  · emit_step 106 using hc
    constructor
    all_goals simpa [maskApplied, putF, put, replace8, low8, UintCodec.Small.get, Reg64s.set64, Reg64s.get64,
      BitVec.replaceLow, BitVec.take, BitVec.drop, Effects.All] using next _

def delimiterSeed (s : MachineData) : MachineData :=
  put (put s .rdx (replace8 (UintCodec.Small.get s .rdx) 1#8)) .rcx (low32 (UintCodec.Small.get s .rbp))

theorem delimiter_seed (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (delimiterSeed s, base + 566)) :
    Eventually (step e) P (s, base + 562) := by
  emit_step 107 using hc
  emit_step 108 using hc
  simpa [delimiterSeed, put, replace8, low32, UintCodec.Small.get, Reg64s.set64, Reg64s.get64,
    BitVec.replaceLow, BitVec.take, BitVec.drop, Effects.All] using next

def delimiterApplied (s : MachineData) (flags : StatusFlags) : MachineData :=
  putF s .rdx (replace8 (UintCodec.Small.get s .rdx) (low8 (UintCodec.Small.get s .rdx) ||| low8 (UintCodec.Small.get s .rax))) flags

theorem delimiter_or (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (delimiterApplied s flags, base + 1160)) :
    Eventually (step e) P (s, base + 568) := by
  emit_step 110 using hc
  constructor
  all_goals
    emit_step 111 using hc
    simpa [delimiterApplied, putF, put, replace8, low8, UintCodec.Small.get, Reg64s.set64, Reg64s.get64,
      BitVec.replaceLow, BitVec.take, BitVec.drop, Effects.All, Int64.add_assoc] using next _

end SszX86.Emit.Bits
