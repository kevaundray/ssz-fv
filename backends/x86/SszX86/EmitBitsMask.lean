import SszX86.EmitBitsByteOps

namespace SszX86.Emit.Bits
open UintCodec.Small (put putF low8 low32 replace8)

@[simp] private theorem low_append (hi : BitVec 56) (lo : BitVec 8) :
    (hi ++ lo).setWidth 8 = lo :=
  BitVec.setWidth_append_eq_right (a := hi) (b := lo)

@[simp] private theorem high_append (hi : BitVec 56) (lo : BitVec 8) :
    (hi ++ lo).extractLsb' 8 56 = hi :=
  BitVec.extractLsb'_append_eq_left (a := hi) (b := lo)

/-- All bits above AL/DL retain their native values. -/
def masked (s : MachineData) (remainder : Nat) (flags : StatusFlags) : MachineData :=
  putF (put s .rdx (replace8 (UintCodec.Small.get s .rdx) (~~~(255#8 <<< remainder)))) .rax
    (replace8 (UintCodec.Small.get s .rax) (maskByte (low8 (UintCodec.Small.get s .rax)) remainder)) flags

theorem mask_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (list : Bool) (s : MachineData) (remainder : Nat) (small : remainder < 8)
    (count : low8 (UintCodec.Small.get s .rcx) = BitVec.ofNat 8 remainder)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (masked s remainder flags, base + if list then 562 else 789)) :
    Eventually (step e) P (s, base + if list then 554 else 781) := by
  apply mask_seed e base hc list s P
  cases list
  · apply shift_byte e base hc .vectorMask (maskSeed s) remainder small
    · simpa [maskSeed, put, UintCodec.Small.get, Reg64s.get64, Reg64s.set64] using count
    intro flags
    apply mask_not e base hc false
    apply mask_and e base hc false
    intro finalFlags
    simpa [masked, maskByte, maskApplied, maskInverted, maskSeed, putF, put,
      UintCodec.Small.get, low8, replace8, Reg64s.set64, Reg64s.get64, BitVec.replaceLow,
      BitVec.drop] using next finalFlags
  · apply shift_byte e base hc .listMask (maskSeed s) remainder small
    · simpa [maskSeed, put, UintCodec.Small.get, Reg64s.get64, Reg64s.set64] using count
    intro flags
    apply mask_not e base hc true
    apply mask_and e base hc true
    intro finalFlags
    simpa [masked, maskByte, maskApplied, maskInverted, maskSeed, putF, put,
      UintCodec.Small.get, low8, replace8, Reg64s.set64, Reg64s.get64, BitVec.replaceLow,
      BitVec.drop] using next finalFlags

def delimited (s : MachineData) (remainder : Nat) (flags : StatusFlags) : MachineData :=
  putF (put s .rcx (low32 (UintCodec.Small.get s .rbp))) .rdx
    (replace8 (UintCodec.Small.get s .rdx) ((1#8 <<< remainder) ||| low8 (UintCodec.Small.get s .rax))) flags

theorem delimiter_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (remainder : Nat) (small : remainder < 8)
    (count : low8 (low32 (UintCodec.Small.get s .rbp)) = BitVec.ofNat 8 remainder)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (delimited s remainder flags, base + 1160)) :
    Eventually (step e) P (s, base + 562) := by
  apply delimiter_seed e base hc s P
  apply shift_byte e base hc .delimiter (delimiterSeed s) remainder small
  · simpa [delimiterSeed, put, UintCodec.Small.get, Reg64s.get64, Reg64s.set64] using count
  intro flags
  apply delimiter_or e base hc
  intro finalFlags
  simpa [delimited, delimiterApplied, delimiterSeed, putF, put, UintCodec.Small.get, low8, low32,
    replace8, Reg64s.set64, Reg64s.get64, BitVec.replaceLow,
    BitVec.drop] using next finalFlags

end SszX86.Emit.Bits
