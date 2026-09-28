import SszX86.EmitUintInstructions

namespace SszX86.Emit.Uint.Instructions
open Kraken.X64.Parser
open BoolCodec UintCodec
open UintCodec.Large (get put putF compare subFlags shift)

@[simp] private theorem take8 (v : BitVec 64) :
    v.extractLsb' 0 8 = v.setWidth 8 := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]

@[simp] private theorem take32 (v : BitVec 64) :
    v.extractLsb' 0 32 = v.setWidth 32 := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]

private theorem all_if (P : MachineState → Prop) (p : Prop) [Decidable p]
    (a b : Effects) : Effects.All P (if p then a else b) ↔
      (p → Effects.All P a) ∧ (¬ p → Effects.All P b) := by
  by_cases h : p <;> simp [h]

@[simp] private theorem mask_lt (n : Nat) : n &&& 63 < 64 := by
  have bound : n &&& 63 ≤ 63 := Nat.and_le_right
  omega

@[simp] private theorem mask_one (n : Nat) (one : n &&& 63 = 1) :
    (UInt64.ofNat n &&& 63 : UInt64) = 1 := by
  have cast := congrArg UInt64.ofNat one
  simpa only [UInt64.ofNat_and, show UInt64.ofNat 63 = (63 : UInt64) from rfl,
    UInt64.ofNat_one] using cast

/-- Each generated declaration uses exactly one bounded literal image row. -/
macro "emit_uint_certificate " name:ident " : " pc:num " , " row:num : command => `(command|
  theorem $name:ident (e : Executable) (base : Int64) (hc : CodeAt e base)
      (s : MachineData) (limb : BitVec 64)
      (read : Read $pc s limb) (writable : Writable $pc s)
      (P : MachineState → Prop)
      (continuation : ∀ flags, Eventually (step e) P
        (instruction $pc s limb flags, base + Int64.ofNat (next $pc s))) :
      Eventually (step e) P (s, base + Int64.ofNat $pc) := by
    have t653 := hc.targets ("emit_u653", 653) (by decide)
    have t644 := hc.targets ("emit_u644", 644) (by decide)
    have t876 := hc.targets ("emit_u876", 876) (by decide)
    have t893 := hc.targets ("emit_u893", 893) (by decide)
    have t912 := hc.targets ("emit_u912", 912) (by decide)
    have t976 := hc.targets ("emit_u976", 976) (by decide)
    have t1002 := hc.targets ("emit_u1002", 1002) (by decide)
    have t1031 := hc.targets ("emit_u1031", 1031) (by decide)
    have t1035 := hc.targets ("emit_u1035", 1035) (by decide)
    have t1056 := hc.targets ("emit_u1056", 1056) (by decide)
    have t1147 := hc.targets ("emit_u1147", 1147) (by decide)
    have t1615 := hc.targets ("emit_u1615", 1615) (by decide)
    simp only [Read, Writable, readAddress, storeAddress, storeWidth,
      Nat.reduceEqDiff, or_true, true_or, or_false, false_or, true_implies,
      false_implies, ↓reduceIte, UintCodec.Large.get, Reg64s.get64] at read writable
    try obtain ⟨old, oldRead⟩ := writable
    emit_step $row using hc
    try simp (config := {instances := true})
      [MachineData.load, MachineData.store, Width.bytes, Width.bits, Effects.All,
        read, oldRead, cast64, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
        ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
        BitVec.take, BitVec.signed, all_if,
        t653, t644, t876, t893, t912, t976, t1002, t1031, t1035, t1056, t1147, t1615]
    try simp (config := {instances := true})
      [MachineData.load, Width.bytes, Width.bits, Effects.All,
        read, cast64, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
        ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
        BitVec.take, BitVec.signed, all_if,
        t653, t644, t876, t893, t912, t976, t1002, t1031, t1035, t1056, t1147, t1615]
    simp only [instruction, next, UintCodec.Large.put, UintCodec.Large.putF,
      UintCodec.Large.get, UintCodec.Large.compare, UintCodec.Large.subFlags, UintCodec.Large.shift,
      low8, low32, test, store, Reg64s.set64, Reg64s.get64,
      BitVec.take, BitVec.drop, BitVec.replaceLow, BitVec.signed] at continuation
    repeat' first | apply And.intro | intro
    all_goals try simp_all (config := {instances := true})
      [Effects.All, all_if, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
        BitVec.extractLsb'_append_eq_right, BitVec.add_comm, BitVec.add_assoc,
        BitVec.mul_comm, BitVec.take, BitVec.signed, UInt64.add_comm, UInt64.mul_comm]
    all_goals first
      | exact continuation s.status
      | exact continuation {s.status with af := false}
      | exact continuation {s.status with af := true}
      | exact continuation _)

emit_uint_certificate at583 : 583, 115
theorem at586 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (read : Read 586 s limb) (writable : Writable 586 s)
    (P : MachineState → Prop)
    (continuation : ∀ flags, Eventually (step e) P
      (instruction 586 s limb flags, base + Int64.ofNat (next 586 s))) :
    Eventually (step e) P (s, base + Int64.ofNat 586) := by
  simp only [Read, Writable, Nat.reduceEqDiff, or_false, false_implies] at read writable
  cases read
  cases writable
  have target := hc.targets ("emit_u1615", 1615) (by decide)
  have selected := continuation s.status
  simp only [instruction, next] at selected
  emit_step 116 using hc
  rw [target]
  cases cf : s.status.cf <;> cases zf : s.status.zf
  all_goals simpa [cf, zf, Effects.All] using selected
emit_uint_certificate at592 : 592, 117
emit_uint_certificate at595 : 595, 118
emit_uint_certificate at597 : 597, 119
emit_uint_certificate at602 : 602, 120
emit_uint_certificate at607 : 607, 121
emit_uint_certificate at610 : 610, 122
emit_uint_certificate at616 : 616, 123
emit_uint_certificate at620 : 620, 124
emit_uint_certificate at626 : 626, 125
emit_uint_certificate at628 : 628, 126
emit_uint_certificate at631 : 631, 127
emit_uint_certificate at635 : 635, 128
emit_uint_certificate at638 : 638, 129
emit_uint_certificate at644 : 644, 130
emit_uint_certificate at648 : 648, 131
emit_uint_certificate at653 : 653, 132
emit_uint_certificate at655 : 655, 133
emit_uint_certificate at658 : 658, 134
emit_uint_certificate at876 : 876, 180
emit_uint_certificate at880 : 880, 181
emit_uint_certificate at886 : 886, 182
emit_uint_certificate at888 : 888, 183
emit_uint_certificate at893 : 893, 184
emit_uint_certificate at896 : 896, 185
emit_uint_certificate at900 : 900, 186
emit_uint_certificate at903 : 903, 187
emit_uint_certificate at905 : 905, 188
emit_uint_certificate at912 : 912, 189
emit_uint_certificate at916 : 916, 190
emit_uint_certificate at919 : 919, 191
emit_uint_certificate at922 : 922, 192
emit_uint_certificate at925 : 925, 193
emit_uint_certificate at928 : 928, 194
emit_uint_certificate at933 : 933, 195
emit_uint_certificate at937 : 937, 196
emit_uint_certificate at941 : 941, 197
emit_uint_certificate at944 : 944, 198
emit_uint_certificate at946 : 946, 199
emit_uint_certificate at949 : 949, 200
emit_uint_certificate at953 : 953, 201
emit_uint_certificate at956 : 956, 202
emit_uint_certificate at958 : 958, 203
emit_uint_certificate at962 : 962, 204
emit_uint_certificate at976 : 976, 205
emit_uint_certificate at979 : 979, 206
emit_uint_certificate at982 : 982, 207
emit_uint_certificate at985 : 985, 208
emit_uint_certificate at988 : 988, 209
emit_uint_certificate at992 : 992, 210
emit_uint_certificate at995 : 995, 211
emit_uint_certificate at997 : 997, 212
emit_uint_certificate at1000 : 1000, 213
emit_uint_certificate at1002 : 1002, 214
emit_uint_certificate at1006 : 1006, 215
emit_uint_certificate at1012 : 1012, 216
emit_uint_certificate at1015 : 1015, 217
emit_uint_certificate at1018 : 1018, 218
emit_uint_certificate at1022 : 1022, 219
emit_uint_certificate at1025 : 1025, 220
emit_uint_certificate at1031 : 1031, 221
emit_uint_certificate at1033 : 1033, 222
emit_uint_certificate at1035 : 1035, 223
emit_uint_certificate at1038 : 1038, 224
emit_uint_certificate at1042 : 1042, 225
emit_uint_certificate at1045 : 1045, 226
emit_uint_certificate at1047 : 1047, 227
emit_uint_certificate at1056 : 1056, 228
emit_uint_certificate at1059 : 1059, 229
emit_uint_certificate at1063 : 1063, 230
emit_uint_certificate at1069 : 1069, 231
emit_uint_certificate at1073 : 1073, 232
emit_uint_certificate at1076 : 1076, 233
emit_uint_certificate at1079 : 1079, 234
emit_uint_certificate at1082 : 1082, 235
emit_uint_certificate at1085 : 1085, 236
emit_uint_certificate at1089 : 1089, 237
emit_uint_certificate at1092 : 1092, 238
emit_uint_certificate at1095 : 1095, 239
emit_uint_certificate at1099 : 1099, 240
emit_uint_certificate at1104 : 1104, 241
emit_uint_certificate at1108 : 1108, 242
emit_uint_certificate at1111 : 1111, 243
emit_uint_certificate at1113 : 1113, 244
emit_uint_certificate at1117 : 1117, 245
emit_uint_certificate at1119 : 1119, 246
emit_uint_certificate at1122 : 1122, 247
emit_uint_certificate at1126 : 1126, 248
emit_uint_certificate at1128 : 1128, 249
theorem at1132 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (read : Read 1132 s limb) (writable : Writable 1132 s)
    (P : MachineState → Prop)
    (continuation : ∀ flags, Eventually (step e) P
      (instruction 1132 s limb flags, base + Int64.ofNat (next 1132 s))) :
    Eventually (step e) P (s, base + Int64.ofNat 1132) := by
  simp only [Read, Writable, Nat.reduceEqDiff, or_false, false_implies] at read writable
  cases read
  cases writable
  have selected := continuation s.status
  simp only [instruction, next, UintCodec.Large.put, UintCodec.Large.get,
    Reg64s.set64, Reg64s.get64] at selected
  emit_step 250 using hc
  cases cf : s.status.cf <;> simpa [cf, Effects.All] using selected
emit_uint_certificate at1136 : 1136, 251
emit_uint_certificate at1139 : 1139, 252
emit_uint_certificate at1141 : 1141, 253
emit_uint_certificate at1144 : 1144, 254
emit_uint_certificate at1147 : 1147, 255
emit_uint_certificate at1150 : 1150, 256

end SszX86.Emit.Uint.Instructions
