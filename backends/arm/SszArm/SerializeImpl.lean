import SszArm.MeasureImpl
import SszArm.EmitImpl

namespace SszArm.Serialize

def entry : Nat := 0
def measureOffset : BitVec 64 := -38108#64
def emitOffset : BitVec 64 := -33756#64

private def bodyWords0 : List (Nat × BitVec 32) := [
  (0, 0xd10243ff#32),
  (4, 0xa9065ffe#32),
  (8, 0xa90757f6#32),
  (12, 0xa9084ff4#32),
  (16, 0xaa0403f7#32),
  (20, 0xaa0303f4#32),
  (24, 0xaa0003f3#32),
  (28, 0x910063e0#32),
  (32, 0xaa0503e3#32),
  (36, 0x52800024#32),
  (40, 0xaa0203f5#32),
  (44, 0xaa0103f6#32),
  (48, 0x97ffdabd#32),
  (52, 0xa941b3eb#32),
  (56, 0xb9405be9#32),
  (60, 0xa94297e8#32),
  (64, 0xf9401fea#32),
  (68, 0xa900b3eb#32),
  (72, 0x34000209#32),
  (76, 0xa94433eb#32),
  (80, 0xf9402bed#32),
  (84, 0xa9011668#32),
  (88, 0xb9405fe8#32),
  (92, 0xf9001e6d#32),
  (96, 0xa902b26b#32),
  (100, 0xa940b3eb#32),
  (104, 0xf900126a#32),
  (108, 0x29082269#32),
  (112, 0xa900326b#32),
  (116, 0xa9484ff4#32),
  (120, 0xa94757f6#32),
  (124, 0xa9465ffe#32),
  (128, 0x910243ff#32),
  (132, 0xd65f03c0#32),
  (136, 0xa940afe9#32),
  (140, 0xa90297e8#32),
  (144, 0xf9001fea#32),
  (148, 0xa901afe9#32),
  (152, 0xb4000888#32),
  (156, 0xd10004aa#32),
  (160, 0xb100055f#32),
  (164, 0x540007e0#32),
  (168, 0xd10043ff#32),
  (172, 0xf90003e9#32),
  (176, 0xaa0a03e9#32),
  (180, 0xd37df129#32),
  (184, 0x8b090109#32),
  (188, 0xf940012b#32),
  (192, 0xf94003e9#32),
  (196, 0x910043ff#32),
  (200, 0xaa0a03e9#32),
  (204, 0xd100054a#32),
  (208, 0xb4fffe8b#32),
  (212, 0x91000529#32),
  (216, 0xf100053f#32),
  (220, 0x54000640#32),
  (224, 0x52800028#32),
  (228, 0xd10043ff#32),
  (232, 0xf90003e9#32),
  (236, 0xf90007ea#32),
  (240, 0x91000269#32),
  (244, 0x9100c129#32),
  (248, 0xd280000a#32),
  (252, 0xf900012a#32),
  (256, 0xd280000a#32),
  (260, 0xf900052a#32),
  (264, 0xf94007ea#32),
  (268, 0xf94003e9#32),
  (272, 0x910043ff#32),
  (276, 0xd10043ff#32),
  (280, 0xf90003e9#32),
  (284, 0xf90007ea#32),
  (288, 0x91000269#32),
  (292, 0x91008129#32),
  (296, 0xd280000a#32),
  (300, 0xf900012a#32),
  (304, 0xd280000a#32),
  (308, 0xf900052a#32),
  (312, 0xf94007ea#32),
  (316, 0xf94003e9#32),
  (320, 0x910043ff#32),
  (324, 0xd10043ff#32),
  (328, 0xf90003e9#32),
  (332, 0xf90007ea#32),
  (336, 0x91000269#32),
  (340, 0x91004129#32),
  (344, 0xd280000a#32),
  (348, 0xf900012a#32),
  (352, 0xd280000a#32),
  (356, 0xf900052a#32),
  (360, 0xf94007ea#32),
  (364, 0xf94003e9#32),
  (368, 0x910043ff#32),
  (372, 0xd10043ff#32),
  (376, 0xf90003e9#32),
  (380, 0xf90007ea#32),
  (384, 0x91000269#32),
  (388, 0xf9000128#32),
  (392, 0xd280000a#32),
  (396, 0xf900052a#32)]

private def bodyWords1 : List (Nat × BitVec 32) := [
  (400, 0xf94007ea#32),
  (404, 0xf94003e9#32),
  (408, 0x910043ff#32),
  (412, 0x14000034#32),
  (416, 0xb4000745#32),
  (420, 0xf9400105#32),
  (424, 0xeb0502ff#32),
  (428, 0x540006e2#32),
  (432, 0x52800028#32),
  (436, 0xd10043ff#32),
  (440, 0xf90003e9#32),
  (444, 0xf90007ea#32),
  (448, 0x91000269#32),
  (452, 0x91004129#32),
  (456, 0xd280000a#32),
  (460, 0xf900012a#32),
  (464, 0xd280000a#32),
  (468, 0xf900052a#32),
  (472, 0xf94007ea#32),
  (476, 0xf94003e9#32),
  (480, 0x910043ff#32),
  (484, 0xd10043ff#32),
  (488, 0xf90003e9#32),
  (492, 0xf90007ea#32),
  (496, 0x91000269#32),
  (500, 0xf9000128#32),
  (504, 0xd280000a#32),
  (508, 0xf900052a#32),
  (512, 0xf94007ea#32),
  (516, 0xf94003e9#32),
  (520, 0x910043ff#32),
  (524, 0xd10043ff#32),
  (528, 0xf90003e9#32),
  (532, 0xf90007ea#32),
  (536, 0x91000269#32),
  (540, 0x91008129#32),
  (544, 0xd280000a#32),
  (548, 0xf900012a#32),
  (552, 0xd280000a#32),
  (556, 0xf900052a#32),
  (560, 0xf94007ea#32),
  (564, 0xf94003e9#32),
  (568, 0x910043ff#32),
  (572, 0xd10043ff#32),
  (576, 0xf90003e9#32),
  (580, 0xf90007ea#32),
  (584, 0x91000269#32),
  (588, 0x9100c129#32),
  (592, 0xd280000a#32),
  (596, 0xf900012a#32),
  (600, 0xd280000a#32),
  (604, 0xf900052a#32),
  (608, 0xf94007ea#32),
  (612, 0xf94003e9#32),
  (616, 0x910043ff#32),
  (620, 0x52900028#32),
  (624, 0xb9004268#32),
  (628, 0xa9484ff4#32),
  (632, 0xa94757f6#32),
  (636, 0xa9465ffe#32),
  (640, 0x910243ff#32),
  (644, 0xd65f03c0#32),
  (648, 0x910063e3#32),
  (652, 0xaa1303e0#32),
  (656, 0xaa1603e1#32),
  (660, 0xaa1503e2#32),
  (664, 0xaa1403e4#32),
  (668, 0x97ffde62#32),
  (672, 0xa9484ff4#32),
  (676, 0xa94757f6#32),
  (680, 0xa9465ffe#32),
  (684, 0x910243ff#32),
  (688, 0xd65f03c0#32)]

/-- Actual standalone native serialize wrapper, with its original entry and calls. -/
def bodyProgram : List (Nat × BitVec 32) := bodyWords0 ++ bodyWords1

def frontiers : List Nat := []

/-- Structural ownership only: the wrapper and its primitive callees share one program. -/
structure CodeAt (s : ArmState) (base : BitVec 64) : Prop where
  body : ∀ row ∈ bodyProgram,
    s.program.find? (base + BitVec.ofNat 64 row.1) = some row.2
  measure : Measure.CodeAt s (base + measureOffset)
  emit : Emit.CodeAt s (base + emitOffset)

theorem body_codeAt {s : ArmState} {base : BitVec 64} (code : CodeAt s base)
    (row : Nat × BitVec 32) (member : row ∈ bodyProgram) :
    s.program.find? (base + BitVec.ofNat 64 row.1) = some row.2 :=
  code.body row member

theorem measure_codeAt {s : ArmState} {base : BitVec 64} (code : CodeAt s base) :
    Measure.CodeAt s (base + measureOffset) := code.measure

theorem emit_codeAt {s : ArmState} {base : BitVec 64} (code : CodeAt s base) :
    Emit.CodeAt s (base + emitOffset) := code.emit

theorem compare_codeAt {s : ArmState} {base : BitVec 64} (code : CodeAt s base) :
    NatCompare.CodeAt s (base + measureOffset + Measure.compareOffset) :=
  code.measure.compare

theorem fromU128_codeAt {s : ArmState} {base : BitVec 64} (code : CodeAt s base) :
    NatFromU128.CodeAt s (base + measureOffset + Measure.fromU128Offset) :=
  code.measure.fromU128

theorem memcpy_codeAt {s : ArmState} {base : BitVec 64} (code : CodeAt s base) :
    SszArm.CodeAt s (base + measureOffset + Measure.memcpyOffset) Memcpy.program :=
  code.measure.memcpy

theorem CodeAt.congr {s t : ArmState} {base : BitVec 64} (code : CodeAt s base)
    (same : t.program = s.program) : CodeAt t base := by
  constructor
  · intro row member; simpa only [same] using code.body row member
  · exact code.measure.congr same
  · intro row member; simpa only [same] using code.emit row member

end SszArm.Serialize
