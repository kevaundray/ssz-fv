import SszArm.EmitUintWidthOps

namespace SszArm.Emit.Uint

inductive ByteOp where
  | p916 | p920 | p924 | p928 | p932 | p936 | p940 | p944 | p948 | p952 | p956 | p960
  | p964 | p968 | p972 | p976 | p980 | p984 | p988 | p992 | p996 | p1000
  | p1072 | p1076 | p1080 | p1084 | p1088 | p1092 | p1096 | p1100 | p1104 | p1108
  | p1112 | p1116 | p1120 | p1124 | p1128 | p1132 | p1136 | p1140 | p1144 | p1148
  | p1152 | p1156 | p1160 | p1164 | p1168 | p1172 | p1176
  deriving DecidableEq

def ByteOp.row : ByteOp → Nat × BitVec 32
  | .p916 => (916, 0xa940a2c9#32)
  | .p920 => (920, 0xaa1f03ea#32)
  | .p924 => (924, 0xb4000069#32)
  | .p928 => (928, 0xaa1f03eb#32)
  | .p932 => (932, 0x14000032#32)
  | .p936 => (936, 0xf100215f#32)
  | .p940 => (940, 0x927d092d#32)
  | .p944 => (944, 0x9100054b#32)
  | .p948 => (948, 0x9a9f310c#32)
  | .p952 => (952, 0xeb0b003f#32)
  | .p956 => (956, 0x91002129#32)
  | .p960 => (960, 0x9acd258c#32)
  | .p964 => (964, 0xd10043ff#32)
  | .p968 => (968, 0xf90003e9#32)
  | .p972 => (972, 0xaa0a03e9#32)
  | .p976 => (976, 0x8b090289#32)
  | .p980 => (980, 0x3900012c#32)
  | .p984 => (984, 0xf94003e9#32)
  | .p988 => (988, 0x910043ff#32)
  | .p992 => (992, 0xaa0b03ea#32)
  | .p996 => (996, 0x54fffe21#32)
  | .p1000 => (1000, 0xf9000261#32)
  | .p1072 => (1072, 0xaa1f03ec#32)
  | .p1076 => (1076, 0x927d094e#32)
  | .p1080 => (1080, 0x9100056d#32)
  | .p1084 => (1084, 0x9100214a#32)
  | .p1088 => (1088, 0x9ace258c#32)
  | .p1092 => (1092, 0xeb0d003f#32)
  | .p1096 => (1096, 0xd10043ff#32)
  | .p1100 => (1100, 0xf90003e9#32)
  | .p1104 => (1104, 0xaa0b03e9#32)
  | .p1108 => (1108, 0x8b090289#32)
  | .p1112 => (1112, 0x3900012c#32)
  | .p1116 => (1116, 0xf94003e9#32)
  | .p1120 => (1120, 0x910043ff#32)
  | .p1124 => (1124, 0xaa0d03eb#32)
  | .p1128 => (1128, 0x54fffc00#32)
  | .p1132 => (1132, 0xd343fd6c#32)
  | .p1136 => (1136, 0xeb08019f#32)
  | .p1140 => (1140, 0x54fffde2#32)
  | .p1144 => (1144, 0xd10043ff#32)
  | .p1148 => (1148, 0xf90003ea#32)
  | .p1152 => (1152, 0xaa0c03ea#32)
  | .p1156 => (1156, 0xd37df14a#32)
  | .p1160 => (1160, 0x8b0a012a#32)
  | .p1164 => (1164, 0xf940014c#32)
  | .p1168 => (1168, 0xf94003ea#32)
  | .p1172 => (1172, 0x910043ff#32)
  | .p1176 => (1176, 0x17ffffe7#32)

def ByteOp.effect (base : BitVec 64) : ByteOp → ArmState → ArmState
  | .p916, s => w (.GPR 8#5) (read_mem_bytes 8 (r (.GPR 22#5) s + 16#64) s)
      (put 9 (read_mem_bytes 8 (r (.GPR 22#5) s + 8#64) s) s)
  | .p920, s => put 10 0#64 s
  | .p924, s => w .PC (if r (.GPR 9#5) s = 0#64 then base + 936#64 else base + 928#64) s
  | .p928, s => put 11 0#64 s
  | .p932, s => w .PC (base + 1132#64) s
  | .p936, s => Dispatch.compare64 (r (.GPR 10#5) s) 8#64 s
  | .p940, s => put 13 (r (.GPR 9#5) s &&& 56#64) s
  | .p944, s => put 11 (r (.GPR 10#5) s + 1#64) s
  | .p948, s => put 12 (if r (.FLAG .C) s = 1#1 then 0#64 else r (.GPR 8#5) s) s
  | .p952, s => Dispatch.compare64 (r (.GPR 1#5) s) (r (.GPR 11#5) s) s
  | .p956, s => put 9 (r (.GPR 9#5) s + 8#64) s
  | .p960, s => put 12 (r (.GPR 12#5) s >>> ((r (.GPR 13#5) s).toNat % 64)) s
  | .p964, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p968, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p972, s => put 9 (r (.GPR 10#5) s) s
  | .p976, s => put 9 (r (.GPR 20#5) s + r (.GPR 9#5) s) s
  | .p980, s => next (write_mem_bytes 1 (r (.GPR 9#5) s) ((r (.GPR 12#5) s).setWidth 8) s)
  | .p984, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p988, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p992, s => put 10 (r (.GPR 11#5) s) s
  | .p996, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 1000#64 else base + 936#64) s
  | .p1000, s => next (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 1#5) s) s)
  | .p1072, s => put 12 0#64 s
  | .p1076, s => put 14 (r (.GPR 10#5) s &&& 56#64) s
  | .p1080, s => put 13 (r (.GPR 11#5) s + 1#64) s
  | .p1084, s => put 10 (r (.GPR 10#5) s + 8#64) s
  | .p1088, s => put 12 (r (.GPR 12#5) s >>> ((r (.GPR 14#5) s).toNat % 64)) s
  | .p1092, s => Dispatch.compare64 (r (.GPR 1#5) s) (r (.GPR 13#5) s) s
  | .p1096, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p1100, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p1104, s => put 9 (r (.GPR 11#5) s) s
  | .p1108, s => put 9 (r (.GPR 20#5) s + r (.GPR 9#5) s) s
  | .p1112, s => next (write_mem_bytes 1 (r (.GPR 9#5) s) ((r (.GPR 12#5) s).setWidth 8) s)
  | .p1116, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p1120, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p1124, s => put 11 (r (.GPR 13#5) s) s
  | .p1128, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 1000#64 else base + 1132#64) s
  | .p1132, s => put 12 (r (.GPR 11#5) s >>> 3) s
  | .p1136, s => Dispatch.compare64 (r (.GPR 12#5) s) (r (.GPR 8#5) s) s
  | .p1140, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 1072#64 else base + 1144#64) s
  | .p1144, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p1148, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p1152, s => put 10 (r (.GPR 12#5) s) s
  | .p1156, s => put 10 (r (.GPR 10#5) s <<< 3) s
  | .p1160, s => put 10 (r (.GPR 9#5) s + r (.GPR 10#5) s) s
  | .p1164, s => put 12 (read_mem_bytes 8 (r (.GPR 10#5) s) s) s
  | .p1168, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p1172, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p1176, s => w .PC (base + 1076#64) s

end SszArm.Emit.Uint
