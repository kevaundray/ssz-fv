import Arm.Exec

namespace SszArm.BoolCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def entry : Nat := 604

/-- Shipped Boolean decoder body, including lowered-store scratch traffic and
RET. Offsets are relative to the private function entry. Gaps contain other
native decoder branches, not synthesized instructions or padding. -/
def program : List (Nat × BitVec 32) := [
  (604, 0xf100047f#32),
  (608, 0x54002e21#32),
  (612, 0x39400048#32),
  (616, 0x34006c68#32),
  (620, 0x7100051f#32),
  (624, 0x54006e01#32),
  (628, 0x52802008#32),
  (632, 0xd10083ff#32),
  (636, 0xf90003e9#32),
  (640, 0xf90007ea#32),
  (644, 0xf9000beb#32),
  (648, 0x91000009#32),
  (652, 0x91004129#32),
  (656, 0x53087d0b#32),
  (660, 0x39000128#32),
  (664, 0x3900052b#32),
  (668, 0xf9400beb#32),
  (672, 0xf94007ea#32),
  (676, 0xf94003e9#32),
  (680, 0x910083ff#32),
  (684, 0x140003bb#32),
  (2084, 0x52800028#32),
  (2088, 0x52800069#32),
  (2092, 0xd10043ff#32),
  (2096, 0xf90003e9#32),
  (2100, 0xf90007ea#32),
  (2104, 0x91000009#32),
  (2108, 0x9100e129#32),
  (2112, 0xd280000a#32),
  (2116, 0xf900012a#32),
  (2120, 0xd280000a#32),
  (2124, 0xf900052a#32),
  (2128, 0xf94007ea#32),
  (2132, 0xf94003e9#32),
  (2136, 0x910043ff#32),
  (2140, 0xd10043ff#32),
  (2144, 0xf90003e9#32),
  (2148, 0xf90007ea#32),
  (2152, 0x91000009#32),
  (2156, 0x91004129#32),
  (2160, 0xd280000a#32),
  (2164, 0xf900012a#32),
  (2168, 0xd280000a#32),
  (2172, 0xf900052a#32),
  (2176, 0xf94007ea#32),
  (2180, 0xf94003e9#32),
  (2184, 0x910043ff#32),
  (2188, 0xd10043ff#32),
  (2192, 0xf90003e9#32),
  (2196, 0xf90007ea#32),
  (2200, 0x91000009#32),
  (2204, 0x91008129#32),
  (2208, 0xf9000128#32),
  (2212, 0xd280000a#32),
  (2216, 0xf900052a#32),
  (2220, 0xf94007ea#32),
  (2224, 0xf94003e9#32),
  (2228, 0x910043ff#32),
  (2232, 0xf9001803#32),
  (2236, 0xb9004809#32),
  (2240, 0xa9002008#32),
  (2244, 0x1400026e#32),
  (4084, 0xd10083ff#32),
  (4088, 0xf90003e9#32),
  (4092, 0xf90007ea#32),
  (4096, 0xf9000beb#32),
  (4100, 0x91000009#32),
  (4104, 0x91004129#32),
  (4108, 0x5280000a#32),
  (4112, 0x53087d4b#32),
  (4116, 0x3900012a#32),
  (4120, 0x3900052b#32),
  (4124, 0xf9400beb#32),
  (4128, 0xf94007ea#32),
  (4132, 0xf94003e9#32),
  (4136, 0x910083ff#32),
  (4140, 0x1400005b#32),
  (4144, 0xd10043ff#32),
  (4148, 0xf90003e9#32),
  (4152, 0xf90007ea#32),
  (4156, 0x91000009#32),
  (4160, 0x9100e129#32),
  (4164, 0xd280000a#32),
  (4168, 0xf900012a#32),
  (4172, 0xd280000a#32),
  (4176, 0xf900052a#32),
  (4180, 0xf94007ea#32),
  (4184, 0xf94003e9#32),
  (4188, 0x910043ff#32),
  (4192, 0xd10043ff#32),
  (4196, 0xf90003e9#32),
  (4200, 0xf90007ea#32),
  (4204, 0x91000009#32),
  (4208, 0x9100a129#32),
  (4212, 0xd280000a#32),
  (4216, 0xf900012a#32),
  (4220, 0xd280000a#32),
  (4224, 0xf900052a#32),
  (4228, 0xf94007ea#32),
  (4232, 0xf94003e9#32),
  (4236, 0x910043ff#32),
  (4240, 0xd10043ff#32),
  (4244, 0xf90003e9#32),
  (4248, 0xf90007ea#32),
  (4252, 0x91000009#32),
  (4256, 0x91004129#32),
  (4260, 0xd280000a#32),
  (4264, 0xf900012a#32),
  (4268, 0xd280000a#32),
  (4272, 0xf900052a#32),
  (4276, 0xf94007ea#32),
  (4280, 0xf94003e9#32),
  (4284, 0x910043ff#32),
  (4288, 0xf9001008#32),
  (4292, 0x528001a8#32),
  (4296, 0x1400006a#32),
  (4504, 0xd10043ff#32),
  (4508, 0xf90003e9#32),
  (4512, 0xf90007ea#32),
  (4516, 0x91000009#32),
  (4520, 0xd280000a#32),
  (4524, 0xf900012a#32),
  (4528, 0xf94007ea#32),
  (4532, 0xf94003e9#32),
  (4536, 0x910043ff#32),
  (4540, 0x14000030#32),
  (4720, 0x52800029#32),
  (4724, 0xb9004808#32),
  (4728, 0xa9002409#32),
  (4732, 0xa9564ff4#32),
  (4736, 0xa95557f6#32),
  (4740, 0xa9545ff8#32),
  (4744, 0xa95367fa#32),
  (4748, 0xa9526ffc#32),
  (4752, 0xa9517bfd#32),
  (4756, 0x9105c3ff#32),
  (4760, 0xd65f03c0#32)]

/-- Instruction memory is immutable and separate from data in LNSym. -/
def CodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  ∀ row ∈ program,
    s.program.find? (base + BitVec.ofNat 64 row.1) = some row.2

/-- Kernel reduction checks that every actual word has an ISA decoder case. -/
theorem all_decode : program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  decide

theorem known_decode (row : Nat × BitVec 32) (hr : row ∈ program) :
    (decode_raw_inst row.2).isSome = true :=
  List.all_eq_true.mp all_decode row hr

def decoded (row : Nat × BitVec 32) (hr : row ∈ program) : ArmInst :=
  (decode_raw_inst row.2).get (known_decode row hr)

theorem step_at (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (row : Nat × BitVec 32) (hr : row ∈ program)
    (hp : read_pc s = base + BitVec.ofNat 64 row.1)
    (he : read_err s = .None) : stepi s = exec_inst (decoded row hr) s := by
  apply stepi_eq_of_fetch_inst_of_decode_raw_inst s _ row.2 _ he hp
  · exact fetch_inst_from_program.trans (hc row hr)
  · exact (Option.some_get (known_decode row hr)).symm

end SszArm.BoolCodec
