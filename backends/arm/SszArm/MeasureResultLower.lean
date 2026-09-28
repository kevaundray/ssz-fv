import SszArm.MeasureResultStatus

namespace SszArm.Measure.Result

inductive Payload where
  | word | pair | status
  deriving DecidableEq

def Payload.store (kind : Payload) (s : ArmState) (address low high : BitVec 64) : ArmState :=
  match kind with
  | .word => write_mem_bytes 8 address low s
  | .pair => write_mem_bytes 8 (address + 8#64) high (write_mem_bytes 8 address low s)
  | .status => write_mem_bytes 4 address (low.setWidth 32) s

def savedPair (s : ArmState) (tmp : BitVec 5) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (r (.GPR tmp) s)
    (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s)

inductive Lower where
  | successHeader | successLeading | successStatus | wrongExpected | wrongHeader | wrongActual | wrongReserved | scopeReserved | scopeHeader | scopeActual | limitReserved | limitHeader
  deriving DecidableEq

def Lower.start : Lower → Nat
  | .successHeader => 4152
  | .successLeading => 4192
  | .successStatus => 4232
  | .wrongExpected => 3928
  | .wrongHeader => 3976
  | .wrongActual => 4016
  | .wrongReserved => 4064
  | .scopeReserved => 3756
  | .scopeHeader => 3804
  | .scopeActual => 3852
  | .limitReserved => 2396
  | .limitHeader => 2444

def Lower.finish : Lower → Nat
  | .successHeader => 4192
  | .successLeading => 4232
  | .successStatus => 4272
  | .wrongExpected => 3976
  | .wrongHeader => 4016
  | .wrongActual => 4064
  | .wrongReserved => 4112
  | .scopeReserved => 3804
  | .scopeHeader => 3844
  | .scopeActual => 3896
  | .limitReserved => 2444
  | .limitHeader => 2484

def Lower.tmp : Lower → BitVec 5
  | .successHeader => 10#5
  | .successLeading => 10#5
  | .successStatus => 10#5
  | .wrongExpected => 10#5
  | .wrongHeader => 10#5
  | .wrongActual => 10#5
  | .wrongReserved => 10#5
  | .scopeReserved => 10#5
  | .scopeHeader => 11#5
  | .scopeActual => 10#5
  | .limitReserved => 10#5
  | .limitHeader => 11#5

def Lower.offset : Lower → BitVec 64
  | .successHeader => 0#64
  | .successLeading => 32#64
  | .successStatus => 64#64
  | .wrongExpected => 16#64
  | .wrongHeader => 0#64
  | .wrongActual => 32#64
  | .wrongReserved => 48#64
  | .scopeReserved => 48#64
  | .scopeHeader => 0#64
  | .scopeActual => 32#64
  | .limitReserved => 48#64
  | .limitHeader => 0#64

def Lower.kind : Lower → Payload
  | .successHeader => .pair
  | .successLeading => .word
  | .successStatus => .status
  | .wrongExpected => .pair
  | .wrongHeader => .pair
  | .wrongActual => .pair
  | .wrongReserved => .pair
  | .scopeReserved => .pair
  | .scopeHeader => .pair
  | .scopeActual => .pair
  | .limitReserved => .pair
  | .limitHeader => .pair

def Lower.low (kind : Lower) (s : ArmState) : BitVec 64 :=
  match kind with
  | .successHeader => r (.GPR 8#5) s
  | .successLeading => 0#64
  | .successStatus => 0#64
  | .wrongExpected => 0#64
  | .wrongHeader => r (.GPR 8#5) s
  | .wrongActual => 0#64
  | .wrongReserved => 0#64
  | .scopeReserved => 0#64
  | .scopeHeader => r (.GPR 10#5) s
  | .scopeActual => 0#64
  | .limitReserved => 0#64
  | .limitHeader => r (.GPR 10#5) s

def Lower.high (kind : Lower) (s : ArmState) : BitVec 64 :=
  match kind with
  | .successHeader => 0#64
  | .successLeading => 0#64
  | .successStatus => 0#64
  | .wrongExpected => 0#64
  | .wrongHeader => 0#64
  | .wrongActual => 0#64
  | .wrongReserved => 0#64
  | .scopeReserved => 0#64
  | .scopeHeader => 0#64
  | .scopeActual => r (.GPR 20#5) s
  | .limitReserved => 0#64
  | .limitHeader => 0#64

def Lower.ops : Lower → List Op
  | .successHeader => [p4152, p4156, p4160, p4164, p4168, p4172, p4176, p4180, p4184, p4188]
  | .successLeading => [p4192, p4196, p4200, p4204, p4208, p4212, p4216, p4220, p4224, p4228]
  | .successStatus => [p4232, p4236, p4240, p4244, p4248, p4252, p4256, p4260, p4264, p4268]
  | .wrongExpected => [p3928, p3932, p3936, p3940, p3944, p3948, p3952, p3956, p3960, p3964, p3968, p3972]
  | .wrongHeader => [p3976, p3980, p3984, p3988, p3992, p3996, p4000, p4004, p4008, p4012]
  | .wrongActual => [p4016, p4020, p4024, p4028, p4032, p4036, p4040, p4044, p4048, p4052, p4056, p4060]
  | .wrongReserved => [p4064, p4068, p4072, p4076, p4080, p4084, p4088, p4092, p4096, p4100, p4104, p4108]
  | .scopeReserved => [p3756, p3760, p3764, p3768, p3772, p3776, p3780, p3784, p3788, p3792, p3796, p3800]
  | .scopeHeader => [p3804, p3808, p3812, p3816, p3820, p3824, p3828, p3832, p3836, p3840]
  | .scopeActual => [p3852, p3856, p3860, p3864, p3868, p3872, p3876, p3880, p3884, p3888, p3892]
  | .limitReserved => [p2396, p2400, p2404, p2408, p2412, p2416, p2420, p2424, p2428, p2432, p2436, p2440]
  | .limitHeader => [p2444, p2448, p2452, p2456, p2460, p2464, p2468, p2472, p2476, p2480]

def Lower.memory (kind : Lower) (s : ArmState) : ArmState :=
  kind.kind.store (savedPair s kind.tmp) (r (.GPR 19#5) s + kind.offset)
    (kind.low s) (kind.high s)

@[irreducible] def Lower.result (kind : Lower) (s : ArmState) (base : BitVec 64) : ArmState :=
  let m := kind.memory s
  w .PC (base + BitVec.ofNat 64 kind.finish)
    (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) m)
      (w (.GPR kind.tmp) (read_mem_bytes 8 (r (.GPR 31#5) s - 8#64) m) m))

end SszArm.Measure.Result
