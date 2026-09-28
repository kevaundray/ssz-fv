import SszArm.NatMulActivation
import SszArm.NatMulStateFold

namespace SszArm.NatMul

inductive RestorePath where
  | tail | return
  deriving DecidableEq

def RestorePath.start : RestorePath → Nat
  | .tail => 232 | .return => 348

def RestorePath.ops : RestorePath → List Op
  | .tail => [.p232, .p236, .p240, .p244, .p248, .p252, .p256, .p260]
  | .return => [.p348, .p352, .p356, .p360, .p364, .p368, .p372]

def restored (path : RestorePath) (s : ArmState) (base : BitVec 64) : ArmState :=
  block base path.ops s

end SszArm.NatMul
