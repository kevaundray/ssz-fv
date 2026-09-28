import SszArm.NatMulWordExec
import SszArm.NatMulSpill
import SszArm.NatMulProduct

namespace SszArm.NatMulWord
inductive HighSite where
  | first | loop | small
  deriving DecidableEq

def HighSite.start : HighSite → Nat
  | .first => 480
  | .loop => 636
  | .small => 928

def HighSite.left : HighSite → BitVec 5
  | .first => 14#5
  | .loop => 17#5
  | .small => 2#5

def HighSite.destination : HighSite → BitVec 5
  | .first => 14#5
  | .loop => 17#5
  | .small => 9#5

def HighSite.saved : HighSite → List (BitVec 5)
  | .first => [9#5, 10#5, 11#5, 12#5, 13#5, 15#5]
  | .loop => [9#5, 10#5, 11#5, 12#5, 13#5, 14#5]
  | .small => [10#5, 11#5, 12#5, 13#5, 14#5, 15#5]

def HighSite.saveOps : HighSite → List Op
  | .first => [.p480, .p484, .p488, .p492, .p496, .p500, .p504]
  | .loop => [.p636, .p640, .p644, .p648, .p652, .p656, .p660]
  | .small => [.p928, .p932, .p936, .p940, .p944, .p948, .p952]

def HighSite.coreOps : HighSite → List Op
  | .first => [.p508, .p512, .p516, .p520, .p524, .p528, .p532, .p536, .p540, .p544, .p548, .p552, .p556, .p560]
  | .loop => [.p664, .p668, .p672, .p676, .p680, .p684, .p688, .p692, .p696, .p700, .p704, .p708, .p712, .p716]
  | .small => [.p956, .p960, .p964, .p968, .p972, .p976, .p980, .p984, .p988, .p992, .p996, .p1000, .p1004, .p1008]

def HighSite.restoreOps : HighSite → List Op
  | .first => [.p564, .p568, .p572, .p576, .p580, .p584, .p588]
  | .loop => [.p720, .p724, .p728, .p732, .p736, .p740, .p744]
  | .small => [.p1012, .p1016, .p1020, .p1024, .p1028, .p1032, .p1036]

def HighSite.spilled (site : HighSite) (s : ArmState) : ArmState :=
  NatMulSpill.six s (r (.GPR 31#5) s)
    (r (.GPR site.saved[0]!) s) (r (.GPR site.saved[1]!) s)
    (r (.GPR site.saved[2]!) s) (r (.GPR site.saved[3]!) s)
    (r (.GPR site.saved[4]!) s) (r (.GPR site.saved[5]!) s)

end SszArm.NatMulWord
