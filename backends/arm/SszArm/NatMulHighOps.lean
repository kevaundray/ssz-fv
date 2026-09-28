import SszArm.NatMulExec
import SszArm.NatMulWordHighFrame

namespace SszArm.NatMul

def highSaveOps : List Op := [.p760, .p764, .p768, .p772, .p776, .p780, .p784]
def highCore0 : List Op := [.p788, .p792, .p796, .p800]
def highCore1 : List Op := [.p804, .p808, .p812]
def highCore2 : List Op := [.p816, .p820, .p824, .p828]
def highCore3 : List Op := [.p832, .p836, .p840]
def highCoreOps : List Op := highCore0 ++ highCore1 ++ highCore2 ++ highCore3
def highRestoreOps : List Op := [.p844, .p848, .p852, .p856, .p860, .p864, .p868]
def highSaved : List (BitVec 5) := [9#5, 10#5, 11#5, 12#5, 13#5, 15#5]

def highSpilled (s : ArmState) : ArmState :=
  NatMulSpill.six s (r (.GPR 31#5) s)
    (r (.GPR 9#5) s) (r (.GPR 10#5) s) (r (.GPR 11#5) s)
    (r (.GPR 12#5) s) (r (.GPR 13#5) s) (r (.GPR 15#5) s)

theorem high_save_word (s : ArmState) (base : BitVec 64) :
    block base highSaveOps s = NatMulWord.block base NatMulWord.HighSite.first.saveOps s := rfl

theorem high_restore_word (s : ArmState) (base : BitVec 64) :
    block base highRestoreOps s = NatMulWord.block base NatMulWord.HighSite.first.restoreOps s := rfl

theorem high_core1_word (s : ArmState) (base : BitVec 64) :
    block base highCore1 s = NatMulWord.block base NatMulWord.HighSite.first.core1 s := rfl

theorem high_core2_word (s : ArmState) (base : BitVec 64) :
    block base highCore2 s = NatMulWord.block base NatMulWord.HighSite.first.core2 s := rfl

theorem high_core_split (s : ArmState) (base : BitVec 64) :
    block base highCoreOps s = block base highCore3
      (block base highCore2 (block base highCore1 (block base highCore0 s))) := by
  simp only [highCoreOps, block, List.foldl_append]

end SszArm.NatMul
