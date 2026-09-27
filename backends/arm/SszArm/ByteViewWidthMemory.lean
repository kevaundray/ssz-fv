import SszArm.UintWidth

namespace SszArm.ByteView

open UintCodec

/-- Only occupied limb bytes need separation from the lowering slot. -/
def Source (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64)) : Prop :=
  16 ≤ (r (.GPR 31) s).toNat ∧
  pointer.toNat + 8 * words.length ≤ 2 ^ 64 ∧
  (words = [] ∨ pointer.toNat + 8 * words.length ≤ (r (.GPR 31) s).toNat - 16 ∨
    (r (.GPR 31) s).toNat ≤ pointer.toNat)

def ScratchSeparated (s : ArmState) : Prop :=
  16 ≤ (r (.GPR 31#5) s).toNat ∧
  let pointer := read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s
  let count := read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s
  pointer ≠ 0#64 → count ≠ 0#64 →
    pointer.toNat + 8 * count.toNat ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ pointer.toNat

end SszArm.ByteView

namespace SszArm.UintCodec.WidthFrame

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem byteSource {s t : ArmState} (h : WidthFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : ByteView.Source s pointer words) : ByteView.Source t pointer words := by
  simpa only [ByteView.Source, h.sp] using hs

theorem byteWords {s t : ArmState} (h : WidthFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : ByteView.Source s pointer words) (hm : WidthWords s pointer words) :
    WidthWords t pointer words := by
  rcases hs with ⟨hsp, hbound, hempty | hsep⟩
  · subst words
    intro i
    exact Fin.elim0 i
  · exact h.words pointer words ⟨hsp, hbound, hsep⟩ hm

end SszArm.UintCodec.WidthFrame
