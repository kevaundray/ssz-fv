import SszArm.BoolActivation
import SszNatMemory
import SszWidth

namespace SszArm.UintCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Absolute observer for the total architectural byte memory. -/
def widthLoad (s : ArmState) (address width : Nat) : Option Nat :=
  some (read_mem_bytes width (BitVec.ofNat 64 address) s).toNat

/-- No register outside the width scratch set is changed. In particular this
retains x0--x3, x19--x30, SP and every SIMD register. -/
structure WidthFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5, 11#5, 12#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ a : BitVec 64,
    a.toNat < (r (.GPR 31) s).toNat - 16 ∨ (r (.GPR 31) s).toNat ≤ a.toNat →
    t.mem a = s.mem a

theorem WidthFrame.refl (s : ArmState) : WidthFrame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem WidthFrame.sp {s t : ArmState} (h : WidthFrame s t) :
    r (.GPR 31) t = r (.GPR 31) s := h.registers _ (by decide)

theorem WidthFrame.trans {s t u : ArmState} (h : WidthFrame s t)
    (k : WidthFrame t u) : WidthFrame s u := by
  refine ⟨k.program.trans h.program, k.error.trans h.error,
    fun reg hr => (k.registers reg hr).trans (h.registers reg hr),
    fun reg => (k.vectors reg).trans (h.vectors reg), ?_⟩
  intro a ha
  exact (k.memory a (by simpa only [h.sp] using ha)).trans (h.memory a ha)

theorem WidthFrame.aligned {s t : ArmState} (h : WidthFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  have hp : r (.GPR 31#5) t = r (.GPR 31#5) s := h.sp
  simpa only [CheckSPAlignment, state_simp_rules, hp] using ha

/-- The source is nonwrapping and outside the *whole* 16-byte lowering slot. -/
def WidthSource (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64)) : Prop :=
  16 ≤ (r (.GPR 31) s).toNat ∧
  pointer.toNat + 8 * words.length ≤ 2 ^ 64 ∧
  (pointer.toNat + 8 * words.length ≤ (r (.GPR 31) s).toNat - 16 ∨
    (r (.GPR 31) s).toNat ≤ pointer.toNat)

def WidthWords (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64)) : Prop :=
  ∀ i : Fin words.length,
    read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * i.val)) s = words[i]

theorem WidthFrame.source {s t : ArmState} (h : WidthFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64)) (hs : WidthSource s pointer words) :
    WidthSource t pointer words := by simpa only [WidthSource, h.sp] using hs

/-- Every limb observation survives every scratch save, not just the final read. -/
theorem WidthFrame.words {s t : ArmState} (h : WidthFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : WidthSource s pointer words) (hm : WidthWords s pointer words) :
    WidthWords t pointer words := by
  intro i
  rw [← hm i]
  apply BoolCodec.read_bytes_congr
  intro j hj
  change t.mem _ = s.mem _
  apply h.memory
  rcases hs with ⟨hsp, hbound, hsep⟩
  have hi := i.isLt
  have haddr : (pointer + BitVec.ofNat 64 (8 * i.val) + BitVec.ofNat 64 j).toNat =
      pointer.toNat + 8 * i.val + j := by bv_omega
  rw [haddr]
  omega

def widthSaved (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31) s - 16#64) (r (.GPR 9) s) s

theorem widthSaved_frame (s : ArmState) (hs : 16 ≤ (r (.GPR 31) s).toNat) :
    WidthFrame s (widthSaved s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [widthSaved, state_simp_rules]
  · simp [widthSaved, state_simp_rules]
  · intro reg hr; simp [widthSaved, state_simp_rules]
  · intro reg; simp [widthSaved, state_simp_rules]
  · intro a ha
    exact BoolCodec.write_mem_bytes_frame s _ 8 _ a (by bv_omega) (by bv_omega)

end SszArm.UintCodec
