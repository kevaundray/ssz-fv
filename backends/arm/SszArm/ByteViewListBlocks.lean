import SszArm.ByteViewListScan
import SszArm.ByteViewTails

namespace SszArm.ByteView.Bounded

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

@[simp] theorem cmp_zero_zero (a : BitVec 64) :
    (AddWithCarry a 18446744073709551615#64 1#1).2.z = 1#1 ↔ a = 0#64 :=
  Udivti3.cmp_zero a 0#64

@[simp] theorem cmp_carry_zero (a : BitVec 64) :
    (AddWithCarry a 18446744073709551615#64 1#1).2.c = 1#1 :=
  (Udivti3.cmp_carry a 0#64).mpr (Nat.zero_le _)

@[simp] theorem cmp_carry_one (a : BitVec 64) :
    (AddWithCarry a 18446744073709551614#64 1#1).2.c = 1#1 ↔ 1 ≤ a.toNat :=
  Udivti3.cmp_carry a 1#64

def flagOps (reject : Bool) : List Op :=
  [.p3536, .p3540, .p3544, .p3548] ++
    if reject then [.p3552, .p3556, .p3560] else [.p3564, .p3568, .p3572]

def smallFlagOps (different : Bool) : List Op :=
  [.p2644, .p2648, .p2652, .p2656] ++
    if different then [.p2672, .p2676, .p2680] else [.p2660, .p2664, .p2668]

def spillOps (small b : Bool) : List Op := if small then smallFlagOps b else flagOps b

def spillTarget (small b : Bool) : Nat :=
  if small then (if b then 3536 else 2684) else (if b then 3576 else 4492)

def spillResult (s : ArmState) (base : BitVec 64) (small b : Bool) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (spillTarget small b)) (widthSaved s)

/-- Both flag tests use precisely the same save/restore discipline. The result
certificate hides every intermediate state and exposes just the single spill. -/
theorem spill_run (s : ArmState) (base : BitVec 64) (small b : Bool)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + (if small then 2644#64 else 3536#64))
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hb : if small then
      r (.GPR 11#5) s = (if b then 1#64 else 0#64)
      else r (.GPR 10#5) s = (if b then 1#64 else 0#64)) :
    run 7 s = spillResult s base small b := by
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (widthSaved s) =
      r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  simp only [widthSaved, BitVec.ofNat_eq_ofNat] at hrestore
  have hpc : r .PC s = base + (if small then 2644#64 else 3536#64) := hp
  have hlen : (spillOps small b).length = 7 := by cases small <;> cases b <;> decide
  have hfollow : Follows base (spillOps small b) s := by
    cases small <;> cases b <;>
      simp only [Bool.false_eq_true, ↓reduceIte] at hb hpc <;>
      simp (config := {decide := true, instances := true})
        [spillOps, smallFlagOps, flagOps, Follows, Op.row, Op.effect,
         put, next, state_simp_rules, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
         BitVec.sub_add_cancel, width_read_spill_w, hpc, hb, hrestore]
  rw [← hlen, block_run base (spillOps small b) s hc he ha hfollow]
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases h9 : reg = 9#5
      · subst reg
        cases small <;> cases b <;>
          simp only [Bool.false_eq_true, ↓reduceIte] at hb hpc <;>
          simp (config := {decide := true, instances := true})
            [spillResult, spillTarget, spillOps, smallFlagOps, flagOps, block, Op.effect,
             put, next, widthSaved, state_simp_rules, BitVec.ofNat_eq_ofNat,
             BitVec.add_assoc, BitVec.sub_add_cancel, width_read_spill_w, hpc, hb, hrestore]
      · by_cases h31 : reg = 31#5
        · subst reg
          cases small <;> cases b <;>
            simp only [Bool.false_eq_true, ↓reduceIte] at hb hpc <;>
            simp (config := {decide := true, instances := true})
              [spillResult, spillTarget, spillOps, smallFlagOps, flagOps, block, Op.effect,
               put, next, widthSaved, state_simp_rules, BitVec.ofNat_eq_ofNat,
               BitVec.add_assoc, BitVec.sub_add_cancel, width_read_spill_w, hpc, hb, hrestore]
        · cases small <;> cases b <;>
            simp only [Bool.false_eq_true, ↓reduceIte] at hb hpc <;>
            simp (config := {decide := true, instances := true})
              [spillResult, spillTarget, spillOps, smallFlagOps, flagOps, block, Op.effect,
               put, next, widthSaved, state_simp_rules, BitVec.ofNat_eq_ofNat,
               BitVec.add_assoc, BitVec.sub_add_cancel, width_read_spill_w, hpc, hb,
               hrestore, h9, h31]
    | SFP reg =>
      cases small <;> cases b <;>
        simp [spillResult, spillOps, smallFlagOps, flagOps, block, Op.effect,
          put, next, widthSaved, state_simp_rules]
    | PC =>
      cases small <;> cases b <;>
        simp only [Bool.false_eq_true, ↓reduceIte] at hb hpc <;>
        simp (config := {decide := true, instances := true})
          [spillResult, spillTarget, spillOps, smallFlagOps, flagOps, block, Op.effect,
           put, next, widthSaved, state_simp_rules, BitVec.ofNat_eq_ofNat,
           BitVec.add_assoc, BitVec.sub_add_cancel, width_read_spill_w, hpc, hb, hrestore]
    | FLAG flag =>
      cases small <;> cases b <;>
        simp [spillResult, spillOps, smallFlagOps, flagOps, block, Op.effect,
          put, next, widthSaved, state_simp_rules]
    | ERR =>
      cases small <;> cases b <;>
        simp [spillResult, spillOps, smallFlagOps, flagOps, block, Op.effect,
          put, next, widthSaved, state_simp_rules]
  · cases small <;> cases b <;>
      simp [spillResult, spillOps, smallFlagOps, flagOps, block, Op.effect,
        put, next, widthSaved, state_simp_rules]
  · intro n address
    cases small <;> cases b <;>
      simp [spillResult, spillOps, smallFlagOps, flagOps, block, Op.effect,
        put, next, widthSaved, state_simp_rules, width_read_spill_w]

theorem spill_frame (s : ArmState) (base : BitVec 64) (small b : Bool)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) : WidthFrame s (spillResult s base small b) := by
  have h := widthSaved_frame s hs
  constructor
  · simpa [spillResult, state_simp_rules] using h.program
  · simpa [spillResult, state_simp_rules] using h.error
  · intro reg hr
    simpa [spillResult, state_simp_rules] using h.registers reg hr
  · intro reg
    simpa [spillResult, state_simp_rules] using h.vectors reg
  · intro a ha
    simpa [spillResult, state_simp_rules] using h.memory a ha

@[simp] theorem spill_register (s : ArmState) (base : BitVec 64) (small b : Bool) (reg : BitVec 5) :
    r (.GPR reg) (spillResult s base small b) = r (.GPR reg) s := by
  simp [spillResult, widthSaved, state_simp_rules]

@[simp] theorem spill_pc (s : ArmState) (base : BitVec 64) (small b : Bool) :
    read_pc (spillResult s base small b) = base + BitVec.ofNat 64 (spillTarget small b) := by
  simp [spillResult, state_simp_rules]

end SszArm.ByteView.Bounded
