import SszArm.MeasureBitsAllocCommit

namespace SszArm.Measure.Bits.Alloc

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

def addressWord (s : ArmState) : BitVec 64 := read_mem_bytes 8 (r (.GPR 20#5) s) s
def capacityWord (s : ArmState) : BitVec 64 := read_mem_bytes 8 (r (.GPR 20#5) s + 8#64) s
def usedWord (s : ArmState) : BitVec 64 := read_mem_bytes 8 (r (.GPR 20#5) s + 16#64) s

def wide (site : Site) (s : ArmState) : BitVec 128 :=
  r (.GPR site.highReg) s ++ r (.GPR site.lowReg) s

def outcome (site : Site) (s : ArmState) : SszNative.NatArithmetic.Outcome SszNative.NatOperand :=
  SszNative.NatArithmetic.fromWide (addressWord s).toNat (capacityWord s).toNat (usedWord s).toNat
    (wide site s)

structure Input (s : ArmState) : Prop where
  header : (r (.GPR 20#5) s).toNat + 24 ≤ 2^64
  storage : (addressWord s).toNat + (capacityWord s).toNat ≤ 2^64
  nonnull : 0 < (capacityWord s).toNat → 0 < (addressWord s).toNat
  freeHeader : Protected [((r (.GPR 20#5) s).toNat, 24)]
    ((addressWord s).toNat + (usedWord s).toNat)
    ((capacityWord s).toNat - (usedWord s).toNat)

def writesFor (site : Site) (s : ArmState) : List Span :=
  match (outcome site s).allocation with
  | none => []
  | some reservation => [((r (.GPR 20#5) s).toNat + 16, 8), (reservation.pointer, 16)]

structure ConstructorPost (site : Site) (s t : ArmState) (base : BitVec 64) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5,
    reg ∉ [site.baseReg, site.usedReg, site.workReg, site.tempReg, site.pointerReg, site.countReg] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  result : match (outcome site s).result with
    | .error reason => reason = .scratchExhausted ∧ read_pc t = base + 3528#64
    | .ok operand => read_pc t = base + BitVec.ofNat 64 (site.entry + 84) ∧
        r (.GPR site.pointerReg) t = operand.pointer ∧
        r (.GPR site.countReg) t = operand.payload ∧ operand.At (widthLoad t)
  cursor : (read_mem_bytes 8 (r (.GPR 20#5) s + 16#64) t).toNat = (outcome site s).used
  header : read_mem_bytes 8 (r (.GPR 20#5) s) t = addressWord s ∧
    read_mem_bytes 8 (r (.GPR 20#5) s + 8#64) t = capacityWord s
  written : NatDivision.WrittenAt (widthLoad t) (outcome site s)
  frame : MemoryFrame (writesFor site s) s t

theorem wide_low (site : Site) (s : ArmState) :
    (wide site s).setWidth 64 = r (.GPR site.lowReg) s := by
  apply BitVec.eq_of_toNat_eq
  exact NatToU128.append_low _ _

theorem wide_high (site : Site) (s : ArmState) :
    ((wide site s) >>> (64 : Nat)).setWidth 64 = r (.GPR site.highReg) s := by
  apply BitVec.eq_of_toNat_eq
  exact NatToU128.append_high _ _

theorem wide_large (site : Site) (s : ArmState) (large : r (.GPR site.highReg) s ≠ 0#64) :
    ¬ (wide site s).toNat < 2^64 := by
  rw [wide, NatToU128.append_toNat]
  have positive : 0 < (r (.GPR site.highReg) s).toNat := by
    have nonzero : (r (.GPR site.highReg) s).toNat ≠ 0 := by
      intro zero
      apply large
      apply BitVec.eq_of_toNat_eq
      simpa using zero
    omega
  omega

theorem outcome_failure (site : Site) (s : ArmState)
    (large : r (.GPR site.highReg) s ≠ 0#64)
    (failed : SszNative.Arena.reserve (addressWord s).toNat (capacityWord s).toNat
      (usedWord s).toNat 2 = none) :
    outcome site s = SszNative.NatArithmetic.unchanged (usedWord s).toNat
      (.error .scratchExhausted) := by
  simp only [outcome, SszNative.NatArithmetic.fromWide, wide_large site s large,
    ↓reduceIte, failed]

theorem outcome_wide (site : Site) (s : ArmState)
    (large : r (.GPR site.highReg) s ≠ 0#64)
    (checks : SszNative.Arena.Checks (addressWord s).toNat (capacityWord s).toNat
      (usedWord s).toNat 2) :
    outcome site s = ⟨.ok (.large
      (BitVec.ofNat 64 ((addressWord s).toNat + SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat))
      [r (.GPR site.lowReg) s, r (.GPR site.highReg) s]),
      SszNative.Arena.finish (addressWord s).toNat (usedWord s).toNat 2,
      some ⟨(addressWord s).toNat + SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat,
        SszNative.Arena.finish (addressWord s).toNat (usedWord s).toNat 2⟩,
      [r (.GPR site.lowReg) s, r (.GPR site.highReg) s]⟩ := by
  simp [outcome, SszNative.NatArithmetic.fromWide, wide_large site s large,
    SszNative.Arena.reserve, checks, wide_low, wide_high,
    SszNative.NatArithmetic.committed, SszNative.NatOperand.fromWords,
    SszNative.Limbs.trim, large]

theorem ConstructorPost.sp {site : Site} {s t : ArmState} {base : BitVec 64}
    (post : ConstructorPost site s t base) : r (.GPR 31#5) t = r (.GPR 31#5) s :=
  post.registers _ (by cases site <;> decide)

end SszArm.Measure.Bits.Alloc
