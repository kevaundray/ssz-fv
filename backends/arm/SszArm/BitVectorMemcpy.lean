import SszArm.BitVectorCalls
import SszArm.BitVectorMemory

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- Subword observations of the actual runtime image, with no alignment
assumption on either the source or target. -/
theorem memcpy_observe (s : ArmState) (offset bytes : Nat)
    (destination : (r (.GPR 0#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (source : (r (.GPR 1#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (separate : Memcpy.Disjoint (r (.GPR 0#5) s) (r (.GPR 1#5) s) (r (.GPR 2#5) s).toNat)
    (within : offset + bytes ≤ (r (.GPR 2#5) s).toNat) :
    widthLoad (Memcpy.result s) ((r (.GPR 0#5) s).toNat + offset) bytes =
      widthLoad s ((r (.GPR 1#5) s).toNat + offset) bytes := by
  unfold widthLoad
  congr 1
  congr 1
  rw [Memory.State.read_mem_bytes_eq_mem_read_bytes,
    Memory.State.read_mem_bytes_eq_mem_read_bytes]
  apply BitVec.eq_of_extractLsByte_eq
  intro index
  have targetBound : (BitVec.ofNat 64 ((r (.GPR 0#5) s).toNat + offset)).toNat + bytes ≤ 2^64 := by
    bv_omega
  have sourceBound : (BitVec.ofNat 64 ((r (.GPR 1#5) s).toNat + offset)).toNat + bytes ≤ 2^64 := by
    bv_omega
  rw [Memory.extractLsByte_read_bytes targetBound, Memory.extractLsByte_read_bytes sourceBound]
  by_cases inside : index < bytes
  · rw [if_pos inside, if_pos inside]
    have targetAddress : BitVec.ofNat 64 ((r (.GPR 0#5) s).toNat + offset) +
        BitVec.ofNat 64 index = r (.GPR 0#5) s + BitVec.ofNat 64 (offset + index) := by bv_omega
    have sourceAddress : BitVec.ofNat 64 ((r (.GPR 1#5) s).toNat + offset) +
        BitVec.ofNat 64 index = r (.GPR 1#5) s + BitVec.ofNat 64 (offset + index) := by bv_omega
    rw [targetAddress, sourceAddress]
    exact Memcpy.result_byte s destination source separate _ (by
      change offset + index < (r (.GPR 2#5) s).toNat
      omega)
  · rw [if_neg inside, if_neg inside]

theorem memcpy_frame (s : ArmState)
    (destination : (r (.GPR 0#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (source : (r (.GPR 1#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (separate : Memcpy.Disjoint (r (.GPR 0#5) s) (r (.GPR 1#5) s) (r (.GPR 2#5) s).toNat) :
    MemoryFrame [((r (.GPR 0#5) s).toNat, (r (.GPR 2#5) s).toNat)] s (Memcpy.result s) := by
  intro address outside
  have position := outside ((r (.GPR 0#5) s).toNat, (r (.GPR 2#5) s).toNat) (by simp)
  rw [Memcpy.result_memory s destination source separate, Memcpy.image]
  split
  · rename_i inside
    change (r (.GPR 0#5) s).toNat ≤ address.toNat ∧
      address.toNat < (r (.GPR 0#5) s).toNat + (r (.GPR 2#5) s).toNat at inside
    omega
  · rfl

/-- Public call summary used by all four error-copy sites: concrete execution,
actual return PC, exact copied observations, and a destination-only byte frame. -/
structure CopyPost (site : CallSite) (s t : ArmState) (base : BitVec 64) : Prop where
  returned : read_pc t = base + BitVec.ofNat 64 (site.offset + 4)
  error : read_err t = .None
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 5 ≤ reg.toNat → reg.toNat ≤ 29 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, reg ≠ 0#5 → r (.SFP reg) t = r (.SFP reg) s
  copied : ∀ offset bytes, offset + bytes ≤ (r (.GPR 2#5) s).toNat →
    widthLoad t ((r (.GPR 0#5) s).toNat + offset) bytes =
      widthLoad s ((r (.GPR 1#5) s).toNat + offset) bytes
  frame : MemoryFrame [((r (.GPR 0#5) s).toNat, (r (.GPR 2#5) s).toNat)] s t

theorem memcpy_correct (site : CallSite) (s : ArmState) (base : BitVec 64)
    (runtime : site = .divisionError ∨ site = .roundTemporary ∨ site = .roundError ∨ site = .scopeError)
    (code : JointCodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 site.offset)
    (destination : (r (.GPR 0#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (source : (r (.GPR 1#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (separate : Memcpy.Disjoint (r (.GPR 0#5) s) (r (.GPR 1#5) s) (r (.GPR 2#5) s).toNat) :
    ∃ fuel t, run fuel s = t ∧ CopyPost site s t base := by
  let c := called site s base
  have r0 : r (.GPR 0#5) c = r (.GPR 0#5) s := by
    simp (config := {decide := true}) [c, called, state_simp_rules]
  have r1 : r (.GPR 1#5) c = r (.GPR 1#5) s := by
    simp (config := {decide := true}) [c, called, state_simp_rules]
  have r2 : r (.GPR 2#5) c = r (.GPR 2#5) s := by
    simp (config := {decide := true}) [c, called, state_simp_rules]
  have dst : (r (.GPR 0#5) c).toNat + (r (.GPR 2#5) c).toNat ≤ 2^64 := by rwa [r0, r2]
  have src : (r (.GPR 1#5) c).toNat + (r (.GPR 2#5) c).toNat ≤ 2^64 := by rwa [r1, r2]
  have sep : Memcpy.Disjoint (r (.GPR 0#5) c) (r (.GPR 1#5) c) (r (.GPR 2#5) c).toNat := by
    rwa [r0, r1, r2]
  refine ⟨Memcpy.fuel (r (.GPR 2#5) s).toNat + 1, Memcpy.result c,
    memcpy_call site s base runtime code error pc, ?_⟩
  constructor
  · have returned := Memcpy.result_return c
    change read_pc (Memcpy.result c) = r (.GPR 30#5) c at returned
    simpa (config := {decide := true}) [c, called, state_simp_rules] using returned
  · have preserved := Memcpy.result_frame c .ERR trivial
    exact preserved.trans (by
      change read_err c = .None
      simpa only [c, called_error] using error)
  · have preserved := Memcpy.result_frame c (.GPR 31#5) (by simp [Memcpy.Preserved])
    simpa (config := {decide := true}) [c, called, state_simp_rules] using preserved
  · intro reg low high
    have untouched : Memcpy.Preserved (.GPR reg) := by simp only [Memcpy.Preserved]; bv_omega
    have preserved := Memcpy.result_frame c (.GPR reg) untouched
    have notLink : reg ≠ 30#5 := by bv_omega
    simpa (config := {decide := true}) [c, called, state_simp_rules, notLink] using preserved
  · intro reg nonzero
    have preserved := Memcpy.result_frame c (.SFP reg) nonzero
    simpa (config := {decide := true}) [c, called, state_simp_rules] using preserved
  · intro offset bytes within
    have observed := memcpy_observe c offset bytes dst src sep (by rwa [r2])
    simpa (config := {decide := true}) [r0, r1, c, widthLoad, called, state_simp_rules] using observed
  · have frame := memcpy_frame c dst src sep
    simpa (config := {decide := true}) [r0, r2, Delimited.MemoryFrame, c, called, state_simp_rules] using frame

end SszArm.BitVector
