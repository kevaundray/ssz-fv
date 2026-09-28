import SszArm.EmitContract
import SszArm.BitVectorMemcpy

namespace SszArm.Emit

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

inductive CopySite where
  | bitList | bytes | bitVector
  deriving DecidableEq

def CopySite.offset : CopySite → Nat
  | .bitList => 648 | .bytes => 856 | .bitVector => 1252

def CopySite.word : CopySite → BitVec 32
  | .bitList => 0x94007393#32 | .bytes => 0x9400735f#32 | .bitVector => 0x940072fc#32

def called (site : CopySite) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 memcpyOffset)
    (w (.GPR 30#5) (base + BitVec.ofNat 64 (site.offset + 4)) s)

theorem call_step (site : CopySite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 site.offset) :
    stepi s = called site s base := by
  change r .PC s = base + BitVec.ofNat 64 site.offset at pc
  have fetched := body_codeAt code (site.offset, site.word) (by cases site <;> decide)
  cases site <;> simp only [CopySite.offset, CopySite.word] at pc fetched
  all_goals
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [called, CopySite.offset, memcpyOffset, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, pc, BitVec.add_assoc]

@[simp] theorem called_program (site : CopySite) (s : ArmState) (base : BitVec 64) :
    (called site s base).program = s.program := by simp [called, state_simp_rules]

@[simp] theorem called_error (site : CopySite) (s : ArmState) (base : BitVec 64) :
    read_err (called site s base) = read_err s := by simp [called, state_simp_rules]

@[simp] theorem called_register (site : CopySite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (notLink : reg ≠ 30#5) :
    r (.GPR reg) (called site s base) = r (.GPR reg) s := by
  simp [called, state_simp_rules, notLink]

theorem copy_run (site : CopySite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 site.offset) :
    run (Memcpy.fuel (r (.GPR 2#5) s).toNat + 1) s = Memcpy.result (called site s base) := by
  rw [run, call_step site s base code error pc]
  have runtime : SszArm.CodeAt (called site s base)
      (base + BitVec.ofNat 64 memcpyOffset) Memcpy.program := by
    simpa only [SszArm.CodeAt, called_program] using memcpy_codeAt code
  have start : read_pc (called site s base) = base + BitVec.ofNat 64 memcpyOffset := by
    simp [called, state_simp_rules]
  have count : r (.GPR 2#5) (called site s base) = r (.GPR 2#5) s :=
    called_register _ _ _ _ (by decide)
  rw [← count]
  exact Memcpy.program_run _ _ runtime start ((called_error _ _ _).trans error)

/-- Derived after the actual BL and accepted runtime RET; ownership is checked
at the call site, never supplied as a future helper-exit assumption. -/
structure CopyPost (site : CopySite) (s t : ArmState) (base : BitVec 64) : Prop where
  pc : read_pc t = base + BitVec.ofNat 64 (site.offset + 4)
  program : t.program = s.program
  error : read_err t = .None
  registers : ∀ reg : BitVec 5, reg ∉ [1#5, 2#5, 3#5, 4#5, 30#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, reg ≠ 0#5 → r (.SFP reg) t = r (.SFP reg) s
  copied : ∀ offset bytes, offset + bytes ≤ (r (.GPR 2#5) s).toNat →
    widthLoad t ((r (.GPR 0#5) s).toNat + offset) bytes =
      widthLoad s ((r (.GPR 1#5) s).toNat + offset) bytes
  frame : MemoryFrame [((r (.GPR 0#5) s).toNat, (r (.GPR 2#5) s).toNat)] s t

theorem copy_correct (site : CopySite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 site.offset)
    (destination : (r (.GPR 0#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (source : (r (.GPR 1#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (separate : Memcpy.Disjoint (r (.GPR 0#5) s) (r (.GPR 1#5) s) (r (.GPR 2#5) s).toNat) :
    CopyPost site s (run (Memcpy.fuel (r (.GPR 2#5) s).toNat + 1) s) base := by
  rw [copy_run site s base code error pc]
  let c := called site s base
  have r0 : r (.GPR 0#5) c = r (.GPR 0#5) s := called_register _ _ _ _ (by decide)
  have r1 : r (.GPR 1#5) c = r (.GPR 1#5) s := called_register _ _ _ _ (by decide)
  have r2 : r (.GPR 2#5) c = r (.GPR 2#5) s := called_register _ _ _ _ (by decide)
  have dst : (r (.GPR 0#5) c).toNat + (r (.GPR 2#5) c).toNat ≤ 2^64 := by rwa [r0, r2]
  have src : (r (.GPR 1#5) c).toNat + (r (.GPR 2#5) c).toNat ≤ 2^64 := by rwa [r1, r2]
  have sep : Memcpy.Disjoint (r (.GPR 0#5) c) (r (.GPR 1#5) c) (r (.GPR 2#5) c).toNat := by
    rwa [r0, r1, r2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have returned := Memcpy.result_return c
    simpa [c, called, state_simp_rules] using returned
  · exact (Memcpy.result_program c).trans (called_program _ _ _)
  · exact (Memcpy.result_frame c .ERR trivial).trans ((called_error _ _ _).trans error)
  · intro reg untouched
    have h1 : reg ≠ 1#5 := by simp_all
    have h2 : reg ≠ 2#5 := by simp_all
    have h3 : reg ≠ 3#5 := by simp_all
    have h4 : reg ≠ 4#5 := by simp_all
    have h30 : reg ≠ 30#5 := by simp_all
    exact (Memcpy.result_frame c (.GPR reg) ⟨h1, h2, h3, h4⟩).trans
      (called_register _ _ _ _ h30)
  · intro reg nonzero
    have preserved := Memcpy.result_frame c (.SFP reg) nonzero
    simpa [c, called, state_simp_rules] using preserved
  · intro offset bytes within
    have observed := BitVector.memcpy_observe c offset bytes dst src sep (by rwa [r2])
    simpa [r0, r1, c, widthLoad, called, state_simp_rules] using observed
  · have frame := BitVector.memcpy_frame c dst src sep
    simpa [r0, r2, Delimited.MemoryFrame, c, called, state_simp_rules] using frame

end SszArm.Emit
