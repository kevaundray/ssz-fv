import SszArm.NatDivisionReturn

namespace SszArm.NatDivision

open Delimited (MemoryFrame)

set_option maxRecDepth 32768

theorem normalization_store_observations (s : ArmState) (base pointer : BitVec 64)
    (physical : (r (.GPR 19#5) s).toNat + 8 ≤ 2^64) :
    let t := w .PC (base + 800#64) (write_mem_bytes 8 (r (.GPR 19#5) s) pointer s)
    MemoryFrame (returnWrites s) s t ∧
    (∀ reg : BitVec 5, r (.GPR reg) t = r (.GPR reg) s) ∧
    (∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s) ∧
    t.program = s.program ∧ read_err t = read_err s ∧
    (CheckSPAlignment s → CheckSPAlignment t) ∧
    read_pc t = base + 800#64 ∧
    read_mem_bytes 8 (r (.GPR 19#5) t) t = pointer := by
  dsimp only
  have keep (field : StateField) (different : field ≠ .PC) :
      r field (w .PC (base + 800#64) (write_mem_bytes 8 (r (.GPR 19#5) s) pointer s)) =
      r field s := by
    rw [r_of_w_different different, r_of_write_mem_bytes]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a outside
    have apart := outside ((r (.GPR 19#5) s).toNat, 68) (by simp [returnWrites])
    simp only [state_simp_rules, ArmState.mem_w_eq_mem]
    apply BoolCodec.write_mem_bytes_frame s (r (.GPR 19#5) s) 8 pointer a physical
    simp only [Prod.fst, Prod.snd] at apart
    omega
  · intro reg
    exact keep (.GPR reg) (by intro equal; cases equal)
  · intro reg
    exact keep (.SFP reg) (by intro equal; cases equal)
  · rw [w_program, write_mem_bytes_program]
  · change r .ERR (w .PC (base + 800#64)
      (write_mem_bytes 8 (r (.GPR 19#5) s) pointer s)) = r .ERR s
    exact keep .ERR (by decide)
  · intro aligned
    simpa only [CheckSPAlignment, state_simp_rules, keep (.GPR 31#5) (by decide)] using aligned
  · change r .PC (w .PC (base + 800#64)
      (write_mem_bytes 8 (r (.GPR 19#5) s) pointer s)) = base + 800#64
    exact r_of_w_same
  · rw [keep (.GPR 19#5) (by decide), read_mem_bytes_of_w]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8
      (r (.GPR 19#5) s) pointer physical

end SszArm.NatDivision
