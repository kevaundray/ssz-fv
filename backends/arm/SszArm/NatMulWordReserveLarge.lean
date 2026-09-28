import SszArm.NatMulWordReserveSize
import SszArm.DelimitedMemory

namespace SszArm.NatMulWord.Reserve

/-- Before commitment the only possible write is the actual saved X9 slot. -/
structure Prefix (s t : ArmState) : Prop where
  runs : ∃ fuel, run fuel s = t
  frame : Frame s t
  memory : t.mem = s.mem ∨ t.mem = (signMemory s).mem

theorem Checkpoint.prefix {s t : ArmState} (reached : Checkpoint s t) : Prefix s t :=
  ⟨reached.runs, reached.frame, Or.inl reached.memory⟩

theorem Prefix.thenHeader {s t u : ArmState} (st : Prefix s t)
    (tu : Checkpoint t u) : Prefix s u := by
  obtain ⟨n, hn⟩ := st.runs
  obtain ⟨m, hm⟩ := tu.runs
  refine ⟨⟨n + m, by rw [run_plus, hn, hm]⟩, st.frame.trans tu.frame, ?_⟩
  rcases st.memory with h | h
  · exact Or.inl (tu.memory.trans h)
  · exact Or.inr (tu.memory.trans h)

theorem Prefix.memoryFrame {s t : ArmState} (reached : Prefix s t)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 8)] s t := by
  intro a outside
  rcases reached.memory with h | h
  · exact congrFun h a
  · rw [h]
    exact sign_memory_frame s stack a outside

theorem Prefix.header {s t : ArmState} (reached : Prefix s t)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64)
    (separate : (r (.GPR 4#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (r (.GPR 4#5) s).toNat)
    (offset : BitVec 64) (bound : offset.toNat ≤ 16) :
    read_mem_bytes 8 (r (.GPR 4#5) t + offset) t =
      read_mem_bytes 8 (r (.GPR 4#5) s + offset) s := by
  rw [reached.frame.registers 4#5 (by decide)]
  rcases reached.memory with h | h
  · exact Memory.mem_eq_iff_read_mem_bytes_eq.mp h _ _
  · rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp h]
    apply BoolCodec.read_mem_bytes_write_mem_bytes_disjoint
    all_goals bv_omega

theorem Checkpoint.sign {s t : ArmState} (reached : Checkpoint s t)
    (negative : Bool) (base : BitVec 64) (hc : CodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc t = base + 348#64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (selected : ((r (.GPR 11#5) t &&& 9223372036854775808#64) = 0#64) ↔ negative = false) :
    Prefix s (block base (signOps negative) t) := by
  obtain ⟨fuel, hr⟩ := reached.runs
  have hrun := sign_run negative t base (reached.frame.code base hc)
    (reached.frame.error.trans he) (reached.frame.aligned ha) hp selected
  have effect := sign_effect negative t base (by rw [reached.frame.sp]; exact stack)
  refine ⟨⟨fuel + 7, by rw [run_plus, hr, hrun]⟩, reached.frame.trans effect.1, Or.inr ?_⟩
  apply effect.2.1.trans
  unfold signMemory
  rw [reached.frame.sp, reached.frame.registers 9#5 (by decide)]
  exact mem_write_mem_bytes_of_mem_eq reached.memory _ _ _

def LargePost (s t : ArmState) (base address capacity used : BitVec 64) : Prop :=
  Prefix s t ∧
    (((r (.GPR 9#5) s).toNat + 1 = 2^64 ∧ read_pc t = base + 1632#64) ∨
      ((r (.GPR 9#5) s).toNat + 1 < 2^64 ∧
        ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
            ((r (.GPR 9#5) s).toNat + 1) = none ∧ read_pc t = base + 1264#64) ∨
          (SszNative.Arena.Checks address.toNat capacity.toNat used.toNat
              ((r (.GPR 9#5) s).toNat + 1) ∧
            read_pc t = base + 452#64 ∧ r (.GPR 10#5) t = address ∧
            (r (.GPR 16#5) t).toNat = SszNative.Arena.start address.toNat used.toNat ∧
            (r (.GPR 17#5) t).toNat = SszNative.Arena.finish address.toNat used.toNat
              ((r (.GPR 9#5) s).toNat + 1) ∧
            r (.GPR 12#5) t = r (.GPR 12#5) s ∧
            (r (.GPR 15#5) t).toNat = address.toNat + SszNative.Arena.start address.toNat used.toNat))))

/-- All actual guards from PC320, including the restored transient signed-size
slot and the distinct original usize-overflow error body at PC1632. -/
theorem large_checks_runs (s : ArmState) (base address capacity used : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 320#64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64)
    (separate : (r (.GPR 4#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (r (.GPR 4#5) s).toNat)
    (headerBase : read_mem_bytes 8 (r (.GPR 4#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s = used) :
    ∃ fuel t, run fuel s = t ∧ LargePost s t base address capacity used := by
  let a := block base SizeGuard.usize.ops s
  have ra : Checkpoint s a := (Checkpoint.refl s).size .usize base hc he ha hp
  have ea := usize_exit s base
  by_cases overflow : (r (.GPR 9#5) s).toNat + 1 = 2^64
  · obtain ⟨fuel, hr⟩ := ra.runs
    exact ⟨fuel, a, hr, ra.prefix, Or.inl ⟨overflow, ea.trans (if_pos overflow)⟩⟩
  · have countBound : (r (.GPR 9#5) s).toNat + 1 < 2^64 := by
      have := (r (.GPR 9#5) s).isLt
      omega
    have apc : read_pc a = base + 328#64 := ea.trans (if_neg overflow)
    let b := block base SizeGuard.multiply.ops a
    have rb : Checkpoint s b := ra.size .multiply base hc he ha apc
    have eb := multiply_exit a base
    have a9 := ra.frame.registers 9#5 (by decide)
    rw [a9] at eb
    by_cases byteOverflow : 2305843009213693950 < (r (.GPR 9#5) s).toNat
    · have failed : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
          ((r (.GPR 9#5) s).toNat + 1) = none := by
        apply (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ (by omega)).2
        intro checks
        have size := checks.1
        omega
      obtain ⟨fuel, hr⟩ := rb.runs
      exact ⟨fuel, b, hr, rb.prefix, Or.inr ⟨countBound,
        Or.inl ⟨failed, eb.trans (if_pos byteOverflow)⟩⟩⟩
    · have bpc : read_pc b = base + 340#64 := eb.trans (if_neg byteOverflow)
      let c := block base SizeGuard.bytes.ops b
      have rc : Checkpoint s c := rb.size .bytes base hc he ha bpc
      have b9 := rb.frame.registers 9#5 (by decide)
      have ec := bytes_exit b base bpc (by rw [b9]; omega)
      rw [b9] at ec
      by_cases signedOK : 8 * ((r (.GPR 9#5) s).toNat + 1) < 2^63
      · have clear : r (.GPR 11#5) c &&& 9223372036854775808#64 = 0#64 :=
          (SszNative.Arena.high_bit_clear _).2 (by rw [ec.2]; exact signedOK)
        let d := block base (signOps false) c
        have rd : Prefix s d := rc.sign false base hc he ha ec.1 stack (by simp [clear])
        have ed := sign_effect false c base (by rw [rc.frame.sp]; exact stack)
        have dpc : read_pc d = base + 388#64 := ed.2.2.2
        have dbytes : (Width.large.bytes d).toNat = 8 * ((r (.GPR 9#5) s).toNat + 1) := by
          change (r (.GPR 11#5) d).toNat = _
          rw [ed.2.2.1, ec.2]
        have db : read_mem_bytes 8 (r (.GPR 4#5) d) d = address := by
          simpa using (rd.header stack physical separate 0#64 (by decide)).trans (by simpa using headerBase)
        have dc := (rd.header stack physical separate 8#64 (by decide)).trans headerCapacity
        have du := (rd.header stack physical separate 16#64 (by decide)).trans headerUsed
        obtain ⟨fuel, t, hrun, rt, selected⟩ := header_checks_runs .large
          ((r (.GPR 9#5) s).toNat + 1) d base address capacity used (by omega) signedOK dbytes
          (rd.frame.code base hc) (rd.frame.error.trans he) (rd.frame.aligned ha) dpc db dc du
        have reached := rd.thenHeader rt
        obtain ⟨total, hr⟩ := reached.runs
        refine ⟨total, t, hr, reached, Or.inr ⟨countBound, ?_⟩⟩
        rcases selected with failed | ⟨checks, pc, addressReg, first, last, keep12, aligned⟩
        · exact Or.inl failed
        · refine Or.inr ⟨checks, pc, addressReg, first, last, ?_, aligned rfl⟩
          apply (keep12 rfl).trans
          calc
            r (.GPR 12#5) d = r (.GPR 12#5) c :=
              sign_registers false c base (by rw [rc.frame.sp]; exact stack) 12#5
            _ = r (.GPR 12#5) b := size_registers .bytes b base 12#5 (by decide)
            _ = r (.GPR 12#5) a := size_registers .multiply a base 12#5 (by decide)
            _ = r (.GPR 12#5) s := size_registers .usize s base 12#5 (by decide)
      · have set : r (.GPR 11#5) c &&& 9223372036854775808#64 ≠ 0#64 := by
          intro clear
          have small := (SszNative.Arena.high_bit_clear _).1 clear
          rw [ec.2] at small
          exact signedOK small
        let d := block base (signOps true) c
        have rd : Prefix s d := rc.sign true base hc he ha ec.1 stack (by simp [set])
        have ed := sign_effect true c base (by rw [rc.frame.sp]; exact stack)
        have failed : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
            ((r (.GPR 9#5) s).toNat + 1) = none := by
          apply (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ (by omega)).2
          exact fun checks => signedOK checks.1
        obtain ⟨fuel, hr⟩ := rd.runs
        exact ⟨fuel, d, hr, rd, Or.inr ⟨countBound, Or.inl ⟨failed, ed.2.2.2⟩⟩⟩

end SszArm.NatMulWord.Reserve
