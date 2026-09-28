import SszArm.MeasureScalarByteReady

namespace SszArm.Measure.Scalar.Bytes

open SszNative (NatOperand)

theorem vector_ready (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bytes : Ssz.Bytes)
    (owned : Owned s args (.byteVector cap) (.bytes bytes))
    (stack : r (.GPR 31#5) s = args.bodySP)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (if cap.pointer = 0#64 then 2316 else 1176))
    (ptr : r (.GPR 8#5) s = cap.pointer) (count : r (.GPR 9#5) s = cap.payload)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 bytes.size) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .vector t base cap bytes.size := by
  have physical : bytes.size < 2^64 := owned.physical
  cases cap with
  | small word =>
    exact vector_small s base word bytes.size code error
      (by simpa [NatOperand.pointer] using pc) physical ptr count actual
  | large pointer words =>
    have input := cap_at (kind := .vector) owned
    have low := owned.stackLow
    have position : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
      rw [stack, Args.bodySP]; bv_omega
    have safe : 16 ≤ (r (.GPR 31#5) s).toNat := by rw [stack, Args.bodySP]; bv_omega
    have nonzero : pointer ≠ 0#64 := by have positive := input.1; bv_omega
    have borrowed := owned.operandOwned (.large pointer words)
      (by simp [Emit.descriptorOperands, Emit.valueOperands])
    have source := NatNarrow.large_source s pointer words
      (writesFor args (outcome s args (.byteVector (.large pointer words)) (.bytes bytes)))
      input borrowed (by simp [position, writesFor, localWrites, stackWrites, bodyStackWrites]) safe
    have stored := NatNarrow.large_words s pointer words input
    obtain ⟨fuel, u, hu, uf, kept, up, remembered⟩ := large_scan .vector s base pointer words
      code error aligned (by simpa [NatOperand.pointer, nonzero, Kind.largePC] using pc)
      ptr count source stored
    obtain ⟨fuel', t, ht, tf, ready⟩ := vector_classify u base pointer words bytes.size
      (code.congr uf.program) (uf.error.trans error)
      (by simpa [Kind.scanZero, Kind.scanExit] using up) physical
      ((kept _ (by decide)).trans ptr) ((kept _ (by decide)).trans count)
      ((uf.registers _ (by decide)).trans actual) remembered
      (uf.source _ _ source) (uf.words _ _ source stored)
    exact ⟨fuel + fuel', t, by rw [run_plus, hu, ht], (Frame.of_narrow uf).trans tf, ready⟩

theorem Setup.frame {kind : Kind} {s t : ArmState} {base : BitVec 64} {cap : NatOperand}
    {size : BitVec 64} (setup : Setup kind s t base cap size) : Frame s t := by
  refine ⟨setup.program, setup.error, setup.registers _ (by decide), setup.registers _ (by decide),
    ?_, setup.vectors, ?_⟩
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact setup.registers _ (by decide)
  · intro address outside
    rw [setup.memory]

theorem vector_bytes_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bytes : Ssz.Bytes)
    (owned : Owned s args (.byteVector cap) (.bytes bytes)) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1156#64) (descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : (r (.GPR 8#5) s).setWidth 32 = 2#32) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.byteVector cap) (.bytes bytes) base := by
  obtain ⟨pointerRead, payloadRead⟩ := cap_reads (kind := .vector) owned
  have lengthRead := length_read (kind := .vector) owned
  obtain ⟨hu, setup⟩ := setup_run .vector s base code error pc tag cap (BitVec.ofNat 64 bytes.size)
    (by simpa only [descriptor] using pointerRead) (by simpa only [descriptor] using payloadRead)
    (by simpa only [registers.value] using lengthRead)
  let u := setupResult .vector s (BitVec.ofNat 64 bytes.size)
  change run 5 s = u at hu
  have uf : Frame s u := setup.frame
  have ownu := uf.owned (kind := .vector) owned registers.stack
  have usp := uf.stack.trans registers.stack
  obtain ⟨fuel, v, hv, vf, ready⟩ := vector_ready u base args cap bytes ownu usp
    (code.congr uf.program) (uf.error.trans error) (uf.aligned aligned)
    setup.pc setup.pointer setup.payload setup.actual
  have frame := uf.trans vf
  obtain ⟨fuel', t, ht, post⟩ := ready_body .vector v base args cap bytes
    (frame.owned (kind := .vector) owned registers.stack) (frame.output.trans registers.result)
    (frame.stack.trans registers.stack) (code.congr frame.program)
    (frame.error.trans error) (frame.aligned aligned) ready
  exact ⟨5 + fuel + fuel', t, by rw [run_plus, run_plus, hu, hv, ht],
    frame.prepend owned registers.stack post⟩

end SszArm.Measure.Scalar.Bytes
