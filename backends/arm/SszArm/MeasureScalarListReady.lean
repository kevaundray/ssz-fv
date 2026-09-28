import SszArm.MeasureScalarListSmall

namespace SszArm.Measure.Scalar.Bytes

open SszNative SszNative.Limbs

theorem list_ready (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bytes : Ssz.Bytes)
    (owned : Owned s args (.byteList cap) (.bytes bytes))
    (stack : r (.GPR 31#5) s = args.bodySP)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (if cap.pointer = 0#64 then 1960 else 816))
    (ptr : r (.GPR 8#5) s = cap.pointer) (count : r (.GPR 9#5) s = cap.payload)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 bytes.size)
    (marker : r (.GPR 10#5) s = if bytes.size = 0 then 0#64 else 1#64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .list t base cap bytes.size := by
  have physical : bytes.size < 2^64 := owned.physical
  have low := owned.stackLow
  have safe : 16 ≤ (r (.GPR 31#5) s).toNat := by rw [stack, Args.bodySP]; bv_omega
  cases cap with
  | small word =>
    exact list_small s base word bytes.size code error aligned
      (by simpa [NatOperand.pointer] using pc) physical safe ptr count actual
  | large pointer words =>
    have input := cap_at (kind := .list) owned
    have position : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
      rw [stack, Args.bodySP]; bv_omega
    have nonzero : pointer ≠ 0#64 := by have positive := input.1; bv_omega
    have borrowed := owned.operandOwned (.large pointer words)
      (by simp [Emit.descriptorOperands, Emit.valueOperands])
    have source := NatNarrow.large_source s pointer words
      (writesFor args (outcome s args (.byteList (.large pointer words)) (.bytes bytes)))
      input borrowed (by simp [position, writesFor, localWrites, stackWrites, bodyStackWrites]) safe
    have stored := NatNarrow.large_words s pointer words input
    have physicalCount : words.length < 2^64 := by have := source.2.1; omega
    have significantBound := sigWords_le_length words
    obtain ⟨fuel, u, hu, uf, kept, up, remembered⟩ := large_scan .list s base pointer words
      code error aligned (by simpa [NatOperand.pointer, nonzero, Kind.largePC] using pc)
      ptr count source stored
    let v := listCountReady u base (sigWords words)
    let countSteps := if sigWords words = 0 then 1 else 2
    have hv : run countSteps u = v := list_count_run u base (sigWords words)
      (code.congr uf.program) (uf.error.trans error)
      (by simpa [Kind.scanZero, Kind.scanExit] using up) (by omega) remembered
    have vf : NatNarrow.Frame s v := uf.trans (list_count_frame u base (sigWords words))
    have keep (reg : BitVec 5) (member : reg ∈ [8#5, 9#5, 10#5]) :
        r (.GPR reg) v = r (.GPR reg) s := by
      have first := kept reg member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;>
        simpa (config := {decide := true}) [v, listCountReady, state_simp_rules] using first
    obtain ⟨fuel', t, ht, tf, ready⟩ := list_large_width v base pointer words bytes.size
      (code.congr vf.program) (vf.error.trans error)
      (by simp [v, listCountReady, state_simp_rules]) physical
      ((keep _ (by decide)).trans ptr) ((keep _ (by decide)).trans count)
      ((vf.registers _ (by decide)).trans actual)
      (by simp [v, listCountReady, state_simp_rules]) ((keep _ (by decide)).trans marker)
      (vf.source _ _ source) (vf.words _ _ source stored)
    exact ⟨fuel + countSteps + fuel', t, by rw [run_plus, run_plus, hu, hv, ht],
      (Frame.of_narrow vf).trans tf, ready⟩

theorem list_bytes_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bytes : Ssz.Bytes)
    (owned : Owned s args (.byteList cap) (.bytes bytes)) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 776#64) (descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : (r (.GPR 8#5) s).setWidth 32 = 2#32) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.byteList cap) (.bytes bytes) base := by
  obtain ⟨pointerRead, payloadRead⟩ := cap_reads (kind := .list) owned
  have lengthRead := length_read (kind := .list) owned
  obtain ⟨hu, setup⟩ := setup_run .list s base code error pc tag cap (BitVec.ofNat 64 bytes.size)
    (by simpa only [descriptor] using pointerRead) (by simpa only [descriptor] using payloadRead)
    (by simpa only [registers.value] using lengthRead)
  let u := setupResult .list s (BitVec.ofNat 64 bytes.size)
  let steps := (Kind.list.setupOps (BitVec.ofNat 64 bytes.size)).length
  change run steps s = u at hu
  have uf : Frame s u := setup.frame
  have ownu := uf.owned (kind := .list) owned registers.stack
  have usp := uf.stack.trans registers.stack
  have physical : bytes.size < 2^64 := owned.physical
  have sizeZero : BitVec.ofNat 64 bytes.size = 0#64 ↔ bytes.size = 0 := by bv_omega
  have marker : r (.GPR 10#5) u = if bytes.size = 0 then 0#64 else 1#64 := by
    simpa only [sizeZero] using setup.marker rfl
  obtain ⟨fuel, v, hv, vf, ready⟩ := list_ready u base args cap bytes ownu usp
    (code.congr uf.program) (uf.error.trans error) (uf.aligned aligned)
    setup.pc setup.pointer setup.payload setup.actual marker
  have frame := uf.trans vf
  obtain ⟨fuel', t, ht, post⟩ := ready_body .list v base args cap bytes
    (frame.owned owned registers.stack) (frame.output.trans registers.result)
    (frame.stack.trans registers.stack) (code.congr frame.program)
    (frame.error.trans error) (frame.aligned aligned) ready
  exact ⟨steps + fuel + fuel', t, by rw [run_plus, run_plus, hu, hv, ht],
    frame.prepend owned registers.stack post⟩

end SszArm.Measure.Scalar.Bytes
