import SszArm.DelimitedFinish
import SszArm.DelimitedCallBlocks

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem prepare_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (preserved : reg ∉ [0#5, 1#5, 2#5, 3#5, 21#5, 22#5, 27#5, 28#5, 29#5]) :
    r (.GPR reg) (block base prepareCompareOps s) = r (.GPR reg) s := by
  simp (disch := simp_all) [block, prepareCompareOps, Op.effect, put, next, state_simp_rules]

private theorem return_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (preserved : reg ∉ [0#5, 2#5, 3#5, 8#5]) :
    r (.GPR reg) (block base callReturnOps s) = r (.GPR reg) s := by
  simp (disch := simp_all) [block, callReturnOps, Op.effect, put, next, state_simp_rules]

private theorem prepare_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (block base prepareCompareOps s) = r (.SFP reg) s := by
  simp [block, prepareCompareOps, Op.effect, put, next, state_simp_rules]

private theorem return_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (block base callReturnOps s) = r (.SFP reg) s := by
  simp [block, callReturnOps, Op.effect, put, next, state_simp_rules]

private theorem compare_owned {s t : ArmState} {pointer payload : BitVec 64}
    (low : 16 ≤ (r (.GPR 31#5) s).toNat)
    (sp : r (.GPR 31#5) t = r (.GPR 31#5) s)
    (owned : NatOwned (tailWrites s) pointer payload) : NatCompare.Owned t pointer payload := by
  refine ⟨?_, ?_⟩
  · simpa only [sp] using low
  · intro hp hw
    have positive : 0 < payload.toNat := by bv_omega
    rcases owned hp hw with empty | separate
    · omega
    · have apart := separate ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [tailWrites])
      simp only [sp]
      omega

private theorem option_word {s u : ArmState} {base : BitVec 64} {cap : Nat}
    {data : Ssz.Bytes} {ready : SszNative.Delimited.Prepared}
    (owned : Owned s (some cap) data) (state : Ready s u base (some cap) data ready)
    (offset : Nat) (fits : offset + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 1#5) s + BitVec.ofNat 64 offset) u =
      read_mem_bytes 8 (r (.GPR 1#5) s + BitVec.ofNat 64 offset) s := by
  have bound := owned.optionBound
  have address : (r (.GPR 1#5) s + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 1#5) s).toNat + offset := by bv_omega
  have header : Protected (writesFor s ready.allocation) (r (.GPR 1#5) s).toNat 24 := by
    rw [← state.allocation]
    exact owned.optionOwned.1
  apply state.frame.read
  · rw [address]
    omega
  · simpa only [address] using header.subspan offset 8 fits

/-- The actual eight argument instructions, linked BL, arbitrary-Nat callee
through RET, and six result instructions. X1 is intentionally caller-clobbered:
it contains the constructed actual payload after the comparison. -/
theorem compare_ready (s u : ArmState) (base : BitVec 64) (cap : Nat)
    (data : Ssz.Bytes) (ready : SszNative.Delimited.Prepared)
    (owned : Owned s (some cap) data) (state : Ready s u base (some cap) data ready)
    (hc : CodeAt s base) (compareCode : NatCompare.CodeAt s (base + compareOffset))
    (nonempty : 0 < data.size) (hp : read_pc u = base + 364#64)
    (optionAddress : r (.GPR 1#5) u = r (.GPR 1#5) s) :
    ∃ fuel t, run fuel u = t ∧ Ready s t base (some cap) data ready ∧
      read_pc t = (if compare ready.count.value cap = .gt then base + 424#64 else base + 540#64) ∧
      r (.GPR 22#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s ∧
      r (.GPR 21#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s := by
  let a := block base prepareCompareOps u
  have codeU : CodeAt u base := by simpa only [CodeAt, state.program] using hc
  have first := prepare_compare_run u base codeU state.error state.aligned hp
  rcases prepare_compare_fields u base hp with
    ⟨pcA, memoryA, a0, a1, a2, a3, a22, a21, a27, a28, a29, spA⟩
  have codeA : CodeAt a base := by
    simpa only [a, CodeAt, block_program] using codeU
  have compareA : NatCompare.CodeAt a (base + compareOffset) := by
    simpa only [a, NatCompare.CodeAt, block_program, state.program] using compareCode
  have errorA : read_err a = .None := (block_error base prepareCompareOps u).trans state.error
  have alignedA : CheckSPAlignment a := block_aligned base prepareCompareOps u state.aligned
  have loadA : widthLoad a = widthLoad u := by
    funext address bytes
    unfold widthLoad
    rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp memoryA) bytes]
  let expectedPointer := read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s
  let expectedPayload := read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s
  have pointerWord := option_word owned state 8 (by decide)
  have payloadWord := option_word owned state 16 (by decide)
  have capPair : SszNative.NatMemory.Pair (widthLoad u) expectedPointer expectedPayload cap := by
    apply ((SszNative.NatMemory.option_some_iff_pair (widthLoad u)
      (r (.GPR 1#5) s).toNat cap expectedPointer expectedPayload ?_ ?_).mp
        (state.inputs owned).option).2
    · simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        using congrArg (fun word : BitVec 64 => some word.toNat) pointerWord
    · simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.add_assoc, BitVec.reduceAdd]
        using congrArg (fun word : BitVec 64 => some word.toNat) payloadWord
  have actualA : SszNative.NatMemory.Pair (widthLoad a)
      (r (.GPR 0#5) a) (r (.GPR 1#5) a) ready.count.value := by
    rw [a0, a1, loadA]
    exact state.pair owned
  have expectedA : SszNative.NatMemory.Pair (widthLoad a)
      (r (.GPR 2#5) a) (r (.GPR 3#5) a) cap := by
    rw [a2, a3, optionAddress, pointerWord, payloadWord, loadA]
    exact capPair
  have nonzero : r (.GPR 3#5) s ≠ 0#64 := by have length := owned.length; bv_omega
  have tailOwned := owned.tail_owned nonzero (state.arguments 0#5 (by simp)) state.saved.sp
  have capOwned : NatOwned (tailWrites u) expectedPointer expectedPayload := by
    intro pointerNonzero payloadNonzero
    exact finish_tail_protected owned nonzero (state.arguments 0#5 (by simp)) state.saved.sp
      (finish_local_protected (owned.optionOwned.2 pointerNonzero payloadNonzero))
  have actualOwned : NatCompare.Owned a (r (.GPR 0#5) a) (r (.GPR 1#5) a) := by
    rw [a0, a1]
    exact compare_owned tailOwned.stackLow spA (state.actual_owned owned nonempty)
  have expectedOwned : NatCompare.Owned a (r (.GPR 2#5) a) (r (.GPR 3#5) a) := by
    rw [a2, a3, optionAddress, pointerWord, payloadWord]
    exact compare_owned tailOwned.stackLow spA capOwned
  obtain ⟨fuel, v, called, callee, pcV, errorV, spV, preservedV, orderV, _, _⟩ :=
    compare_call a base ready.count.value cap codeA compareA errorA alignedA pcA
      actualA expectedA actualOwned expectedOwned
  let t := block base callReturnOps v
  have programV : v.program = u.program := by
    have same : (compareCalled a base).program = a.program := by
      simp [compareCalled, state_simp_rules]
    exact callee.program.trans (same.trans (block_program base prepareCompareOps u))
  have codeV : CodeAt v base := by simpa only [CodeAt, programV] using codeU
  have alignedV : CheckSPAlignment v := by
    simpa only [CheckSPAlignment, state_simp_rules, spV] using alignedA
  have last := callReturn_run v base codeV errorV alignedV pcV
  rcases compare_return_fields v base (compare ready.count.value cap) orderV with
    ⟨pcT, memoryT, t0, t2, t3, spT⟩
  have sp : r (.GPR 31#5) t = r (.GPR 31#5) u := spT.trans (spV.trans spA)
  have registers (reg : BitVec 5)
      (kept : reg ∈ [4#5, 19#5, 20#5, 23#5, 24#5, 25#5, 26#5]) :
      r (.GPR reg) t = r (.GPR reg) u := by
    have retKept : reg ∉ [0#5, 2#5, 3#5, 8#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at kept
      rcases kept with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have prepKept : reg ∉ [0#5, 1#5, 2#5, 3#5, 21#5, 22#5, 27#5, 28#5, 29#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at kept
      rcases kept with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have callKept : reg ∉ [0#5, 8#5, 9#5, 10#5, 11#5, 12#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at kept
      rcases kept with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have notLink : reg ≠ 30#5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at kept
      rcases kept with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have middle : r (.GPR reg) v = r (.GPR reg) a := by
      simpa [compareCalled, state_simp_rules, notLink] using callee.registers reg callKept
    exact (return_register v base reg retKept).trans
      (middle.trans (prepare_register u base reg prepKept))
  have vectors (reg : BitVec 5) : r (.SFP reg) t = r (.SFP reg) u := by
    have middle : r (.SFP reg) v = r (.SFP reg) a := by
      simpa [compareCalled, state_simp_rules] using callee.vectors reg
    exact (return_vector v base reg).trans (middle.trans (prepare_vector u base reg))
  have calledSp : r (.GPR 31#5) (compareCalled a base) = r (.GPR 31#5) u := by
    have setupSp : r (.GPR 31#5) a = r (.GPR 31#5) u := spA
    simpa [compareCalled, state_simp_rules] using setupSp
  have lowering : MemoryFrame [((r (.GPR 31#5) u).toNat - 16, 16)] u t := by
    intro address outside
    have apart := outside ((r (.GPR 31#5) u).toNat - 16, 16) (by simp)
    have nativeApart : address.toNat < (r (.GPR 31#5) (compareCalled a base)).toNat - 16 ∨
        (r (.GPR 31#5) (compareCalled a base)).toNat ≤ address.toNat := by
      rw [calledSp]
      have low := tailOwned.stackLow
      omega
    have middle : v.mem address = a.mem address := by
      simpa [compareCalled, state_simp_rules] using callee.memory address nativeApart
    exact (congrFun memoryT address).trans (middle.trans (congrFun memoryA address))
  have stack := owned.stackBound
  simp only [activationSpan, nonzero, ↓reduceIte] at stack
  have localFrame := lower_frame_local nonzero stack state.saved.sp lowering
  have saved : Saved s t := state.saved.frame lowering sp tailOwned.stackHigh (by
      right
      intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst span
      have low := tailOwned.stackLow
      right
      omega) (fun reg _ _ => congrArg (BitVec.setWidth 64) (vectors reg))
  have args : ∀ reg : BitVec 5, reg ∈ [0#5, 2#5, 3#5, 4#5] →
      r (.GPR reg) t = r (.GPR reg) s := by
    intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact t0.trans ((preservedV 27#5 (by decide) (by decide)).trans
        (a27.trans (state.arguments 0#5 (by simp))))
    · exact t2.trans ((preservedV 28#5 (by decide) (by decide)).trans
        (a28.trans (state.arguments 2#5 (by simp))))
    · exact t3.trans ((preservedV 29#5 (by decide) (by decide)).trans
        (a29.trans (state.arguments 3#5 (by simp))))
    · exact (registers 4#5 (by simp)).trans (state.arguments 4#5 (by simp))
  have cursor := localFrame.load ((r (.GPR 4#5) s).toNat + 16) 8
    (by have bound := owned.arenaBound; omega) (owned.arenaLocal.subspan 16 8 (by decide))
  refine ⟨8 + fuel + 6, t, ?_, ?_, pcT, ?_, ?_⟩
  · rw [run_plus, run_plus, first, called, last]
  · refine ⟨state.prepared, state.allocation,
      (block_program base callReturnOps v).trans (programV.trans state.program),
      (block_error base callReturnOps v).trans errorV,
      block_aligned base callReturnOps v alignedV, saved, args,
      (registers 25#5 (by simp)).trans state.preceding,
      (registers 26#5 (by simp)).trans state.counter,
      (registers 24#5 (by simp)).trans state.low,
      (registers 23#5 (by simp)).trans state.high,
      (registers 20#5 (by simp)).trans state.pointer,
      (registers 19#5 (by simp)).trans state.payload,
      finish_stored owned state localFrame, ?_,
      state.frame.trans (finish_lift_frame ready.allocation localFrame)⟩
    have same : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat =
        (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) u).toNat := by
      simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        using Option.some.inj cursor
    exact same.trans state.cursor
  · rw [return_register v base 22#5 (by decide), preservedV 22#5 (by decide) (by decide),
      a22, optionAddress, pointerWord]
  · rw [return_register v base 21#5 (by decide), preservedV 21#5 (by decide) (by decide),
      a21, optionAddress, payloadWord]

end SszArm.Delimited
