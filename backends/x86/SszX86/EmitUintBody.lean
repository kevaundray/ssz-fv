import SszX86.EmitUintWidth
import SszX86.EmitUintComplete

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open SszNative
open BoolCodec UintCodec
open Instructions
open UintCodec.Large (get)

structure Loaded (original current : MachineData) (number : NatOperand) (count : Nat) : Prop where
  memory : current.dmem = original.dmem
  stack : current.regs.rsp = original.regs.rsp
  result : current.regs.rbx = original.regs.rbx
  output : current.regs.r14 = original.regs.r14
  vector : current.zmms = original.zmms
  length : get current .rsi = BitVec.ofNat 64 count
  pointer : get current .rdi = number.pointer
  payload : get current .rdx = number.payload

theorem initial_loop (original current : MachineData) (number : NatOperand) (count : Nat)
    (physical : count < 2 ^ 64) (loaded : Loaded original current number count)
    (flags : StatusFlags) :
    LoopInv original (pairReady current (match number with | .small _ => false | .large _ _ => true) flags)
      number count 0 := by
  cases number with
  | small limb =>
    refine ⟨loaded.stack, loaded.result, loaded.output, loaded.vector, loaded.length,
      rfl, rfl, loaded.payload, ?_, trivial, ?_, ?_⟩
    · change get current .rsi &&& 0xfffffffffffffffe#64 = _
      rw [loaded.length, even_length count physical]
    · intro impossible
      omega
    · change Prefix original.dmem current.dmem _ _ 0
      rw [loaded.memory]
      exact prefix_empty _ _ _
  | large pointer limbs =>
    refine ⟨loaded.stack, loaded.result, loaded.output, loaded.vector, loaded.length,
      rfl, rfl, loaded.payload, loaded.pointer, ?_, trivial, ?_⟩
    · change get current .rsi &&& 0xfffffffffffffffe#64 = _
      rw [loaded.length, even_length count physical]
    · change Prefix original.dmem current.dmem _ _ 0
      rw [loaded.memory]
      exact prefix_empty _ _ _

/-- All actual number paths from their representation branch, with arbitrary
logical width and original readonly limbs. -/
theorem loaded_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original current : MachineData) (logicalWidth number : NatOperand) (count : Nat)
    (owned : Owned original logicalWidth number count) (positive : 0 < count)
    (loaded : Loaded original current number count) :
    Eventually (step e) (OutputPost original number count base)
      (current, base + match number with | .small _ => 876 | .large _ _ => 616) := by
  have static := LoopOwned.of_owned original logicalWidth number count owned
  have hprefix : Prefix original.dmem current.dmem original.regs.r14.toBitVec
      (Limbs.bytes number.words count) 0 := by
    rw [loaded.memory]
    exact prefix_empty _ _ _
  by_cases one : count = 1
  · subst count
    cases number with
    | small limb =>
      apply one_small_setup e base hc current _ loaded.length
      intro flags
      apply complete_scalar e base hc original
        {current with regs := {current.regs with rax := 0}, status := flags}
        logicalWidth (.small limb) 1 0 owned rfl
        loaded.stack loaded.result loaded.vector loaded.length
      · simpa only [UintCodec.Large.get, Reg64s.get64, BitVec.add_zero] using
          congrArg UInt64.toBitVec loaded.output
      · rfl
      · exact loaded.payload
      · exact hprefix
    | large pointer limbs =>
      have physical : limbs.length < 2 ^ 64 := by have := static.operand.2.2.1; omega
      have len : (get current .rdx).toNat = limbs.length := by
        rw [loaded.payload]
        exact Nat.mod_eq_of_lt physical
      apply one_large_setup e base hc current (limbs[0]?.getD 0) _ loaded.length
      · intro nonempty
        rw [len] at nonempty
        have observed := widthLoad_eq original.dmem _ 8 _ (static.operand.2.2.2 ⟨0, nonempty⟩)
        rw [loaded.pointer, loaded.memory]
        simpa only [Nat.mul_zero, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          NatOperand.pointer, Fin.getElem_fin, List.getElem?_eq_getElem nonempty,
          Option.getD_some] using observed
      · intro empty
        rw [len] at empty
        simp [List.getElem?_eq_none (by omega : limbs.length ≤ 0)]
      · intro flags
        apply complete_scalar e base hc original
          {current with
            regs := {current.regs with rax := 0, rcx := 0, rdx := UInt64.ofBitVec (limbs[0]?.getD 0)}
            status := flags}
          logicalWidth (.large pointer limbs) 1 0 owned rfl
          loaded.stack loaded.result loaded.vector loaded.length
        · simpa only [UintCodec.Large.get, Reg64s.get64, BitVec.add_zero] using
            congrArg UInt64.toBitVec loaded.output
        · rfl
        · rfl
        · exact hprefix
  · have many : 2 ≤ count := by omega
    have notOne : get current .rsi ≠ 1#64 := by
      intro equal
      rw [loaded.length] at equal
      have value := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt static.bounded] at value
      exact one value
    cases number with
    | small limb =>
      apply pair_setup e base hc current false _ notOne
      intro flags
      refine small_loop_runs e base hc original limb count static
        (OutputPost original (.small limb) count base) ?_ 0 (pairReady current false flags) ?_ ?_ ?_
      · intro final inv
        exact small_complete e base hc original final logicalWidth limb count owned many inv
      · rfl
      · omega
      · exact initial_loop original current (.small limb) count static.bounded loaded flags
    | large pointer limbs =>
      apply pair_setup e base hc current true _ notOne
      intro flags
      refine large_loop_runs e base hc original pointer limbs count static
        (OutputPost original (.large pointer limbs) count base) ?_ 0 (pairReady current true flags) ?_ ?_ ?_
      · intro final inv
        exact large_complete e base hc original final logicalWidth pointer limbs count owned inv
      · rfl
      · omega
      · exact initial_loop original current (.large pointer limbs) count static.bounded loaded flags

/-- The zero path writes only the length slot; even the number header is not
loaded. Empty output imposes no output-byte mapping or pointer requirement. -/
theorem zero_body (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original current : MachineData) (logicalWidth number : NatOperand)
    (owned : Owned original logicalWidth number 0)
    (memory : current.dmem = original.dmem)
    (stack : current.regs.rsp = original.regs.rsp)
    (result : current.regs.rbx = original.regs.rbx)
    (vector : current.zmms = original.zmms) :
    Eventually (step e) (OutputPost original number 0 base) (current, base + 653) := by
  have byteSize : (Limbs.bytes number.words 0).size = 0 := by
    simp only [Limbs.bytes, Array.size_ofFn]
  have output : BytesAt current.dmem original.regs.r14.toBitVec (Limbs.bytes number.words 0) := by
    intro i hi
    rw [byteSize] at hi
    omega
  have frame : MemoryFrame original.dmem current.dmem
      (BodyWritable original (Limbs.bytes number.words 0).size) := by
    rw [memory]
    intro _ _
    rfl
  have apart : Large.Disjoint original.regs.r14.toBitVec original.regs.rbx.toBitVec
      (Limbs.bytes number.words 0).size 8 := by
    intro i hi
    rw [byteSize] at hi
    omega
  have finished (flags : StatusFlags) : OutputPost original number 0 base
      (Bits.lengthStored {current with regs := {current.regs with rsi := 0}, status := flags} 0,
        base + 1593) := by
    refine ⟨rfl, ?_, ?_⟩
    · have body := Bits.length_post original
        {current with regs := {current.regs with rsi := 0}, status := flags}
        (Limbs.bytes number.words 0) (by rw [byteSize]; decide)
        stack result vector output frame apart
      simpa only [byteSize] using body
    · change MemoryFrame original.dmem
        (Mem.storeInt current.dmem current.regs.rbx.toBitVec 8 (BitVec.ofNat 64 0).toInt)
        (Writable original 0)
      rw [memory, result]
      exact Bits.frame_mono
        (Bits.store_frame original.dmem original.regs.rbx.toBitVec 8 (BitVec.ofNat 64 0).toInt)
        (fun _ inside => Or.inr inside)
  apply zero_runs e base hc current
  · rw [memory, result]
    simpa using Large.mapped_load original.dmem original.regs.rbx.toBitVec 8 0 8 owned.result (by omega)
  · intro flags
    exact Eventually.done _ (finished flags)

/-- Actual UInt emitter body, including tag check, arbitrary padded width
normalization, original number loads, all zero-extension bytes, and length
publication at the common PC1593. Preconditions concern only PC50 originals. -/
theorem output_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original : MachineData) (logicalWidth number : NatOperand) (count : Nat)
    (owned : Owned original logicalWidth number count) :
    Eventually (step e) (OutputPost original number count base) (original, base + 50) := by
  have measured := measured logicalWidth number count owned.valid
  have physical := width_physical logicalWidth number count original.regs.r9 owned.valid owned.capacity
  apply eventually_trans (step e) (WidthPost original base logicalWidth)
    (OutputPost original number count base) _
    (width_runs e base hc original logicalWidth owned.tag owned.widthAt physical.1)
  intro state post
  obtain ⟨a, c, d, flags, memoryState, pc⟩ := post
  cases state with
  | mk current address =>
    simp only at memoryState pc
    subst current
    rcases pc with normal | empty
    · subst address
      apply capacity_runs e base hc
      · change (BitVec.ofNat 64 logicalWidth.value).toNat ≤ original.regs.r9.toNat
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical.1, measured.1]
        exact owned.capacity
      · intro capacityFlags
        by_cases zero : count = 0
        · subst count
          uint_exec at592 using hc
          uint_exec at595 using hc
          have zeroFlag : (BitVec.ofNat 64 logicalWidth.value == BitVec.zero 64) = true := by
            rw [measured.1]
            decide
          simp only [widthState, StatusFlags.from_result, zeroFlag, ↓reduceIte]
          exact zero_body e base hc original _ logicalWidth number owned rfl rfl rfl rfl
        · apply nonzero_runs e base hc
          · change BitVec.ofNat 64 logicalWidth.value ≠ 0#64
            intro equal
            have value := congrArg BitVec.toNat equal
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical.1] at value
            omega
          · intro nonzeroFlags
            have pair := width_pair_loads original (original.regs.r12.toBitVec + 8) number owned.numberAt
            apply number_runs e base hc _ number.pointer number.payload
            · exact pair.1
            · change Mem.loadInt original.dmem (original.regs.r12.toBitVec + 16) 8 =
                some (number.payload.toNat : Int)
              simpa only [BitVec.add_assoc, show (8 : BitVec 64) + 8 = 16 by decide] using pair.2
            · intro loadedFlags
              have loadedState : Loaded original
                  {widthState original a c d (BitVec.ofNat 64 logicalWidth.value) nonzeroFlags with
                    regs := {(widthState original a c d (BitVec.ofNat 64 logicalWidth.value) nonzeroFlags).regs with
                      rdi := UInt64.ofBitVec number.pointer, rdx := UInt64.ofBitVec number.payload},
                    status := loadedFlags} number count := by
                refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
                simp only [widthState, UintCodec.Large.get, Reg64s.get64, measured.1]
              cases number with
              | small limb =>
                exact loaded_runs e base hc original _ logicalWidth (.small limb) count owned (by omega) loadedState
              | large pointer limbs =>
                have nonnull : pointer ≠ 0#64 := by
                  intro equal
                  have positive := owned.numberAt.2.2.1
                  simp only [equal, BitVec.toNat_ofNat, Nat.zero_mod, Nat.lt_irrefl] at positive
                simp only [NatOperand.pointer, nonnull, ↓reduceIte]
                exact loaded_runs e base hc original _ logicalWidth (.large pointer limbs) count owned (by omega) loadedState
    · obtain ⟨emptyPc, zeroWidth⟩ := empty
      subst address
      have zero : count = 0 := by omega
      subst count
      exact zero_body e base hc original _ logicalWidth number owned rfl rfl rfl rfl

/-- The full body result retains both exact original padded operands in addition
to the shared endpoint contract and the strictly actual output/result frame. -/
theorem body_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original : MachineData) (logicalWidth number : NatOperand) (count : Nat)
    (owned : Owned original logicalWidth number count) :
    Eventually (step e)
      (fun state => state.2 = base + 1593 ∧
        BodyPost original (Serialize.emit (.uint logicalWidth) (.uint number)) state.1 ∧
        MemoryFrame original.dmem state.1.dmem (Writable original count) ∧
        NatAt state.1.dmem (original.regs.rsi.toBitVec + 8) logicalWidth ∧
        NatAt state.1.dmem (original.regs.r12.toBitVec + 8) number)
      (original, base + 50) := by
  apply eventually_weaken _ _ _ _ _ (output_runs e base hc original logicalWidth number count owned)
  intro state post
  refine ⟨post.pc, ?_, post.exactFrame, ?_, ?_⟩
  · simpa only [Serialize.emit, (measured logicalWidth number count owned.valid).1] using post.body
  · exact natAt_preserved _ _ _ _ _ post.exactFrame owned.widthAt
      (fun a borrowed => owned.readonly a (Or.inl borrowed))
  · exact natAt_preserved _ _ _ _ _ post.exactFrame owned.numberAt
      (fun a borrowed => owned.readonly a (Or.inr borrowed))

end SszX86.Emit.Uint
