import SszArm.SerializeSizeNormalize

namespace SszArm.Serialize.Size

open SszNative (NatOperand)

/-- Small and physically empty values execute no spill at all. -/
def actualWrites (s : ArmState) : NatOperand → List Delimited.Span
  | .small _ => []
  | .large _ [] => []
  | .large _ (_ :: _) => writes s

def destination (base : BitVec 64) (number : Nat) (capacity : BitVec 64) : BitVec 64 :=
  if number < 2^64 then
    if number ≤ capacity.toNat then base + 648#64 else base + 432#64
  else base + 224#64

structure Post (s t : ArmState) (base : BitVec 64) (operand : NatOperand)
    (capacity : BitVec 64) : Prop where
  frame : Frame s t
  footprint : Delimited.MemoryFrame (actualWrites s operand) s t
  input : NatDivision.OperandPreserved s t operand
  pc : read_pc t = destination base operand.value capacity
  payload : operand.value < 2^64 → r (.GPR 5#5) t = BitVec.ofNat 64 operand.value

theorem Post.success_iff {s t : ArmState} {base capacity : BitVec 64} {operand : NatOperand}
    (post : Post s t base operand capacity) :
    read_pc t = base + 648#64 ↔ operand.value < 2^64 ∧ operand.value ≤ capacity.toNat := by
  rw [post.pc]
  by_cases host : operand.value < 2^64 <;>
    by_cases fits : operand.value ≤ capacity.toNat <;>
    simp [destination, host, fits] <;> bv_omega

theorem Post.host_error_iff {s t : ArmState} {base capacity : BitVec 64} {operand : NatOperand}
    (post : Post s t base operand capacity) :
    read_pc t = base + 224#64 ↔ 2^64 ≤ operand.value := by
  rw [post.pc]
  by_cases host : operand.value < 2^64 <;>
    by_cases fits : operand.value ≤ capacity.toNat <;>
    simp [destination, host, fits] <;> bv_omega

theorem Post.capacity_error_iff {s t : ArmState} {base capacity : BitVec 64} {operand : NatOperand}
    (post : Post s t base operand capacity) :
    read_pc t = base + 432#64 ↔ operand.value < 2^64 ∧ capacity.toNat < operand.value := by
  rw [post.pc]
  by_cases host : operand.value < 2^64 <;>
    by_cases fits : operand.value ≤ capacity.toNat <;>
    simp [destination, host, fits] <;> bv_omega

theorem capacity_run (s : ArmState) (base capacity : BitVec 64) (number : Nat)
    (code : Serialize.CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 424#64) (cap : r (.GPR 23#5) s = capacity)
    (payload : r (.GPR 5#5) s = BitVec.ofNat 64 number) (bound : number < 2^64) :
    ∃ t, run 2 s = t ∧ Frame s t ∧ t.mem = s.mem ∧
      read_pc t = destination base number capacity ∧
      r (.GPR 5#5) t = BitVec.ofNat 64 number := by
  have carry : (AddWithCarry capacity (~~~(BitVec.ofNat 64 number)) 1#1).2.c = 1#1 ↔
      number ≤ capacity.toNat := by
    rw [Udivti3.cmp_carry]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  let ops : List Serialize.Op := [.p424, .p428]
  let t := Serialize.block base ops s
  have follows : Serialize.Follows base ops s := by
    change r .PC s = base + 424#64 at pc
    simp [ops, Serialize.Follows, Serialize.Op.row, Serialize.Op.effect,
      Serialize.put, Serialize.next, Emit.Dispatch.compare64, Emit.Dispatch.next,
      state_simp_rules, pc, BitVec.add_assoc]
  refine ⟨t, Serialize.block_run base ops s code error aligned follows,
    readonly_frame base ops s (by decide), readonly_memory base ops s (by decide), ?_, ?_⟩
  · simp [t, ops, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
      Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules, cap, payload, carry,
      destination, bound]
  · simpa [t, ops, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
      Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules] using payload

/-- PC152 through the actual host-size and output-capacity guards, for every
    original Nat representation. Oversized naturals stop before the host-error
    writer; insufficient output stops before the capacity-error writer; success
    stops before argument setup for emit. No future execution is a premise. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (operand : NatOperand)
    (capacity : BitVec 64)
    (code : Serialize.CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 152#64)
    (pointer : r (.GPR 8#5) s = operand.pointer)
    (payload : r (.GPR 5#5) s = operand.payload)
    (cap : r (.GPR 23#5) s = capacity)
    (input : operand.At (UintCodec.widthLoad s))
    (owned : NatDivision.OperandOwned [((r (.GPR 31#5) s).toNat - 16, 16)] operand)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    ∃ fuel t, run fuel s = t ∧ Post s t base operand capacity := by
  have finish (fuel : Nat) (t : ArmState) (executed : run fuel s = t)
      (frame : Frame s t) (footprint : Delimited.MemoryFrame (actualWrites s operand) s t)
      (pcT : read_pc t = destination base operand.value capacity)
      (valueT : operand.value < 2^64 → r (.GPR 5#5) t = BitVec.ofNat 64 operand.value) :
      ∃ fuel t, run fuel s = t ∧ Post s t base operand capacity :=
    ⟨fuel, t, executed, frame, footprint,
      NatDivision.operand_preserved frame.memory16 operand input owned, pcT, valueT⟩
  cases operand with
  | small data =>
    have address : r (.GPR 8#5) s = 0#64 := pointer
    have valueS : r (.GPR 5#5) s = data := payload
    let u := Serialize.block base [.p152] s
    have runEntry : run 1 s = u :=
      Serialize.block_run base [.p152] s code error aligned ⟨pc, trivial⟩
    have entryFrame : Frame s u := readonly_frame base _ s (by decide)
    have pcU : read_pc u = base + 424#64 := by
      simp [u, Serialize.block, Serialize.Op.effect, state_simp_rules, address]
    have valueU : r (.GPR 5#5) u = BitVec.ofNat 64 data.toNat := by
      simpa [u, Serialize.block, Serialize.Op.effect, state_simp_rules] using valueS
    obtain ⟨t, runCap, capFrame, capMemory, pcT, valueT⟩ := capacity_run u base capacity data.toNat
      (entryFrame.code code) (entryFrame.error.trans error) (entryFrame.aligned aligned)
      pcU ((entryFrame.registers _ (by decide)).trans cap) valueU data.isLt
    apply finish 3 t
    · rw [show 3 = 1 + 2 by decide, run_plus, runEntry, runCap]
    · exact entryFrame.trans capFrame
    · have memory : t.mem = s.mem := capMemory.trans (readonly_memory base [.p152] s (by decide))
      intro a outside
      exact congrFun memory a
    · simpa [NatOperand.value, NatOperand.words, SszNative.Limbs.value] using pcT
    · intro fits
      simpa [NatOperand.value, NatOperand.words, SszNative.Limbs.value] using valueT
  | large address words =>
    have nonnull : address ≠ 0#64 := by
      have positive := input.1
      intro zero
      simp [zero] at positive
    have addressS : r (.GPR 8#5) s = address := pointer
    have countS : r (.GPR 5#5) s = BitVec.ofNat 64 words.length := payload
    have source := NatNarrow.large_source s address words
      [((r (.GPR 31#5) s).toNat - 16, 16)] input owned (by simp) stack
    have stored := NatNarrow.large_words s address words input
    cases words with
    | nil =>
      let ops : List Serialize.Op := [.p152, .p156, .p160, .p164, .p416]
      let t := Serialize.block base ops s
      have follows : Serialize.Follows base ops s := by
        change r .PC s = base + 152#64 at pc
        simp [ops, Serialize.Follows, Serialize.Op.row, Serialize.Op.effect,
          Serialize.put, Serialize.next, state_simp_rules, pc, addressS, nonnull,
          countS, BitVec.add_assoc]
      apply finish 5 t
      · exact Serialize.block_run base ops s code error aligned follows
      · exact readonly_frame base ops s (by decide)
      · have memory := readonly_memory base ops s (by decide)
        intro a outside
        exact congrFun memory a
      · simp [t, ops, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
          state_simp_rules, countS, destination, NatOperand.value, NatOperand.words,
          SszNative.Limbs.value]
      · intro fits
        simp [t, ops, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
          state_simp_rules, countS, NatOperand.value, NatOperand.words, SszNative.Limbs.value]
    | cons first rest =>
      let words := first :: rest
      let ops : List Serialize.Op := [.p152, .p156]
      let u := Serialize.block base ops s
      have follows : Serialize.Follows base ops s := by
        change r .PC s = base + 152#64 at pc
        simp [ops, Serialize.Follows, Serialize.Op.row, Serialize.Op.effect,
          Serialize.put, Serialize.next, state_simp_rules, pc, addressS, nonnull, BitVec.add_assoc]
      have runEntry : run 2 s = u := Serialize.block_run base ops s code error aligned follows
      have entryFrame : Frame s u := readonly_frame base ops s (by decide)
      have pcU : read_pc u = base + 160#64 := by
        simp [u, ops, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
          state_simp_rules, addressS, nonnull, BitVec.add_assoc]
      have countU : r (.GPR 5#5) u = BitVec.ofNat 64 words.length := by
        simpa [u, ops, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
          state_simp_rules, words] using countS
      have indexU : r (.GPR 10#5) u = BitVec.ofNat 64 words.length - 1#64 := by
        simp [u, ops, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
          state_simp_rules, countS, words]
      obtain ⟨fuel, v, runScan, scanFrame, pcV, valueV⟩ := large_ready u base address words
        (entryFrame.code code) (entryFrame.error.trans error) (entryFrame.aligned aligned)
        pcU ((entryFrame.registers _ (by decide)).trans addressS) countU indexU
        (entryFrame.source _ _ source) (entryFrame.words _ _ source stored) (by simp [words])
      have totalFrame := entryFrame.trans scanFrame
      by_cases fits : SszNative.Limbs.value words < 2^64
      · have capacityPC : read_pc v = base + 424#64 := by simpa [fits] using pcV
        obtain ⟨t, runCap, capFrame, capMemory, pcT, valueT⟩ :=
          capacity_run v base capacity (SszNative.Limbs.value words)
            (totalFrame.code code) (totalFrame.error.trans error) (totalFrame.aligned aligned)
            capacityPC ((totalFrame.registers _ (by decide)).trans cap) (valueV fits) fits
        have allFrame := totalFrame.trans capFrame
        apply finish (2 + fuel + 2) t
        · rw [run_plus, run_plus, runEntry, runScan, runCap]
        · exact allFrame
        · exact allFrame.memory
        · exact pcT
        · exact fun _ => valueT
      · apply finish (2 + fuel) v
        · rw [run_plus, runEntry, runScan]
        · exact totalFrame
        · exact totalFrame.memory
        · simpa [destination, fits, NatOperand.value, NatOperand.words, words] using pcV
        · intro impossible
          exact False.elim (fits impossible)

end SszArm.Serialize.Size
