import SszArm.EmitScalarBytesSetup
import SszArm.EmitMemcpy

namespace SszArm.Emit.Scalar

open SszNative.Serialize (Desc)
open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected)

@[irreducible] def bytesFinish (s : ArmState) (base : BitVec 64) (args : Args) (size : Nat) : ArmState :=
  w .PC (base + 1004#64) (write_mem_bytes 8 args.result (BitVec.ofNat 64 size) s)

theorem bytes_finish_run (s : ArmState) (base : BitVec 64) (args : Args) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 860#64) (result : r (.GPR 19#5) s = args.result)
    (count : r (.GPR 23#5) s = BitVec.ofNat 64 size) :
    run 2 s = bytesFinish s base args size := by
  have follows : Follows base [.p860, .p864] s := by
    change r .PC s = _ at pc
    simp [Follows, Op.row, Op.effect, next, state_simp_rules, pc, BitVec.add_assoc]
  have execution := runs [.p860, .p864] s base code error aligned follows
  change run 2 s = _ at execution
  rw [execution]
  change r .PC s = _ at pc
  simp [bytesFinish, block, Op.effect, next, state_simp_rules, result, count, pc, BitVec.add_assoc]

theorem bytes_body (s : ArmState) (base : BitVec 64) (args : Args) (desc : Desc)
    (bytes : Ssz.Bytes) (size : Nat) (kind : ByteKind desc)
    (owned : Owned s args desc (.bytes bytes) size) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 820#64) (tag : r (.GPR 8#5) s = descriptorTag desc) :
    ∃ steps t, run steps s = t ∧ Produced s t args desc (.bytes bytes) size base := by
  have sizeEq := bytes_size kind owned
  subst size
  obtain ⟨setupRun, setupPC⟩ := bytes_setup_run s base args desc bytes bytes.size kind owned
    registers code error aligned pc tag
  obtain ⟨r0, r1, r2, r23⟩ := bytes_setup_arguments s args registers
  have count := owned.value_at.2.1
  have word : read_mem_bytes 8 (args.value + 16#64) s = BitVec.ofNat 64 bytes.size := by
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt owned.representable] using count
  have destination : (r (.GPR 0#5) (bytesSetup s)).toNat +
      (r (.GPR 2#5) (bytesSetup s)).toNat ≤ 2^64 := by
    rw [r0, r2, count]
    have := owned.outputBound
    have := owned.fitting
    omega
  have source : (r (.GPR 1#5) (bytesSetup s)).toNat +
      (r (.GPR 2#5) (bytesSetup s)).toNat ≤ 2^64 := by
    rw [r1, r2, count]
    exact owned.value_at.2.2.1
  have separate : Memcpy.Disjoint (r (.GPR 0#5) (bytesSetup s))
      (r (.GPR 1#5) (bytesSetup s)) (r (.GPR 2#5) (bytesSetup s)).toNat := by
    rw [r0, r1, r2, count]
    have backing := owned.backingOwned
      ((read_mem_bytes 8 (args.value + 8#64) s).toNat, bytes.size) (by simp [backingSpan])
    unfold Memcpy.Disjoint
    by_cases empty : bytes.size = 0
    · omega
    · rcases backing with impossible | separated
      · exact False.elim (empty impossible)
      · have apart := separated (args.output.toNat, bytes.size) (by simp [writesFor, empty])
        change (read_mem_bytes 8 (args.value + 8#64) s).toNat + bytes.size ≤ args.output.toNat ∨
          args.output.toNat + bytes.size ≤ (read_mem_bytes 8 (args.value + 8#64) s).toNat at apart
        omega
  have setupCode : CodeAt (bytesSetup s) base := by
    simpa only [CodeAt, bytes_setup_program] using code
  have setupError := (bytes_setup_error s).trans error
  let copied := run (Memcpy.fuel bytes.size + 1) (bytesSetup s)
  have post : CopyPost .bytes (bytesSetup s) copied base := by
    simpa only [copied, r2, count] using
      copy_correct .bytes (bytesSetup s) base setupCode setupError setupPC destination source separate
  have resultReg : r (.GPR 19#5) copied = args.result :=
    (post.registers _ (by decide)).trans
      ((bytes_setup_register s _ (by decide)).trans registers.result)
  have stackReg : r (.GPR 31#5) copied = r (.GPR 31#5) s :=
    (post.registers _ (by decide)).trans (bytes_setup_register s _ (by decide))
  have countReg : r (.GPR 23#5) copied = BitVec.ofNat 64 bytes.size :=
    (post.registers _ (by decide)).trans (r23.trans word)
  have copiedCode : CodeAt copied base := by
    simpa only [CodeAt, post.program] using setupCode
  have copiedAligned : CheckSPAlignment copied := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, stackReg] using aligned
  have finishRun := bytes_finish_run copied base args bytes.size copiedCode post.error
    copiedAligned post.pc resultReg countReg
  have resultBound : args.result.toNat + 8 ≤ 2^64 := by have := owned.resultBound; omega
  have outputBound : args.output.toNat + bytes.size ≤ 2^64 := by
    have := owned.outputBound
    have := owned.fitting
    omega
  have storeFrame := Delimited.store_frame copied args.result 8 (BitVec.ofNat 64 bytes.size) resultBound
  have outputProtected : Protected [(args.result.toNat, 8)] args.output.toNat bytes.size := by
    by_cases empty : bytes.size = 0
    · exact Or.inl empty
    · right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      rcases owned.outputResult with zero | separated
      · have := owned.fitting; omega
      · have apart := separated (args.result.toNat, 8) (by simp)
        have := owned.fitting
        change args.output.toNat + bytes.size ≤ args.result.toNat ∨
          args.result.toNat + 8 ≤ args.output.toNat
        change args.output.toNat + args.capacity.toNat ≤ args.result.toNat ∨
          args.result.toNat + 8 ≤ args.output.toNat at apart
        omega
  have copiedBytes : SszNative.ByteView.BytesAt (widthLoad copied) args.output.toNat bytes := by
    intro index within
    have observation := post.copied index 1 (by rw [r2, count]; omega)
    rw [r0, r1, load_eq_of_mem_eq (bytes_setup_memory s)] at observation
    exact observation.trans (owned.value_at.2.2.2 index within)
  have storedBytes := storeFrame.bytes args.output bytes outputBound outputProtected copiedBytes
  refine ⟨9 + ((Memcpy.fuel bytes.size + 1) + 2), bytesFinish copied base args bytes.size, ?_, ?_⟩
  · rw [run_plus, setupRun, run_plus]
    exact finishRun
  · constructor
    · simp [bytesFinish, state_simp_rules]
    · simpa only [bytesFinish, state_simp_rules, bytes_setup_program] using post.program
    · simpa (config := {decide := true}) [bytesFinish, state_simp_rules] using post.error
    · simpa (config := {decide := true}) [bytesFinish, state_simp_rules] using resultReg
    · simpa (config := {decide := true}) [bytesFinish, state_simp_rules] using stackReg.trans registers.stack
    · simp only [bytesFinish, state_simp_rules]
      exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ resultBound
    · rw [bytes_emit desc bytes kind]
      have memory : (bytesFinish copied base args bytes.size).mem =
          (write_mem_bytes 8 args.result (BitVec.ofNat 64 bytes.size) copied).mem := by
        simp only [bytesFinish, state_simp_rules]
      rw [load_eq_of_mem_eq memory]
      exact storedBytes
    · intro address outside
      have resultOutside := outside (args.result.toNat, 8) (by simp [bodyWrites])
      have copiedOutside : ∀ span ∈ [(args.output.toNat, bytes.size)],
          address.toNat < span.1 ∨ span.1 + span.2 ≤ address.toNat := by
        intro span member
        simp only [List.mem_singleton] at member
        subst span
        by_cases empty : bytes.size = 0
        · change address.toNat < args.output.toNat ∨ args.output.toNat + bytes.size ≤ address.toNat
          omega
        · exact outside _ (by simp [bodyWrites, empty])
      have copiedFrame := post.frame
      rw [r0, r2, count] at copiedFrame
      simp only [bytesFinish, state_simp_rules]
      rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address resultBound resultOutside,
        copiedFrame address copiedOutside]
      exact congrFun (bytes_setup_memory s) address
    · intro reg member
      have copyUntouched : reg ∉ [1#5, 2#5, 3#5, 4#5, 30#5] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> decide
      have setupUntouched : reg ∉ [0#5, 1#5, 2#5, 8#5, 23#5] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> decide
      simpa (config := {decide := true}) [bytesFinish, state_simp_rules] using
        (post.registers reg copyUntouched).trans (bytes_setup_register s reg setupUntouched)
    · intro reg low high
      have nonzero : reg ≠ 0#5 := by bv_omega
      have preserved := (post.vectors reg nonzero).trans (bytes_setup_vector s reg)
      simpa (config := {decide := true}) [bytesFinish, state_simp_rules] using congrArg (BitVec.setWidth 64) preserved

end SszArm.Emit.Scalar
