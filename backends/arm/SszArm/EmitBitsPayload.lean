import SszArm.EmitBitsTailState
import SszArm.EmitBitsTailGuards

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

def Path.isList : Path → Bool
  | .list => true | .vector => false

def Path.lastGuard : Path → TailGuard
  | .list => .listLast | .vector => .vectorLast

def Path.remainderStage (path : Path) : MaskStage :=
  if path.isList then .listRemainder else .vectorRemainder

def Path.maskStage (path : Path) : MaskStage :=
  if path.isList then .listMask else .vectorMask

def Path.maskEnd : Path → Nat
  | .list => 724 | .vector => 1332

structure PayloadPost (s t : ArmState) (base : BitVec 64) (args : Args) (path : Path)
    (desc : Desc) (bits : Packed) (size : Nat) : Prop where
  pc : read_pc t = base + BitVec.ofNat 64 path.maskEnd
  program : t.program = s.program
  error : read_err t = .None
  owned : Owned t args desc (.bits bits) size
  work : WorkRegisters t args path bits
  byte : (r (.GPR 8#5) t).setWidth 8 =
    (bits.bytes[bits.count.toNat / 8]! &&& UInt8.ofNat (2 ^ (bits.count.toNat % 8) - 1)).toBitVec
  frame : MemoryFrame (bodyWrites args size) s t
  output : ∀ index, index < bits.count.toNat / 8 →
    widthLoad t (args.output.toNat + index) 1 = widthLoad s (args.output.toNat + index) 1
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5] → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem payload_run (path : Path) (s : ArmState) (base : BitVec 64) (args : Args)
    (desc : Desc) (bits : Packed) (size : Nat) (kind : IsBits desc)
    (owned : Owned s args desc (.bits bits) size) (work : WorkRegisters s args path bits)
    (hasTail : bits.count.toNat % 8 ≠ 0)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.indexStart) :
    ∃ t, run 15 s = t ∧ PayloadPost s t base args path desc bits size := by
  let a := indexed s
  let b := byteLoaded a
  let c := tailGuarded path.lastGuard b
  let d := maskResult path.remainderStage c
  let e := maskResult path.maskStage d
  have aRun := index_run path s base code error aligned pc
  have aWork := work.of_memory owned (indexed_memory s) (by
    intro reg untouched
    apply indexed_register
    simp_all)
  have aInput : Owned a args desc (.bits bits) size := owned.of_mem_eq (indexed_memory s)
  have aPC : read_pc a = base + BitVec.ofNat 64 path.readStart := by
    rw [indexed_pc, pc]
    cases path <;> simp [Path.indexStart, Path.readStart, BitVec.add_assoc]
  have aCode : CodeAt a base := by simpa only [a, CodeAt, indexed_program] using code
  have aError : read_err a = .None := (indexed_error s).trans error
  have aAligned := aligned_of_stack aligned (indexed_register s 31#5 (by decide))
  have stackLow : 16 ≤ (r (.GPR 31#5) a).toNat := by
    have low := owned.stackLow
    rw [aWork.stack, Args.bodySP]
    bv_omega
  have bRun := byte_read_run path a base aCode aError aAligned aPC stackLow
  have bFrame := byteLoaded_frame size aWork.stack owned.stackLow
  have bInput := aInput.of_body_frame bFrame
  have bWork := aWork.of_body_frame aInput bFrame (by
    intro reg untouched
    apply byteLoaded_register
    simp_all)
  have bPC : read_pc b = base + BitVec.ofNat 64 path.lastGuard.start := by
    rw [byteLoaded_pc, aPC]
    cases path <;> simp [Path.readStart, Path.lastGuard, TailGuard.start, BitVec.add_assoc]
  have bCode : CodeAt b base := by simpa only [b, CodeAt, byteLoaded_program] using aCode
  have bError : read_err b = .None := (byteLoaded_error a).trans aError
  have bAligned := aligned_of_stack aAligned (byteLoaded_register a 31#5 (by decide))
  have backingSize := (backing_guards bits).2.2 hasTail
  have good : path.lastGuard.good b := by
    have equal : r (.GPR 9#5) b = r (.GPR 24#5) b := by
      apply BitVec.eq_of_toNat_eq
      rw [byteLoaded_register a 9#5 (by decide), indexed_word, BitVec.toNat_add,
        work.full, bWork.backing, BitVec.toNat_ofNat, ← backingSize]
      exact Nat.mod_eq_of_lt owned.physical
    cases path <;> exact equal
  have cRun := tail_guard_run path.lastGuard b base bCode bError bAligned bPC
  have cPC : read_pc c = base + BitVec.ofNat 64 path.remainderStage.start := by
    rw [tailGuarded_pc path.lastGuard b good, bPC]
    cases path <;> simp [Path.lastGuard, TailGuard.start, Path.remainderStage, Path.isList,
      MaskStage.start, BitVec.add_assoc]
  have cCode : CodeAt c base := by simpa only [c, CodeAt, tailGuarded_program] using bCode
  have cError : read_err c = .None := (tailGuarded_error path.lastGuard b).trans bError
  have cAligned := aligned_of_stack bAligned (tailGuarded_register path.lastGuard b 31#5)
  have cInput : Owned c args desc (.bits bits) size := bInput.of_mem_eq (tailGuarded_memory _ _)
  have cWork := bWork.of_memory bInput (tailGuarded_memory path.lastGuard b)
    (fun reg _ => tailGuarded_register path.lastGuard b reg)
  have lowReg : (if path.isList then 26#5 else 25#5) = path.low := by cases path <;> rfl
  have remainder : (r (.GPR (if path.isList then 26#5 else 25#5)) c &&& 7#64).toNat = bits.count.toNat % 8 := by
    rw [lowReg, cWork.low]
    exact (count_quotient bits owned.physical).2
  have nonzero : r (.GPR (if path.isList then 26#5 else 25#5)) c &&& 7#64 ≠ 0#64 := by
    intro zero
    have number := congrArg BitVec.toNat zero
    rw [remainder] at number
    exact hasTail number
  have dRun := mask_run path.remainderStage c base cCode cError cAligned cPC
  have dPC : read_pc d = base + BitVec.ofNat 64 path.maskStage.start := by
    dsimp only [d, Path.remainderStage]
    rw [remainder_pc c path.isList nonzero, cPC]
    cases path <;> simp [Path.remainderStage, Path.maskStage, Path.isList, MaskStage.start, BitVec.add_assoc]
  have dCode : CodeAt d base := by simpa only [d, CodeAt, maskResult_program] using cCode
  have dError : read_err d = .None := (maskResult_error path.remainderStage c).trans cError
  have dAligned := aligned_of_stack cAligned (maskResult_register path.remainderStage c 31#5 (by decide))
  have dInput : Owned d args desc (.bits bits) size := cInput.of_mem_eq (maskResult_memory _ _)
  have dWork := cWork.of_memory cInput (maskResult_memory path.remainderStage c)
    (maskResult_register path.remainderStage c)
  have remainderD : (r (.GPR 9#5) d).toNat = bits.count.toNat % 8 := by
    dsimp only [d, Path.remainderStage]
    rw [remainder_word c path.isList]
    exact remainder
  have byteD : (r (.GPR 8#5) d).setWidth 8 = bits.bytes[bits.count.toNat / 8]!.toBitVec := by
    dsimp only [d, Path.remainderStage]
    rw [remainder_byte c path.isList, tailGuarded_register, byteLoaded_byte,
      tail_read_byte path aInput aWork hasTail]
    simp
  have eRun := mask_run path.maskStage d base dCode dError dAligned dPC
  have ePC : read_pc e = base + BitVec.ofNat 64 path.maskEnd := by
    dsimp only [e, Path.maskStage]
    rw [masked_pc d path.isList, dPC]
    cases path <;> simp [Path.maskStage, Path.isList, MaskStage.start, Path.maskEnd, BitVec.add_assoc]
  have eInput : Owned e args desc (.bits bits) size := dInput.of_mem_eq (maskResult_memory _ _)
  have eWork := dWork.of_memory dInput (maskResult_memory path.maskStage d)
    (maskResult_register path.maskStage d)
  have eMemory : e.mem = b.mem := by simp [e, d, c]
  have eFrame : MemoryFrame (bodyWrites args size) s e := by
    intro address outside
    rw [eMemory]
    exact (bFrame address outside).trans (congrFun (indexed_memory s) address)
  refine ⟨e, ?_, ePC, ?_, ?_, eInput, eWork, ?_, eFrame, ?_, ?_, ?_⟩
  · change run (1 + (7 + (2 + (2 + 3)))) s = _
    rw [run_plus, aRun, run_plus, bRun, run_plus, cRun, run_plus]
    have dr : run 2 c = d := by cases path <;> exact dRun
    rw [dr]
    cases path <;> exact eRun
  · simp [e, d, c, b, a]
  · simpa only [e, d, c, b, a, maskResult_error, tailGuarded_error,
      byteLoaded_error, indexed_error] using error
  · dsimp only [e, Path.maskStage]
    rw [masked_byte d path.isList (by rw [remainderD]; omega), byteD, remainderD]
    exact maskByte_eq _ _ (by omega)
  · intro index before
    rw [load_eq_of_mem_eq eMemory]
    have fit := owned.fitting
    have full := full_le_size kind owned.expected
    have unchanged := saved_output_read aInput aWork.stack index (by omega)
    have initial := load_eq_of_mem_eq (indexed_memory s)
    have same := unchanged.trans (congrFun (congrFun initial (args.output.toNat + index)) 1)
    simpa only [widthLoad, b, byteLoaded, state_simp_rules] using same
  · intro reg untouched
    have not8 : reg ≠ 8#5 := by simp_all
    have not9 : reg ≠ 9#5 := by simp_all
    rw [maskResult_register path.maskStage d reg untouched,
      maskResult_register path.remainderStage c reg untouched, tailGuarded_register,
      byteLoaded_register a reg not8, indexed_register s reg not9]
  · intro reg
    simp [e, d, c, b, a]

end SszArm.Emit.Bits
