import SszArm.NatMulExec
import SszArm.UintResultMemory

namespace SszArm.NatMul

def saveMemory (s : ArmState) : ArmState :=
  let sp := r (.GPR 31#5) s - 96#64
  write_mem_bytes 16 (sp + 80#64) (r (.GPR 19#5) s ++ r (.GPR 20#5) s)
    (write_mem_bytes 16 (sp + 64#64) (r (.GPR 21#5) s ++ r (.GPR 22#5) s)
      (write_mem_bytes 16 (sp + 48#64) (r (.GPR 23#5) s ++ r (.GPR 24#5) s)
        (write_mem_bytes 16 (sp + 32#64) (r (.GPR 25#5) s ++ r (.GPR 26#5) s)
          (write_mem_bytes 16 (sp + 16#64) (r (.GPR 27#5) s ++ r (.GPR 28#5) s)
            (write_mem_bytes 8 sp (r (.GPR 30#5) s) s)))))

def saveMemoryWords (s : ArmState) : ArmState :=
  let sp := r (.GPR 31#5) s - 96#64
  write_mem_bytes 8 (sp + 88#64) (r (.GPR 19#5) s) (write_mem_bytes 8 (sp + 80#64) (r (.GPR 20#5) s) (write_mem_bytes 8 (sp + 72#64) (r (.GPR 21#5) s) (write_mem_bytes 8 (sp + 64#64) (r (.GPR 22#5) s) (write_mem_bytes 8 (sp + 56#64) (r (.GPR 23#5) s) (write_mem_bytes 8 (sp + 48#64) (r (.GPR 24#5) s) (write_mem_bytes 8 (sp + 40#64) (r (.GPR 25#5) s) (write_mem_bytes 8 (sp + 32#64) (r (.GPR 26#5) s) (write_mem_bytes 8 (sp + 24#64) (r (.GPR 27#5) s) (write_mem_bytes 8 (sp + 16#64) (r (.GPR 28#5) s) (write_mem_bytes 8 sp (r (.GPR 30#5) s) (s)))))))))))

theorem saveMemory_split (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    saveMemory s = saveMemoryWords s := by
  unfold saveMemory saveMemoryWords
  rw [UintCodec.Tail.write_pair_words _ _ _ _ (by bv_omega),
    UintCodec.Tail.write_pair_words _ _ _ _ (by bv_omega),
    UintCodec.Tail.write_pair_words _ _ _ _ (by bv_omega),
    UintCodec.Tail.write_pair_words _ _ _ _ (by bv_omega),
    UintCodec.Tail.write_pair_words _ _ _ _ (by bv_omega)]
  simp only [BitVec.add_assoc,
    show 80#64 + 8#64 = 88#64 by decide,
    show 64#64 + 8#64 = 72#64 by decide,
    show 48#64 + 8#64 = 56#64 by decide,
    show 32#64 + 8#64 = 40#64 by decide,
    show 16#64 + 8#64 = 24#64 by decide]

theorem saveMemory_read_30 (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + 0#64) (saveMemory s) = r (.GPR 30#5) s := by
  rw [saveMemory_split s stack]
  simp (disch := bv_omega) [saveMemoryWords,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

theorem saveMemory_read_28 (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + 16#64) (saveMemory s) = r (.GPR 28#5) s := by
  rw [saveMemory_split s stack]
  simp (disch := bv_omega) [saveMemoryWords,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

theorem saveMemory_read_27 (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + 24#64) (saveMemory s) = r (.GPR 27#5) s := by
  rw [saveMemory_split s stack]
  simp (disch := bv_omega) [saveMemoryWords,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

theorem saveMemory_read_26 (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + 32#64) (saveMemory s) = r (.GPR 26#5) s := by
  rw [saveMemory_split s stack]
  simp (disch := bv_omega) [saveMemoryWords,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

theorem saveMemory_read_25 (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + 40#64) (saveMemory s) = r (.GPR 25#5) s := by
  rw [saveMemory_split s stack]
  simp (disch := bv_omega) [saveMemoryWords,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

theorem saveMemory_read_24 (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + 48#64) (saveMemory s) = r (.GPR 24#5) s := by
  rw [saveMemory_split s stack]
  simp (disch := bv_omega) [saveMemoryWords,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

theorem saveMemory_read_23 (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + 56#64) (saveMemory s) = r (.GPR 23#5) s := by
  rw [saveMemory_split s stack]
  simp (disch := bv_omega) [saveMemoryWords,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

theorem saveMemory_read_22 (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + 64#64) (saveMemory s) = r (.GPR 22#5) s := by
  rw [saveMemory_split s stack]
  simp (disch := bv_omega) [saveMemoryWords,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

theorem saveMemory_read_21 (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + 72#64) (saveMemory s) = r (.GPR 21#5) s := by
  rw [saveMemory_split s stack]
  simp (disch := bv_omega) [saveMemoryWords,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

theorem saveMemory_read_20 (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + 80#64) (saveMemory s) = r (.GPR 20#5) s := by
  rw [saveMemory_split s stack]
  simp (disch := bv_omega) [saveMemoryWords,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

theorem saveMemory_read_19 (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + 88#64) (saveMemory s) = r (.GPR 19#5) s := by
  rw [saveMemory_split s stack]
  simp (disch := bv_omega) [saveMemoryWords,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

end SszArm.NatMul
