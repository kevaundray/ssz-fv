import SszArm.NatMulWordReturnStatus
import SszArm.WordNormalize

namespace SszArm.NatMulWord

open NatFromU128 (scratchPair)

inductive PairKind where
  | zero | small | error

def PairKind.enterOps : PairKind → List Op
  | .zero => [.p12, .p16, .p20]
  | .small => [.p1048, .p1052, .p1056]
  | .error => [.p1412, .p1416, .p1420]

def PairKind.storeOps : PairKind → List Op
  | .zero => [.p24, .p28, .p32, .p36, .p40]
  | .small => [.p1060, .p1064, .p1068, .p1072]
  | .error => [.p1424, .p1428, .p1432, .p1436]

def PairKind.restoreOps : PairKind → List Op
  | .zero => [.p44, .p48, .p52]
  | .small => [.p1076, .p1080, .p1084]
  | .error => [.p1440, .p1444, .p1448]

def PairKind.ops (kind : PairKind) : List Op := kind.enterOps ++ kind.storeOps ++ kind.restoreOps

def zeroPairOps : List Op := PairKind.zero.ops

def smallPairOps : List Op := PairKind.small.ops

def PairKind.low (kind : PairKind) (s : ArmState) : BitVec 64 :=
  match kind with | .error => r (.GPR 8#5) s | _ => 0#64

def PairKind.high (kind : PairKind) (s : ArmState) : BitVec 64 :=
  match kind with | .small => r (.GPR 8#5) s | _ => 0#64

def pairMemory (s : ArmState) (word : BitVec 64) : ArmState :=
  scratchPair s (r (.GPR 31#5) s) (r (.GPR 0#5) s)
    (r (.GPR 9#5) s) (r (.GPR 10#5) s) 0#64 word

def pairEnter (s : ArmState) : ArmState :=
  w .PC (read_pc s + 12#64) (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64)
    (write_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (r (.GPR 10#5) s)
      (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s)))

def pairStore (kind : PairKind) (s : ArmState) : ArmState :=
  w .PC (read_pc s + BitVec.ofNat 64 (4 * kind.storeOps.length))
    (w (.GPR 10#5) 0#64 (w (.GPR 9#5) (r (.GPR 0#5) s)
      (write_mem_bytes 8 (r (.GPR 0#5) s + 8#64) (kind.high s)
        (write_mem_bytes 8 (r (.GPR 0#5) s) (kind.low s) s))))

def pairRestore (s : ArmState) : ArmState :=
  w .PC (read_pc s + 12#64) (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64)
    (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s)
      (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s)))

/-- Named current states keep every proof cut to one actual instruction. -/
def pairEnterFirst (s : ArmState) : ArmState :=
  w .PC (read_pc s + 4#64) (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) s)

def pairEnterSecond (s : ArmState) : ArmState :=
  w .PC (read_pc s + 8#64) (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64)
    (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s))

theorem pair_enter_first (s : ArmState) (base : BitVec 64) :
    Op.p12.effect base s = pairEnterFirst s := by
  simp only [Op.effect, put, next, pairEnterFirst]
  arm_state_nf

theorem pair_enter_second (s : ArmState) (base : BitVec 64) :
    Op.p16.effect base (pairEnterFirst s) = pairEnterSecond s := by
  simp only [Op.effect, next, pairEnterFirst, pairEnterSecond]
  arm_state_nf <;> simp [BitVec.add_assoc]

theorem pair_enter_last (s : ArmState) (base : BitVec 64) :
    Op.p20.effect base (pairEnterSecond s) = pairEnter s := by
  simp only [Op.effect, next, pairEnterSecond, pairEnter]
  arm_state_nf <;> simp [BitVec.add_assoc, BitVec.sub_eq_add_neg]

def pairAddress (s : ArmState) : ArmState :=
  w .PC (read_pc s + 4#64) (w (.GPR 9#5) (r (.GPR 0#5) s) s)

def pairZeroSource (s : ArmState) : ArmState :=
  w .PC (read_pc s + 8#64) (w (.GPR 10#5) 0#64 (w (.GPR 9#5) (r (.GPR 0#5) s) s))

def pairLowStored (s : ArmState) (bytes : Nat) (low : BitVec 64) : ArmState :=
  w .PC (read_pc s + BitVec.ofNat 64 bytes)
    (w (.GPR 10#5) 0#64 (w (.GPR 9#5) (r (.GPR 0#5) s)
      (write_mem_bytes 8 (r (.GPR 0#5) s) low s)))

def pairErrorLow (s : ArmState) : ArmState :=
  w .PC (read_pc s + 8#64) (w (.GPR 9#5) (r (.GPR 0#5) s)
    (write_mem_bytes 8 (r (.GPR 0#5) s) (r (.GPR 8#5) s) s))

theorem pair_address (s : ArmState) (base : BitVec 64) :
    Op.p24.effect base s = pairAddress s := by
  simp only [Op.effect, put, next, pairAddress]
  arm_state_nf <;> simp

theorem pair_zero_source (s : ArmState) (base : BitVec 64) :
    Op.p28.effect base (pairAddress s) = pairZeroSource s := by
  simp only [Op.effect, put, next, pairAddress, pairZeroSource]
  arm_state_nf <;> simp [BitVec.add_assoc]

theorem pair_low_stored (s : ArmState) (base : BitVec 64) :
    Op.p32.effect base (pairZeroSource s) = pairLowStored s 12 0#64 := by
  simp only [Op.effect, next, pairZeroSource, pairLowStored]
  arm_state_nf <;> simp [BitVec.add_assoc]

theorem pair_zero_ready (s : ArmState) (base : BitVec 64) :
    Op.p36.effect base (pairLowStored s 12 0#64) = pairLowStored s 16 0#64 := by
  simp only [Op.effect, put, next, pairLowStored]
  arm_state_nf <;> simp [BitVec.add_assoc]

theorem pair_zero_last (s : ArmState) (base : BitVec 64) :
    Op.p40.effect base (pairLowStored s 16 0#64) = pairStore .zero s := by
  simp only [Op.effect, next, pairLowStored, pairStore,
    PairKind.storeOps, PairKind.low, PairKind.high, List.length_cons, List.length_nil]
  arm_state_nf <;> simp [BitVec.add_assoc]

theorem pair_small_last (s : ArmState) (base : BitVec 64) :
    Op.p1072.effect base (pairLowStored s 12 0#64) = pairStore .small s := by
  simp only [Op.effect, next, pairLowStored, pairStore,
    PairKind.storeOps, PairKind.low, PairKind.high, List.length_cons, List.length_nil]
  arm_state_nf <;> simp [BitVec.add_assoc]

theorem pair_error_low (s : ArmState) (base : BitVec 64) :
    Op.p1428.effect base (pairAddress s) = pairErrorLow s := by
  simp only [Op.effect, next, pairAddress, pairErrorLow]
  arm_state_nf <;> simp [BitVec.add_assoc]

theorem pair_error_ready (s : ArmState) (base : BitVec 64) :
    Op.p1432.effect base (pairErrorLow s) = pairLowStored s 12 (r (.GPR 8#5) s) := by
  simp only [Op.effect, put, next, pairErrorLow, pairLowStored]
  arm_state_nf <;> simp [BitVec.add_assoc]

theorem pair_error_last (s : ArmState) (base : BitVec 64) :
    Op.p1436.effect base (pairLowStored s 12 (r (.GPR 8#5) s)) = pairStore .error s := by
  simp only [Op.effect, next, pairLowStored, pairStore,
    PairKind.storeOps, PairKind.low, PairKind.high, List.length_cons, List.length_nil]
  arm_state_nf <;> simp [BitVec.add_assoc]

def pairRestoreFirst (s : ArmState) : ArmState :=
  w .PC (read_pc s + 4#64)
    (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s)

def pairRestoreSecond (s : ArmState) : ArmState :=
  w .PC (read_pc s + 8#64)
    (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s)
      (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s))

theorem pair_restore_first (s : ArmState) (base : BitVec 64) :
    Op.p44.effect base s = pairRestoreFirst s := by
  simp only [Op.effect, put, next, pairRestoreFirst]
  arm_state_nf

theorem pair_restore_second (s : ArmState) (base : BitVec 64) :
    Op.p48.effect base (pairRestoreFirst s) = pairRestoreSecond s := by
  simp only [Op.effect, put, next, pairRestoreFirst, pairRestoreSecond]
  arm_state_nf <;> simp [BitVec.add_assoc]

theorem pair_restore_last (s : ArmState) (base : BitVec 64) :
    Op.p52.effect base (pairRestoreSecond s) = pairRestore s := by
  simp only [Op.effect, put, next, pairRestoreSecond, pairRestore]
  arm_state_nf <;> simp [BitVec.add_assoc]

theorem pair_enter_effect (kind : PairKind) (s : ArmState) (base : BitVec 64) :
    block base kind.enterOps s = pairEnter s := by
  have first : Op.effect base .p1048 = Op.effect base .p12 := by funext t; rfl
  have second : Op.effect base .p1052 = Op.effect base .p16 := by funext t; rfl
  have third : Op.effect base .p1056 = Op.effect base .p20 := by funext t; rfl
  have ef : Op.effect base .p1412 = Op.effect base .p12 := by funext t; rfl
  have es : Op.effect base .p1416 = Op.effect base .p16 := by funext t; rfl
  have et : Op.effect base .p1420 = Op.effect base .p20 := by funext t; rfl
  cases kind <;>
    simp only [PairKind.enterOps, block, List.foldl_cons, List.foldl_nil,
      first, second, third, ef, es, et, pair_enter_first, pair_enter_second, pair_enter_last]

theorem pair_store_effect (kind : PairKind) (s : ArmState) (base : BitVec 64) :
    block base kind.storeOps s = pairStore kind s := by
  have first : Op.effect base .p1060 = Op.effect base .p24 := by funext t; rfl
  have second : Op.effect base .p1064 = Op.effect base .p28 := by funext t; rfl
  have third : Op.effect base .p1068 = Op.effect base .p32 := by funext t; rfl
  have ef : Op.effect base .p1424 = Op.effect base .p24 := by funext t; rfl
  cases kind <;>
    simp only [PairKind.storeOps, block, List.foldl_cons, List.foldl_nil,
      first, second, third, ef, pair_address, pair_zero_source, pair_low_stored,
      pair_zero_ready, pair_zero_last, pair_small_last, pair_error_low, pair_error_ready, pair_error_last]

theorem pair_restore_effect (kind : PairKind) (s : ArmState) (base : BitVec 64) :
    block base kind.restoreOps s = pairRestore s := by
  have first : Op.effect base .p1076 = Op.effect base .p44 := by funext t; rfl
  have second : Op.effect base .p1080 = Op.effect base .p48 := by funext t; rfl
  have third : Op.effect base .p1084 = Op.effect base .p52 := by funext t; rfl
  have ef : Op.effect base .p1440 = Op.effect base .p44 := by funext t; rfl
  have es : Op.effect base .p1444 = Op.effect base .p48 := by funext t; rfl
  have et : Op.effect base .p1448 = Op.effect base .p52 := by funext t; rfl
  cases kind <;>
    simp only [PairKind.restoreOps, block, List.foldl_cons, List.foldl_nil,
      first, second, third, ef, es, et, pair_restore_first, pair_restore_second, pair_restore_last]

end SszArm.NatMulWord
