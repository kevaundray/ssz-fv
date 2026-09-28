import SszArm.NatMulWordReturnStatus

namespace SszArm.NatMulWord

open NatFromU128 (scratchPair scratchPair_reads store_field_write)

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

theorem pair_enter_effect (kind : PairKind) (s : ArmState) (base : BitVec 64) :
    block base kind.enterOps s = pairEnter s := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases kind <;> cases f <;>
      simp (config := {decide := true, instances := true})
        [PairKind.enterOps, block, Op.effect, put, next, pairEnter,
         state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg, store_field_write]
  · cases kind <;> simp [PairKind.enterOps, block, Op.effect, put, next, pairEnter, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    cases kind <;>
      simp [PairKind.enterOps, block, Op.effect, put, next, pairEnter,
        state_simp_rules, ArmState.mem_w_eq_mem, store_field_write,
        BitVec.add_assoc, BitVec.sub_eq_add_neg]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem pair_store_effect (kind : PairKind) (s : ArmState) (base : BitVec 64) :
    block base kind.storeOps s = pairStore kind s := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases kind <;> cases f <;>
      simp (config := {decide := true, instances := true})
        [PairKind.storeOps, PairKind.low, PairKind.high, block, Op.effect, put, next, pairStore,
         state_simp_rules, BitVec.add_assoc, store_field_write]
  · cases kind <;>
      simp [PairKind.storeOps, block, Op.effect, put, next, pairStore, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    cases kind <;>
      simp [PairKind.storeOps, PairKind.low, PairKind.high, block, Op.effect, put, next, pairStore,
        state_simp_rules, ArmState.mem_w_eq_mem, store_field_write, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem pair_restore_effect (kind : PairKind) (s : ArmState) (base : BitVec 64) :
    block base kind.restoreOps s = pairRestore s := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases kind <;> cases f <;>
      simp (config := {decide := true, instances := true})
        [PairKind.restoreOps, block, Op.effect, put, next, pairRestore,
         state_simp_rules, BitVec.add_assoc]
  · cases kind <;>
      simp [PairKind.restoreOps, block, Op.effect, put, next, pairRestore, state_simp_rules]
  · cases kind <;>
      simp [PairKind.restoreOps, block, Op.effect, put, next, pairRestore, ArmState.mem_w_eq_mem]

theorem pair_finish (kind : PairKind) (s : ArmState) (owned : ReturnOwned s) :
    pairRestore (pairStore kind (pairEnter s)) =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * kind.ops.length))
        (scratchPair s (r (.GPR 31#5) s) (r (.GPR 0#5) s)
          (r (.GPR 9#5) s) (r (.GPR 10#5) s) (kind.low s) (kind.high s)) := by
  obtain ⟨stack, output, separate⟩ := owned
  have reads := scratchPair_reads s (r (.GPR 31#5) s) (r (.GPR 0#5) s)
    (r (.GPR 9#5) s) (r (.GPR 10#5) s) (kind.low s) (kind.high s) stack (by omega) (by omega)
  simp [scratchPair, BitVec.sub_eq_add_neg, BitVec.add_assoc] at reads
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases kind <;> cases f <;>
      simp (config := {decide := true, instances := true})
        [pairRestore, pairStore, pairEnter, scratchPair, PairKind.ops, PairKind.enterOps,
         PairKind.storeOps, PairKind.restoreOps, PairKind.low, PairKind.high,
         state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg, store_field_write] at reads ⊢
    all_goals
      simp (config := {decide := true, instances := true})
        [state_simp_rules, reads.1, reads.2]
    all_goals
      rename_i reg
      by_cases h9 : reg = 9#5
      · subst reg; simp [state_simp_rules]
      · by_cases h10 : reg = 10#5
        · subst reg; simp [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg; simp [state_simp_rules]
          · simp (disch := simp_all) [state_simp_rules]
  · cases kind <;>
      simp [pairRestore, pairStore, pairEnter, scratchPair, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    cases kind <;>
      simp [pairRestore, pairStore, pairEnter, scratchPair, PairKind.low, PairKind.high,
        state_simp_rules, ArmState.mem_w_eq_mem, store_field_write]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem pair_effect (kind : PairKind) (s : ArmState) (base : BitVec 64) (owned : ReturnOwned s) :
    block base kind.ops s =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * kind.ops.length))
        (scratchPair s (r (.GPR 31#5) s) (r (.GPR 0#5) s)
          (r (.GPR 9#5) s) (r (.GPR 10#5) s) (kind.low s) (kind.high s)) := by
  have append (xs ys : List Op) (t : ArmState) :
      block base (xs ++ ys) t = block base ys (block base xs t) := by
    simp only [block, List.foldl_append]
  rw [PairKind.ops, append, append, pair_enter_effect, pair_store_effect, pair_restore_effect]
  exact pair_finish kind s owned

theorem zero_pair_effect (s : ArmState) (base : BitVec 64) (owned : ReturnOwned s) :
    block base zeroPairOps s = w .PC (read_pc s + 44#64) (pairMemory s 0#64) :=
  pair_effect .zero s base owned

theorem small_pair_effect (s : ArmState) (base : BitVec 64) (owned : ReturnOwned s) :
    block base smallPairOps s = w .PC (read_pc s + 40#64) (pairMemory s (r (.GPR 8#5) s)) :=
  pair_effect .small s base owned

end SszArm.NatMulWord
