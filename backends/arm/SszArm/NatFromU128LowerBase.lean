import SszArm.NatFromU128Exec
import SszArm.UintResultMemory
import SszArm.DelimitedMemory

namespace SszArm.NatFromU128

open Delimited (Span MemoryFrame)

structure Space (s : ArmState) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  output : (r (.GPR 0#5) s).toNat + 68 ≤ 2^64
  separate : (r (.GPR 0#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat

inductive LowerKind where
  | smallPair | smallStatus | wideStatus | zero48 | zero32 | zero16 | errorPair
  deriving DecidableEq

def LowerKind.ops : LowerKind → List Op
  | .smallPair => [.p4, .p8, .p12, .p16, .p20, .p24, .p28, .p32, .p36, .p40]
  | .smallStatus => [.p44, .p48, .p52, .p56, .p60, .p64, .p68, .p72, .p76, .p80]
  | .wideStatus => [.p176, .p180, .p184, .p188, .p192, .p196, .p200, .p204, .p208, .p212]
  | .zero48 => [.p228, .p232, .p236, .p240, .p244, .p248, .p252, .p256, .p260, .p264, .p268, .p272]
  | .zero32 => [.p276, .p280, .p284, .p288, .p292, .p296, .p300, .p304, .p308, .p312, .p316, .p320]
  | .zero16 => [.p324, .p328, .p332, .p336, .p340, .p344, .p348, .p352, .p356, .p360, .p364, .p368]
  | .errorPair => [.p372, .p376, .p380, .p384, .p388, .p392, .p396, .p400, .p404, .p408]

def LowerKind.entry : LowerKind → Nat
  | .smallPair => 4 | .smallStatus => 44 | .wideStatus => 176
  | .zero48 => 228 | .zero32 => 276 | .zero16 => 324 | .errorPair => 372

def LowerKind.offset : LowerKind → Nat
  | .smallPair | .errorPair => 0
  | .smallStatus | .wideStatus => 64
  | .zero48 => 48 | .zero32 => 32 | .zero16 => 16

def LowerKind.bytes : LowerKind → Nat
  | .smallStatus | .wideStatus => 4
  | _ => 16

def lowerSaved (kind : LowerKind) (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 8#64)
    (r (.GPR (if kind = .errorPair then 11#5 else 10#5)) s)
    (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (r (.GPR (if kind = .errorPair then 10#5 else 9#5)) s) s)

def lowerMemory (kind : LowerKind) (s : ArmState) : ArmState :=
  let address := r (.GPR 0#5) s + BitVec.ofNat 64 kind.offset
  match kind with
  | .smallStatus | .wideStatus => write_mem_bytes 4 address 0#32 (lowerSaved kind s)
  | .smallPair => write_mem_bytes 8 (address + 8#64) (r (.GPR 2#5) s)
      (write_mem_bytes 8 address 0#64 (lowerSaved kind s))
  | .errorPair => write_mem_bytes 8 (address + 8#64) 0#64
      (write_mem_bytes 8 address (r (.GPR 9#5) s) (lowerSaved kind s))
  | _ => write_mem_bytes 8 (address + 8#64) 0#64
      (write_mem_bytes 8 address 0#64 (lowerSaved kind s))

macro "from128_side" : tactic => `(tactic|
  first
  | assumption
  | omega
  | (try simp -implicitDefEqProofs only [bitvec_to_nat] at *
     omega))

def scratchPair (s : ArmState) (sp out first second low high : BitVec 64) : ArmState :=
  write_mem_bytes 8 (out + 8#64) high (write_mem_bytes 8 out low
    (write_mem_bytes 8 (sp - 8#64) second (write_mem_bytes 8 (sp - 16#64) first s)))

theorem scratchPair_reads (s : ArmState) (sp out first second low high : BitVec 64)
    (stack : 16 ≤ sp.toNat) (output : out.toNat + 16 ≤ 2^64)
    (separate : out.toNat + 16 ≤ sp.toNat - 16 ∨ sp.toNat ≤ out.toNat) :
    read_mem_bytes 8 (sp - 8#64) (scratchPair s sp out first second low high) = second ∧
    read_mem_bytes 8 (sp - 16#64) (scratchPair s sp out first second low high) = first := by
  constructor
  · unfold scratchPair
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by bv_omega) (by bv_omega) (by bv_omega)]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by bv_omega) (by omega) (by bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)
  · unfold scratchPair
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by bv_omega) (by bv_omega) (by bv_omega)]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by bv_omega) (by omega) (by bv_omega)]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by bv_omega) (by bv_omega) (by bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)

def scratchStatus (s : ArmState) (sp out first second : BitVec 64) : ArmState :=
  write_mem_bytes 4 out 0#32
    (write_mem_bytes 8 (sp - 8#64) second (write_mem_bytes 8 (sp - 16#64) first s))

theorem scratchStatus_reads (s : ArmState) (sp out first second : BitVec 64)
    (stack : 16 ≤ sp.toNat) (output : out.toNat + 4 ≤ 2^64)
    (separate : out.toNat + 4 ≤ sp.toNat - 16 ∨ sp.toNat ≤ out.toNat) :
    read_mem_bytes 8 (sp - 8#64) (scratchStatus s sp out first second) = second ∧
    read_mem_bytes 8 (sp - 16#64) (scratchStatus s sp out first second) = first := by
  constructor
  · unfold scratchStatus
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 4 _ _ _
      (by bv_omega) output (by bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)
  · unfold scratchStatus
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 4 _ _ _
      (by bv_omega) output (by bv_omega)]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by bv_omega) (by bv_omega) (by bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)

end SszArm.NatFromU128
