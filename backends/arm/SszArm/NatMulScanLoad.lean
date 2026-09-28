import SszArm.NatMulScanLoadState

namespace SszArm.NatMul

inductive ScanLoad where
  | left | right
  deriving DecidableEq

def ScanLoad.start : ScanLoad → Nat
  | .left => 48 | .right => 176

def ScanLoad.size : ScanLoad → Nat
  | .left => 8 | .right => 7

def ScanLoad.tmp : ScanLoad → BitVec 5
  | .left => 10#5 | .right => 11#5

def ScanLoad.dst : ScanLoad → BitVec 5
  | .left => 11#5 | .right => 10#5

def ScanLoad.ops : ScanLoad → List Op
  | .left => [.p48, .p52, .p56, .p60, .p64, .p68, .p72, .p76]
  | .right => [.p176, .p180, .p184, .p188, .p192, .p196, .p200]

def ScanLoad.address (kind : ScanLoad) (s : ArmState) : BitVec 64 :=
  match kind with
  | .left => r (.GPR 8#5) s + (r (.GPR 9#5) s <<< 3)
  | .right => r (.GPR 9#5) s - 8#64

def scanLoadResult (s : ArmState) (base : BitVec 64) (kind : ScanLoad)
    (word : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (kind.start + 4 * kind.size))
    (w (.GPR kind.dst) word (NatCompare.saved s kind.tmp))

/-- Execution includes every lowered save, address computation and restore.
The current-memory hypothesis is discharged from physical ownership by rounds. -/
theorem scan_load_run (s : ArmState) (base word : BitVec 64) (kind : ScanLoad)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hload : read_mem_bytes 8 (kind.address s) (NatCompare.saved s kind.tmp) = word) :
    run kind.size s = scanLoadResult s base kind word := by
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s kind.tmp) = r (.GPR kind.tmp) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.start := hp
  have hf : Follows base kind.ops s := by
    cases kind <;> simp [ScanLoad.ops, ScanLoad.start, Follows, Op.row,
      Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  rw [show kind.size = kind.ops.length by cases kind <;> rfl,
    block_run base kind.ops s hc he ha hf]
  cases kind with
  | left =>
    change NatAdd.indexedReadSequence s 8#5 9#5 10#5 11#5 = _
    have semantics := NatAdd.indexedReadSequence_eq s 8#5 9#5 10#5 11#5 word
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hload hrestore
    simpa only [scanLoadResult, ScanLoad.start, ScanLoad.size, ScanLoad.dst,
      ScanLoad.tmp, hp, BitVec.add_assoc,
      show (48#64 + 32#64) = BitVec.ofNat 64 (48 + 4 * 8) by decide] using semantics
  | right =>
    change offsetReadSequence s 9#5 11#5 10#5 8#64 = _
    have semantics := offsetReadSequence_eq s 9#5 11#5 10#5 8#64 word
      (by decide) (by decide) (by decide) (by decide) (by decide) hload hrestore
    simpa only [scanLoadResult, ScanLoad.start, ScanLoad.size, ScanLoad.dst,
      ScanLoad.tmp, hp, BitVec.add_assoc,
      show (176#64 + 28#64) = BitVec.ofNat 64 (176 + 4 * 7) by decide] using semantics

theorem scan_load_frame (s : ArmState) (base word : BitVec 64) (kind : ScanLoad)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    ScanFrame s (scanLoadResult s base kind word) := by
  have hf := NatCompare.saved_frame s kind.tmp hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [scanLoadResult, state_simp_rules] using hf.program
  · simpa [scanLoadResult, state_simp_rules] using hf.error
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    cases kind <;> simp (disch := simp_all)
      [scanLoadResult, ScanLoad.dst, NatCompare.saved, state_simp_rules]
  · intro reg; simpa [scanLoadResult, state_simp_rules] using hf.vectors reg
  · intro a ha; simpa [scanLoadResult, state_simp_rules] using hf.memory a ha

end SszArm.NatMul
