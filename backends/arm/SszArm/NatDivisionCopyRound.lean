import SszArm.NatDivisionCopyMemory
import SszArm.NatCompareOrder

namespace SszArm.NatDivision

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def copyGuardOps : List Op := [.p452, .p456]
def copyTailOps : List Op := [.p440, .p444, .p448]

def copyRoundResult (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base copyTailOps
    (copyStoreResult
      (Op.p404.effect base (scanLoadResult (block base copyGuardOps s) base .copy word)) base)

/-- A valid physical index always takes the real load/store path; the native
zero-fill arm at pc460 is not entered. -/
theorem copy_round_run (s : ArmState) (base pointer destination : BitVec 64)
    (words : List (BitVec 64)) (count i : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 452#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 i)
    (h24 : r (.GPR 24#5) s = destination)
    (hi : i < count) (hn : count ≤ words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words)
    (hd : CopyDestination s destination count) :
    run 22 s = copyRoundResult s base (words[i]?.getD 0#64) := by
  have hbound : words.length < 2^64 := by have := hs.2.1; omega
  have hcarry : (AddWithCarry (BitVec.ofNat 64 i)
      (~~~BitVec.ofNat 64 words.length) 1#1).2.c ≠ 1#1 := by
    intro carry
    have ordered := (Udivti3.cmp_carry _ _).mp carry
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound,
      Nat.mod_eq_of_lt (show i < 2^64 by omega)] at ordered
    omega
  let g := block base copyGuardOps s
  have hpc : r .PC s = base + 452#64 := hp
  have hfg : Follows base copyGuardOps s := by
    simp [copyGuardOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, BitVec.add_assoc]
  have hg : run 2 s = g := block_run base copyGuardOps s hc he ha hfg
  have hgc : CodeAt g base := by simpa [g, CodeAt] using hc
  have hge : read_err g = .None := (block_error base copyGuardOps s).trans he
  have hga : CheckSPAlignment g := block_aligned base copyGuardOps s ha
  have hgp : read_pc g = base + 372#64 := by
    simp [g, copyGuardOps, block, Op.effect, put, next, state_simp_rules, h9, h2, hcarry]
  have hgs : NatCompare.Source g pointer words := by
    simpa [NatCompare.Source, ByteView.Source, g, copyGuardOps, block, Op.effect,
      put, next, state_simp_rules] using hs
  have hgm : NatCompare.Words g pointer words := by
    simpa [NatCompare.Words, WidthWords, g, copyGuardOps, block, Op.effect,
      put, next, state_simp_rules] using hm
  have hload : read_mem_bytes 8 (ScanLoad.copy.address g)
      (NatCompare.saved g 11#5) = words[i]?.getD 0#64 := by
    have hadd : ScanLoad.copy.address g = pointer + (BitVec.ofNat 64 i <<< 3) := by
      simp [g, ScanLoad.address, copyGuardOps, block, Op.effect, put, next,
        state_simp_rules, h1, h9]
    rw [hadd]
    exact NatCompare.limb_load g pointer words i 11#5 (by omega) hgs hgm
  let l := scanLoadResult g base .copy (words[i]?.getD 0#64)
  have hl : run 8 g = l := scan_load_run g base _ .copy hgc hge hga hgp hgs.1 hload
  have hlf : ScanFrame g l := scan_load_frame g base _ .copy hgs.1
  have hlp : read_pc l = base + 404#64 := by
    simp [l, scanLoadResult, ScanLoad.start, ScanLoad.size, state_simp_rules]
  let a := Op.p404.effect base l
  have hai : run 1 l = a := by
    change stepi l = a
    exact step l base .p404 (hlf.code hgc) hlp (hlf.error.trans hge) (hlf.aligned hga)
  have hac : CodeAt a base := by simpa [a, CodeAt] using hlf.code hgc
  have hae : read_err a = .None := (Op.error .p404 base l).trans (hlf.error.trans hge)
  have haa : CheckSPAlignment a := Op.aligned .p404 base l (hlf.aligned hga)
  have hap : read_pc a = base + 408#64 := by
    have hlpc : r .PC l = base + 404#64 := hlp
    simp [a, Op.effect, put, next, state_simp_rules, hlpc, BitVec.add_assoc]
  have hasp : r (.GPR 31#5) a = r (.GPR 31#5) s := by
    simp [a, l, g, scanLoadResult, copyGuardOps, block, Op.effect, put, next,
      NatCompare.saved, state_simp_rules]
  have haaddr : r (.GPR 24#5) a + (r (.GPR 9#5) a <<< 3) =
      destination + BitVec.ofNat 64 (8 * i) := by
    simp [a, l, g, scanLoadResult, copyGuardOps, block, Op.effect, put, next,
      NatCompare.saved, state_simp_rules, h24, h9]
    bv_omega
  have hdaddr : (destination + BitVec.ofNat 64 (8 * i)).toNat = destination.toNat + 8 * i := by
    have := hd.1
    bv_omega
  have hstore := copy_store_run a base hac hae haa hap (by rw [hasp]; exact hs.1)
    (by rw [haaddr, hdaddr]; have := hd.1; omega)
    (by rw [haaddr, hdaddr, hasp]; have := hd.2; omega)
  let v := copyStoreResult a base
  change run 8 a = v at hstore
  have hvc : CodeAt v base := by simpa [v, copyStoreResult, NatCompare.saved, CodeAt, state_simp_rules] using hac
  have hve : read_err v = .None := by simpa [v, copyStoreResult, NatCompare.saved, state_simp_rules] using hae
  have hva : CheckSPAlignment v := by
    simpa [v, copyStoreResult, NatCompare.saved, CheckSPAlignment, state_simp_rules] using haa
  have hft : Follows base copyTailOps v := by
    simp [v, copyStoreResult, copyTailOps, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, BitVec.add_assoc]
  have ht : run 3 v = block base copyTailOps v := block_run base copyTailOps v hvc hve hva hft
  rw [show 22 = 2 + 8 + 1 + 8 + 3 by decide, run_plus, run_plus, run_plus, run_plus,
    hg, hl, hai, hstore, ht]
  rfl

/-- Exact three stores in a forward round: two lowering saves followed by the
single destination word. No zero-fill or extra destination word is executed. -/
def copyRoundMemory (s : ArmState) (destination : BitVec 64) (i : Nat)
    (word : BitVec 64) : ArmState :=
  write_mem_bytes 8 (destination + BitVec.ofNat 64 (8 * i)) word
    (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (BitVec.ofNat 64 (i + 1))
      (NatCompare.saved s 11#5))

theorem copy_round_memory (s : ArmState) (base destination word : BitVec 64) (i : Nat)
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 i)
    (h24 : r (.GPR 24#5) s = destination) :
    (copyRoundResult s base word).mem = (copyRoundMemory s destination i word).mem := by
  have hshift : BitVec.ofNat 64 i <<< 3 = BitVec.ofNat 64 (8 * i) := by bv_omega
  simp [copyRoundResult, copyStoreResult, copyTailOps, copyGuardOps,
    scanLoadResult, copyRoundMemory, block, Op.effect, put, next,
    NatCompare.saved, state_simp_rules, NatCompare.spill_mem_w,
    h9, h24, hshift, BitVec.ofNat_add]
  apply mem_write_mem_bytes_of_mem_eq
  apply mem_write_mem_bytes_of_mem_eq
  simp [state_simp_rules, NatCompare.spill_mem_w]

theorem copy_round_registers (s : ArmState) (base word : BitVec 64) (i count : Nat)
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 i)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 count)
    (hi : i < count) (hb : count < 2^64) :
    r (.GPR 9#5) (copyRoundResult s base word) = BitVec.ofNat 64 (i + 1) ∧
    r (.GPR 1#5) (copyRoundResult s base word) = r (.GPR 1#5) s ∧
    read_pc (copyRoundResult s base word) =
      if i + 1 = count then base + 520#64 else base + 452#64 := by
  have heq : BitVec.ofNat 64 count = BitVec.ofNat 64 i + 1#64 ↔ i + 1 = count := by bv_omega
  simp [copyRoundResult, copyStoreResult, copyTailOps, copyGuardOps,
    scanLoadResult, block, Op.effect, put, next, NatCompare.saved,
    state_simp_rules, h9, h8, Udivti3.cmp_zero, heq, BitVec.ofNat_add]

end SszArm.NatDivision
