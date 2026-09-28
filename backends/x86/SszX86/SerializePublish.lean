import SszX86.SerializePublishMemory

namespace SszX86.Serialize.Publish
open UintCodec BoolCodec
open Kraken.X64.Parser

/-- Decode only the selected literal row, without simplifying the complete image. -/
macro "publish_decoded " row:num " at " pc:num " encodedWidth " count:num
    " opcodeAST " instructions:term " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member := List.getElem_mem (l := SszX86.Serialize.program) (n := $row)
     (by rw [SszX86.Serialize.program_length]; decide)
   have fetched := SszX86.Serialize.step_at _ _ $hc
     (($pc, $count, $instructions) : Nat × Nat × Program) member
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.Serialize.directives, SszX86.Serialize.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp, ConstExpr.interp,
      RelRegOrMem.interp, BitVec.toAddressSize, MachineData.set, MachineData.setReg,
      Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
      BitVec.drop, BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

macro "publish_step " row:num " using " hc:term : tactic => do
  match row.getNat with
  | 15 => `(tactic| publish_decoded 15 at 47 encodedWidth 4 opcodeAST parse("movl 0x58(%rsp),%ecx") using $hc)
  | 16 => `(tactic| publish_decoded 16 at 51 encodedWidth 5 opcodeAST parse("movq 0x18(%rsp),%rax") using $hc)
  | 17 => `(tactic| publish_decoded 17 at 56 encodedWidth 5 opcodeAST parse("movq 0x20(%rsp),%rdx") using $hc)
  | 18 => `(tactic| publish_decoded 18 at 61 encodedWidth 5 opcodeAST parse("movq %rax,0x8(%rsp)") using $hc)
  | 19 => `(tactic| publish_decoded 19 at 66 encodedWidth 5 opcodeAST parse("movq %rdx,0x10(%rsp)") using $hc)
  | 20 => `(tactic| publish_decoded 20 at 71 encodedWidth 5 opcodeAST parse("movq 0x28(%rsp),%rax") using $hc)
  | 21 => `(tactic| publish_decoded 21 at 76 encodedWidth 5 opcodeAST parse("movq 0x30(%rsp),%r9") using $hc)
  | 22 => `(tactic| publish_decoded 22 at 81 encodedWidth 5 opcodeAST parse("movq 0x38(%rsp),%rdx") using $hc)
  | 23 => `(tactic| publish_decoded 23 at 86 encodedWidth 2 opcodeAST parse("testl %ecx,%ecx") using $hc)
  | 24 => `(tactic| publish_decoded 24 at 88 encodedWidth 2 opcodeAST parse("je serialize_u161") using $hc)
  | 25 => `(tactic| publish_decoded 25 at 90 encodedWidth 5 opcodeAST parse("movq 0x50(%rsp),%rsi") using $hc)
  | 26 => `(tactic| publish_decoded 26 at 95 encodedWidth 4 opcodeAST parse("movq %rsi,0x38(%rbx)") using $hc)
  | 27 => `(tactic| publish_decoded 27 at 99 encodedWidth 5 opcodeAST parse("movq 0x40(%rsp),%rsi") using $hc)
  | 28 => `(tactic| publish_decoded 28 at 104 encodedWidth 5 opcodeAST parse("movq 0x48(%rsp),%rdi") using $hc)
  | 29 => `(tactic| publish_decoded 29 at 109 encodedWidth 4 opcodeAST parse("movq %rdi,0x30(%rbx)") using $hc)
  | 30 => `(tactic| publish_decoded 30 at 113 encodedWidth 4 opcodeAST parse("movq %rsi,0x28(%rbx)") using $hc)
  | 31 => `(tactic| publish_decoded 31 at 117 encodedWidth 4 opcodeAST parse("movl 0x5c(%rsp),%esi") using $hc)
  | 32 => `(tactic| publish_decoded 32 at 121 encodedWidth 5 opcodeAST parse("movq 0x8(%rsp),%rdi") using $hc)
  | 33 => `(tactic| publish_decoded 33 at 126 encodedWidth 5 opcodeAST parse("movq 0x10(%rsp),%r8") using $hc)
  | 34 => `(tactic| publish_decoded 34 at 131 encodedWidth 4 opcodeAST parse("movq %r8,0x8(%rbx)") using $hc)
  | 35 => `(tactic| publish_decoded 35 at 135 encodedWidth 3 opcodeAST parse("movq %rdi,(%rbx)") using $hc)
  | 36 => `(tactic| publish_decoded 36 at 138 encodedWidth 4 opcodeAST parse("movq %rax,0x10(%rbx)") using $hc)
  | 37 => `(tactic| publish_decoded 37 at 142 encodedWidth 4 opcodeAST parse("movq %r9,0x18(%rbx)") using $hc)
  | 38 => `(tactic| publish_decoded 38 at 146 encodedWidth 4 opcodeAST parse("movq %rdx,0x20(%rbx)") using $hc)
  | 39 => `(tactic| publish_decoded 39 at 150 encodedWidth 3 opcodeAST parse("movl %ecx,0x40(%rbx)") using $hc)
  | 40 => `(tactic| publish_decoded 40 at 153 encodedWidth 3 opcodeAST parse("movl %esi,0x44(%rbx)") using $hc)
  | 41 => `(tactic| publish_decoded 41 at 156 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (249)))))] using $hc)
  | 42 => `(tactic| publish_decoded 42 at 161 encodedWidth 5 opcodeAST parse("movq 0x8(%rsp),%rcx") using $hc)
  | 43 => `(tactic| publish_decoded 43 at 166 encodedWidth 5 opcodeAST parse("movq 0x10(%rsp),%rsi") using $hc)
  | 44 => `(tactic| publish_decoded 44 at 171 encodedWidth 5 opcodeAST parse("movq %rcx,0x18(%rsp)") using $hc)
  | 45 => `(tactic| publish_decoded 45 at 176 encodedWidth 5 opcodeAST parse("movq %rsi,0x20(%rsp)") using $hc)
  | 46 => `(tactic| publish_decoded 46 at 181 encodedWidth 5 opcodeAST parse("movq %rax,0x28(%rsp)") using $hc)
  | 47 => `(tactic| publish_decoded 47 at 186 encodedWidth 5 opcodeAST parse("movq %r9,0x30(%rsp)") using $hc)
  | 48 => `(tactic| publish_decoded 48 at 191 encodedWidth 5 opcodeAST parse("movq %rdx,0x38(%rsp)") using $hc)
  | 61 => `(tactic| publish_decoded 61 at 235 encodedWidth 8 opcodeAST parse("movq $0x0,0x38(%rbx)") using $hc)
  | 62 => `(tactic| publish_decoded 62 at 243 encodedWidth 8 opcodeAST parse("movq $0x0,0x30(%rbx)") using $hc)
  | 63 => `(tactic| publish_decoded 63 at 251 encodedWidth 8 opcodeAST parse("movq $0x0,0x28(%rbx)") using $hc)
  | 64 => `(tactic| publish_decoded 64 at 259 encodedWidth 8 opcodeAST parse("movq $0x0,0x20(%rbx)") using $hc)
  | 65 => `(tactic| publish_decoded 65 at 267 encodedWidth 8 opcodeAST parse("movq $0x0,0x18(%rbx)") using $hc)
  | 66 => `(tactic| publish_decoded 66 at 275 encodedWidth 8 opcodeAST parse("movq $0x0,0x10(%rbx)") using $hc)
  | 67 => `(tactic| publish_decoded 67 at 283 encodedWidth 8 opcodeAST parse("movq $0x0,0x8(%rbx)") using $hc)
  | 68 => `(tactic| publish_decoded 68 at 291 encodedWidth 7 opcodeAST parse("movq $0x1,(%rbx)") using $hc)
  | 69 => `(tactic| publish_decoded 69 at 298 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (76)))))] using $hc)
  | 75 => `(tactic| publish_decoded 75 at 313 encodedWidth 7 opcodeAST parse("movq $0x1,(%rbx)") using $hc)
  | 76 => `(tactic| publish_decoded 76 at 320 encodedWidth 8 opcodeAST parse("movq $0x0,0x8(%rbx)") using $hc)
  | 77 => `(tactic| publish_decoded 77 at 328 encodedWidth 8 opcodeAST parse("movq $0x0,0x10(%rbx)") using $hc)
  | 78 => `(tactic| publish_decoded 78 at 336 encodedWidth 8 opcodeAST parse("movq $0x0,0x18(%rbx)") using $hc)
  | 79 => `(tactic| publish_decoded 79 at 344 encodedWidth 8 opcodeAST parse("movq $0x0,0x20(%rbx)") using $hc)
  | 80 => `(tactic| publish_decoded 80 at 352 encodedWidth 8 opcodeAST parse("movq $0x0,0x28(%rbx)") using $hc)
  | 81 => `(tactic| publish_decoded 81 at 360 encodedWidth 8 opcodeAST parse("movq $0x0,0x30(%rbx)") using $hc)
  | 82 => `(tactic| publish_decoded 82 at 368 encodedWidth 8 opcodeAST parse("movq $0x0,0x38(%rbx)") using $hc)
  | 83 => `(tactic| publish_decoded 83 at 376 encodedWidth 7 opcodeAST parse("movl $0x8001,0x40(%rbx)") using $hc)
  | 84 => `(tactic| publish_decoded 84 at 383 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (25)))))] using $hc)
  | _ => Lean.Macro.throwUnsupported

/-- State after the eight reads and two scratch writes at PC47..81. -/
def loaded (s : MachineData) (v : Image) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec v.w2
      rdx := UInt64.ofBitVec v.w4
      r9 := UInt64.ofBitVec v.w3
      rcx := UInt64.ofBitVec (v.tag.setWidth 64)}
    dmem := spillMem s.dmem s.regs.rsp.toBitVec v}

def tested (s : MachineData) (v : Image) (flags : StatusFlags) : MachineData :=
  {loaded s v with status := flags}

/-- PC196: the Nat pair is still in RAX/R9 and all original callee-saved GPRs remain. -/
def prepared (s : MachineData) (v : Image) (flags : StatusFlags) : MachineData :=
  {tested s v flags with
    regs := {(loaded s v).regs with
      rcx := UInt64.ofBitVec v.w0
      rsi := UInt64.ofBitVec v.w1}
    dmem := preparedMem (spillMem s.dmem s.regs.rsp.toBitVec v) s.regs.rsp.toBitVec v}

def copied (s : MachineData) (v : Image) (flags : StatusFlags) : MachineData :=
  {tested s v flags with
    regs := {(loaded s v).regs with
      rsi := UInt64.ofBitVec (v.padding.setWidth 64)
      rdi := UInt64.ofBitVec v.w0
      r8 := UInt64.ofBitVec v.w1}
    dmem := copyMem (spillMem s.dmem s.regs.rsp.toBitVec v) s.regs.rbx.toBitVec v}

def capacityFailed (s : MachineData) : MachineData :=
  {s with dmem := capacityMem s.dmem s.regs.rbx.toBitVec}

def hostFailed (s : MachineData) : MachineData :=
  {s with dmem := hostMem s.dmem s.regs.rbx.toBitVec}

macro "publish_store " row:num " at " off:num " width " count:num
    &"capacity" total:num " using " hc:term:max &"mapped" hm:term:max : tactic => do
  let obtainLoad ← if off.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := $total) (byteCount := $count))
  else
    `(tactic| apply Large.mapped_load (capacity := $total) («offset» := $off) («width» := $count))
  `(tactic|
    (publish_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $obtainLoad
       · have mappingBase := $hm
         repeat' first | apply Large.mapped_store | assumption
       · decide
     simp only [Effects.All]))

macro "publish_read " row:num " using " hc:term " publishWord " hl:term : tactic => `(tactic|
  (publish_step $row using $hc
   simp (disch := first | assumption | omega | decide)
     [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc,
      local_read (extent := 96), remote_read (srcCount := 96) (dstCount := 80),
      ($hl), Delimited.word_cast]))

/-- Only mapped scratch is assumed; its old values are not constrained. -/
theorem loads_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : Image)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 96)
    (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (image : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) v)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (loaded s v, base + 86)) :
    Eventually (step e) P (s, base + 47) := by
  have preserved := spill_plan s.dmem s.regs.rsp.toBitVec v bound image
  have post2 := preserved.w2
  have post3 := preserved.w3
  have post4 := preserved.w4
  simp only [spillMem, BitVec.add_assoc, BitVec.reduceAdd] at post2 post3 post4
  rcases image with ⟨h0,h1,h2,h3,h4,h5,h6,h7,ht,hp⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 ht hp
  publish_read 15 using hc publishWord ht
  publish_read 16 using hc publishWord h0
  publish_read 17 using hc publishWord h1
  publish_store 18 at 8 width 8 capacity 96 using hc mapped stack
  publish_store 19 at 16 width 8 capacity 96 using hc mapped stack
  publish_read 20 using hc publishWord post2
  publish_read 21 using hc publishWord post3
  publish_read 22 using hc publishWord post4
  simpa [loaded, spillMem, BitVec.ofInt_natCast, BitVec.ofNat_toNat] using next

/-- The actual TEST and conditional branch; AF is nondeterministic and dead. -/
theorem branch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : Image) (P : MachineState → Prop)
    (success : v.tag = 0 → ∀ flags,
      Eventually (step e) P (tested s v flags, base + 161))
    (failure : v.tag ≠ 0 → ∀ flags,
      Eventually (step e) P (tested s v flags, base + 90)) :
    Eventually (step e) P (loaded s v, base + 86) := by
  have target := hc.targets ("serialize_u161", 161) (by decide)
  unfold loaded
  publish_step 23 using hc
  constructor <;> publish_step 24 using hc
  all_goals
    simp [StatusFlags.from_result]
    by_cases zero : v.tag = 0#32
    · simpa [tested, loaded, target, zero, Effects.All] using success zero _
    · simpa [tested, loaded, target, zero, Effects.All] using failure zero _

/-- PC161..191 copies all five live Plan words back into the actual Plan. -/
theorem prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : Image) (flags : StatusFlags)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 96)
    (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (prepared s v flags, base + 196)) :
    Eventually (step e) P (tested s v flags, base + 161) := by
  have spills := spill_reads s.dmem s.regs.rsp.toBitVec v bound
  have hmap := spill_mapping s.dmem s.regs.rsp.toBitVec v _ _ stack
  unfold tested loaded
  publish_read 42 using hc publishWord spills.1
  publish_read 43 using hc publishWord spills.2
  publish_store 44 at 24 width 8 capacity 96 using hc mapped hmap
  publish_store 45 at 32 width 8 capacity 96 using hc mapped hmap
  publish_store 46 at 40 width 8 capacity 96 using hc mapped hmap
  publish_store 47 at 48 width 8 capacity 96 using hc mapped hmap
  publish_store 48 at 56 width 8 capacity 96 using hc mapped hmap
  simpa [prepared, tested, loaded, preparedMem] using next

/-- PC90..156 copies all 72 bytes. In particular ESI carries Plan+68, not zero. -/
theorem copy_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : Image) (flags : StatusFlags)
    (result : Large.Mapped s.dmem s.regs.rbx.toBitVec 80)
    (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 96 80)
    (image : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) v)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (copied s v flags, base + 410)) :
    Eventually (step e) P (tested s v flags, base + 90) := by
  have preserved := spill_plan s.dmem s.regs.rsp.toBitVec v bound image
  rcases preserved with ⟨h0,h1,h2,h3,h4,h5,h6,h7,ht,hp⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 ht hp
  have spills := spill_reads s.dmem s.regs.rsp.toBitVec v bound
  have hmap := spill_mapping s.dmem s.regs.rsp.toBitVec v _ _ result
  unfold tested loaded
  publish_read 25 using hc publishWord h7
  publish_store 26 at 56 width 8 capacity 80 using hc mapped hmap
  publish_read 27 using hc publishWord h5
  publish_read 28 using hc publishWord h6
  publish_store 29 at 48 width 8 capacity 80 using hc mapped hmap
  publish_store 30 at 40 width 8 capacity 80 using hc mapped hmap
  publish_read 31 using hc publishWord hp
  publish_read 32 using hc publishWord spills.1
  publish_read 33 using hc publishWord spills.2
  publish_store 34 at 8 width 8 capacity 80 using hc mapped hmap
  publish_store 35 at 0 width 8 capacity 80 using hc mapped hmap
  publish_store 36 at 16 width 8 capacity 80 using hc mapped hmap
  publish_store 37 at 24 width 8 capacity 80 using hc mapped hmap
  publish_store 38 at 32 width 8 capacity 80 using hc mapped hmap
  publish_store 39 at 64 width 4 capacity 80 using hc mapped hmap
  publish_store 40 at 68 width 4 capacity 80 using hc mapped hmap
  publish_step 41 using hc
  simpa [copied, tested, loaded, copyMem, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.setWidth_setWidth_of_le] using next

/-- Full successful preparation from the real measure-return PC47. -/
theorem success_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : Image)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 96)
    (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (image : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) v)
    (zero : v.tag = 0) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (prepared s v flags, base + 196)) :
    Eventually (step e) P (s, base + 47) := by
  apply loads_cps e base hc s v stack bound image P
  apply branch_cps e base hc s v P
  · intro _ flags
    exact prepare_cps e base hc s v flags stack bound P (next flags)
  · intro nonzero
    exact False.elim (nonzero zero)

/-- Full measurement-error publication from PC47 to the epilogue PC410. -/
theorem failure_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : Image)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 96)
    (result : Large.Mapped s.dmem s.regs.rbx.toBitVec 80)
    (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 96 80)
    (image : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) v)
    (nonzero : v.tag ≠ 0) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (copied s v flags, base + 410)) :
    Eventually (step e) P (s, base + 47) := by
  apply loads_cps e base hc s v stack bound image P
  apply branch_cps e base hc s v P
  · intro zero
    exact False.elim (nonzero zero)
  · intro _ flags
    exact copy_cps e base hc s v flags result bound apart image P (next flags)

/-- The PC313 capacity-failure arm and its shared status/jump tail. -/
theorem capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hmap : Large.Mapped s.dmem s.regs.rbx.toBitVec 80)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (capacityFailed s, base + 410)) :
    Eventually (step e) P (s, base + 313) := by
  publish_store 75 at 0 width 8 capacity 80 using hc mapped hmap
  publish_store 76 at 8 width 8 capacity 80 using hc mapped hmap
  publish_store 77 at 16 width 8 capacity 80 using hc mapped hmap
  publish_store 78 at 24 width 8 capacity 80 using hc mapped hmap
  publish_store 79 at 32 width 8 capacity 80 using hc mapped hmap
  publish_store 80 at 40 width 8 capacity 80 using hc mapped hmap
  publish_store 81 at 48 width 8 capacity 80 using hc mapped hmap
  publish_store 82 at 56 width 8 capacity 80 using hc mapped hmap
  publish_store 83 at 64 width 4 capacity 80 using hc mapped hmap
  publish_step 84 using hc
  simpa [capacityFailed, capacityMem] using next

/-- PC235 executes its reverse-order payload, JMP298, and the same status tail. -/
theorem host_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hmap : Large.Mapped s.dmem s.regs.rbx.toBitVec 80)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (hostFailed s, base + 410)) :
    Eventually (step e) P (s, base + 235) := by
  publish_store 61 at 56 width 8 capacity 80 using hc mapped hmap
  publish_store 62 at 48 width 8 capacity 80 using hc mapped hmap
  publish_store 63 at 40 width 8 capacity 80 using hc mapped hmap
  publish_store 64 at 32 width 8 capacity 80 using hc mapped hmap
  publish_store 65 at 24 width 8 capacity 80 using hc mapped hmap
  publish_store 66 at 16 width 8 capacity 80 using hc mapped hmap
  publish_store 67 at 8 width 8 capacity 80 using hc mapped hmap
  publish_store 68 at 0 width 8 capacity 80 using hc mapped hmap
  publish_step 69 using hc
  publish_store 83 at 64 width 4 capacity 80 using hc mapped hmap
  publish_step 84 using hc
  simpa [hostFailed, hostMem] using next

theorem prepared_state_frame (s : MachineData) (v : Image) (flags : StatusFlags) :
    MemoryFrame s.dmem (prepared s v flags).dmem
      (fun a => InSpan a (s.regs.rsp.toBitVec + 8#64) 56) := by
  change MemoryFrame s.dmem
    (preparedMem (spillMem s.dmem s.regs.rsp.toBitVec v) s.regs.rsp.toBitVec v) _
  apply Emit.Bits.frame_trans
  · apply Emit.Bits.frame_mono (spill_frame s.dmem s.regs.rsp.toBitVec v)
    rintro a ⟨i, hi, equal⟩
    exact ⟨i, by omega, equal⟩
  · apply Emit.Bits.frame_mono
      (Publish.prepared_frame (spillMem s.dmem s.regs.rsp.toBitVec v) s.regs.rsp.toBitVec v)
    rintro a ⟨i, hi, equal⟩
    refine ⟨16+i, by omega, ?_⟩
    have shift : 8 + (16+i) = 24+i := by omega
    simpa only [memmove_addr_add, shift] using equal

theorem copied_frame (s : MachineData) (v : Image) (flags : StatusFlags) :
    MemoryFrame s.dmem (copied s v flags).dmem
      (fun a => InSpan a s.regs.rbx.toBitVec 72 ∨ InSpan a (s.regs.rsp.toBitVec + 8#64) 16) := by
  change MemoryFrame s.dmem
    (copyMem (spillMem s.dmem s.regs.rsp.toBitVec v) s.regs.rbx.toBitVec v) _
  apply Emit.Bits.frame_trans
  · exact Emit.Bits.frame_mono (spill_frame s.dmem s.regs.rsp.toBitVec v) (fun _ h => Or.inr h)
  · exact Emit.Bits.frame_mono
      (copy_frame (spillMem s.dmem s.regs.rsp.toBitVec v) s.regs.rbx.toBitVec v)
      (fun _ h => Or.inl h)

end SszX86.Serialize.Publish
