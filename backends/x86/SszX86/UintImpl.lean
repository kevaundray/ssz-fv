module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.UintCodec
open Kraken.X64.Parser

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def entry : Nat := 1131
/-- Unbound bounds-panic frontier; body proofs must establish unreachability. -/
def boundsPanic : Nat := 7773

/-- Actual linked instruction offsets, byte widths and ISA directives. -/
def program : List (Nat × Nat × Program) := [
  (45, 4, parse("cmpq $0x1,%r14")),
  (49, 6, parse("jne boolScope")),
  (55, 3, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rax .W32)) (.mem (w := .W8) { base := some (.reg .rdx), idx := none, disp := .int64 (0) })))]),
  (58, 2, parse("testl %eax,%eax")),
  (60, 6, parse("je boolZero")),
  (66, 3, parse("cmpl $0x1,%eax")),
  (69, 6, parse("jne boolBad")),
  (75, 6, parse("movw $0x100,0x10(%rdi)")),
  (81, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (5428)))))]),
  (1131, 4, parse("movq 0x8(%rbp),%rax")),
  (1135, 4, parse("movq 0x10(%rbp),%rcx")),
  (1139, 3, parse("testq %rax,%rax")),
  (1142, 6, parse("je u2462")),
  (1148, 4, parse("leaq 0x1(%rcx),%rsi")),
  (1152, 4, parse("cmpq $0x1,%rsi")),
  (1156, 6, parse("je u2529")),
  (1162, 4, parse("leaq -0x1(%rsi),%r8")),
  (1166, 6, parse("cmpq $0x0,-0x10(%rax,%rsi,8)")),
  (1172, 3, parse("movq %r8,%rsi")),
  (1175, 2, parse("je u1152")),
  (1177, 4, parse("cmpq $0x3,%r8")),
  (1181, 6, parse("jb u2538")),
  (1187, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1659)))))]),
  (1580, 8, parse("movq $0x0,0x40(%rdi)")),
  (1588, 8, parse("movq $0x0,0x38(%rdi)")),
  (1596, 8, parse("movq $0x0,0x18(%rdi)")),
  (1604, 8, parse("movq $0x1,0x20(%rdi)")),
  (1612, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2365)))))]),
  (2462, 2, parse("xorl %esi,%esi")),
  (2464, 3, parse("movq %rcx,%r8")),
  (2467, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (309)))))]),
  (2529, 3, parse("testq %rcx,%rcx")),
  (2532, 6, parse("je u2776")),
  (2538, 3, parse("movq (%rax),%r8")),
  (2541, 4, parse("cmpq $0x2,%rcx")),
  (2545, 2, parse("jb u2659")),
  (2547, 4, parse("movq 0x8(%rax),%rsi")),
  (2551, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (225)))))]),
  (2659, 2, parse("xorl %esi,%esi")),
  (2661, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (118)))))]),
  (2663, 6, parse("movw $0x0,0x10(%rdi)")),
  (2669, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2840)))))]),
  (2674, 8, parse("movq $0x0,0x40(%rdi)")),
  (2682, 8, parse("movq $0x0,0x38(%rdi)")),
  (2690, 8, parse("movq $0x0,0x30(%rdi)")),
  (2698, 8, parse("movq $0x0,0x28(%rdi)")),
  (2706, 8, parse("movq $0x1,0x8(%rdi)")),
  (2714, 8, parse("movq $0x0,0x10(%rdi)")),
  (2722, 8, parse("movq $0x0,0x18(%rdi)")),
  (2730, 4, parse("movq %rax,0x20(%rdi)")),
  (2734, 7, parse("movl $0xd,0x48(%rdi)")),
  (2741, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (4967)))))]),
  (2776, 2, parse("xorl %esi,%esi")),
  (2778, 3, parse("xorl %r8d,%r8d")),
  (2781, 3, parse("xorq %r14,%r8")),
  (2784, 3, parse("orq %rsi,%r8")),
  (2787, 2, parse("jne u2851")),
  (2789, 3, parse("xorl %r8d,%r8d")),
  (2792, 3, parse("movq %r14,%rax")),
  (2795, 3, parse("movq %r14,%r10")),
  (2798, 2, [.instr (.regular .W64 .W64 (.nop 2))]),
  (2800, 4, parse("subq $0x1,%r10")),
  (2804, 6, parse("jb u5499")),
  (2810, 5, parse("cmpb $0x0,-0x1(%rdx,%rax,1)")),
  (2815, 3, parse("movq %r10,%rax")),
  (2818, 2, parse("je u2800")),
  (2820, 4, parse("leaq 0x1(%r10),%rbp")),
  (2824, 4, parse("cmpq $0x9,%rbp")),
  (2828, 2, parse("jae u2896")),
  (2830, 4, parse("cmpq $0x4,%rbp")),
  (2834, 6, parse("jae u5354")),
  (2840, 3, parse("xorl %r8d,%r8d")),
  (2843, 3, parse("xorl %r10d,%r10d")),
  (2846, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2599)))))]),
  (2851, 8, parse("movq $0x0,0x40(%rdi)")),
  (2859, 8, parse("movq $0x0,0x38(%rdi)")),
  (2867, 8, parse("movq $0x1,0x8(%rdi)")),
  (2875, 8, parse("movq $0x0,0x10(%rdi)")),
  (2883, 4, parse("movq %rax,0x18(%rdi)")),
  (2887, 4, parse("movq %rcx,0x20(%rdi)")),
  (2891, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1102)))))]),
  (2896, 4, parse("shrq $0x3,%r10")),
  (2900, 8, [.instr (.regular .W64 .W64 (.lea (.low .rax .W64) { base := none, idx := some ⟨.r10, .W64⟩, disp := .int64 (8) }))]),
  (2908, 3, parse("testq %rax,%rax")),
  (2911, 2, parse("jl u2918")),
  (2913, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2608)))))]),
  (2918, 9, parse("movq $0x0,0x78(%rsp)")),
  (2927, 12, parse("movq $0x0,0x80(%rsp)")),
  (2939, 12, parse("movq $0x0,0x88(%rsp)")),
  (2951, 12, parse("movq $0x0,0x90(%rsp)")),
  (2963, 12, parse("movq $0x0,0x98(%rsp)")),
  (2975, 12, parse("movq $0x0,0xa0(%rsp)")),
  (2987, 8, parse("movq $0x1,0x8(%rdi)")),
  (2995, 8, parse("movq $0x0,0x10(%rdi)")),
  (3003, 5, parse("movq 0x78(%rsp),%rax")),
  (3008, 8, parse("movq 0x80(%rsp),%rcx")),
  (3016, 4, parse("movq %rax,0x18(%rdi)")),
  (3020, 4, parse("movq %rcx,0x20(%rdi)")),
  (3024, 8, parse("movq 0x88(%rsp),%rax")),
  (3032, 4, parse("movq %rax,0x28(%rdi)")),
  (3036, 8, parse("movq 0x90(%rsp),%rax")),
  (3044, 4, parse("movq %rax,0x30(%rdi)")),
  (3048, 8, parse("movq 0x98(%rsp),%rax")),
  (3056, 4, parse("movq %rax,0x38(%rdi)")),
  (3060, 8, parse("movq 0xa0(%rsp),%rax")),
  (3068, 4, parse("movq %rax,0x40(%rdi)")),
  (3072, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (4629)))))]),
  (3982, 8, parse("movq $0x1,0x8(%rdi)")),
  (3990, 8, parse("movq $0x0,0x10(%rdi)")),
  (3998, 8, parse("movq $0x0,0x28(%rdi)")),
  (4006, 4, parse("movq %r14,0x30(%rdi)")),
  (4010, 7, parse("movl $0x3,0x48(%rdi)")),
  (4017, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (3691)))))]),
  (5354, 3, parse("movl %ebp,%r9d")),
  (5357, 4, parse("andl $0xc,%r9d")),
  (5361, 3, parse("xorl %r11d,%r11d")),
  (5364, 3, parse("xorl %r8d,%r8d")),
  (5367, 3, parse("xorl %r10d,%r10d")),
  (5370, 5, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rbx .W32)) (.mem (w := .W8) { base := some (.reg .rdx), idx := some ⟨.r10, .W8⟩, disp := .int64 (0) })))]),
  (5375, 3, parse("movl %r11d,%eax")),
  (5378, 2, parse("andb $0x20,%al")),
  (5380, 2, parse("movl %eax,%ecx")),
  (5382, 3, parse("shlq %cl,%rbx")),
  (5385, 6, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .r14 .W32)) (.mem (w := .W8) { base := some (.reg .rdx), idx := some ⟨.r10, .W8⟩, disp := .int64 (1) })))]),
  (5391, 3, parse("leal 0x8(%rax),%ecx")),
  (5394, 3, parse("shlq %cl,%r14")),
  (5397, 3, parse("orq %r8,%rbx")),
  (5400, 6, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .r15 .W32)) (.mem (w := .W8) { base := some (.reg .rdx), idx := some ⟨.r10, .W8⟩, disp := .int64 (2) })))]),
  (5406, 3, parse("leal 0x10(%rax),%ecx")),
  (5409, 3, parse("shlq %cl,%r15")),
  (5412, 3, parse("orq %r14,%r15")),
  (5415, 3, parse("orq %rbx,%r15")),
  (5418, 6, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .r8 .W32)) (.mem (w := .W8) { base := some (.reg .rdx), idx := some ⟨.r10, .W8⟩, disp := .int64 (3) })))]),
  (5424, 2, parse("orb $0x18,%al")),
  (5426, 2, parse("movl %eax,%ecx")),
  (5428, 3, parse("shlq %cl,%r8")),
  (5431, 4, parse("addq $0x4,%r10")),
  (5435, 3, parse("orq %r15,%r8")),
  (5438, 4, parse("addq $0x20,%r11")),
  (5442, 3, parse("cmpq %r10,%r9")),
  (5445, 2, parse("jne u5370")),
  (5447, 3, parse("addq %r10,%rdx")),
  (5450, 4, parse("testb $0x3,%bpl")),
  (5454, 2, parse("je u5499")),
  (5456, 4, parse("shlq $0x3,%r10")),
  (5460, 3, parse("andl $0x3,%ebp")),
  (5463, 3, parse("xorl %r9d,%r9d")),
  (5466, 2, parse("xorl %eax,%eax")),
  (5468, 5, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .r11 .W32)) (.mem (w := .W8) { base := some (.reg .rdx), idx := some ⟨.rax, .W8⟩, disp := .int64 (0) })))]),
  (5473, 3, parse("movl %r10d,%ecx")),
  (5476, 3, parse("andb $0x38,%cl")),
  (5479, 3, parse("shlq %cl,%r11")),
  (5482, 3, parse("orq %r11,%r8")),
  (5485, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64))))]),
  (5488, 4, parse("addq $0x8,%r10")),
  (5492, 3, parse("cmpq %rax,%rbp")),
  (5495, 2, parse("jne u5468")),
  (5497, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (3)))))]),
  (5499, 3, parse("xorl %r9d,%r9d")),
  (5502, 4, parse("movb $0x1,0x10(%rdi)")),
  (5506, 4, parse("movq %r9,0x18(%rdi)")),
  (5510, 4, parse("movq %r8,0x20(%rdi)")),
  (5514, 7, parse("movq $0x0,(%rdi)")),
  (5521, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2194)))))]),
  (5526, 3, parse("movq (%rbx),%r9")),
  (5529, 4, parse("movq 0x10(%rbx),%r8")),
  (5533, 3, parse("movq %r8,%r11")),
  (5536, 3, parse("addq %r9,%r11")),
  (5539, 6, parse("jb u2918")),
  (5545, 4, parse("cmpq $0xfffffffffffffff8,%r11")),
  (5549, 6, parse("ja u2918")),
  (5555, 4, parse("leaq 0x7(%r11),%rcx")),
  (5559, 4, parse("andq $0xfffffffffffffff8,%rcx")),
  (5563, 3, parse("subq %r11,%rcx")),
  (5566, 3, parse("addq %r8,%rcx")),
  (5569, 6, parse("jb u2918")),
  (5575, 3, parse("addq %rcx,%rax")),
  (5578, 6, parse("jb u2918")),
  (5584, 4, parse("cmpq 0x8(%rbx),%rax")),
  (5588, 6, parse("ja u2918")),
  (5594, 3, parse("movq %r14,%rsi")),
  (5597, 4, parse("leaq 0x1(%r10),%r8")),
  (5601, 4, parse("movq %rax,0x10(%rbx)")),
  (5605, 3, parse("addq %rcx,%r9")),
  (5608, 3, parse("xorl %r11d,%r11d")),
  (5611, 3, parse("movq %rbp,%rbx")),
  (5614, 3, parse("xorl %r14d,%r14d")),
  (5617, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (28)))))]),
  (5619, 3, parse("xorl %r12d,%r12d")),
  (5622, 4, parse("movq %r12,(%r9,%r14,8)")),
  (5626, 4, parse("addq $0xfffffffffffffff8,%rbx")),
  (5630, 4, parse("addq $0x8,%r11")),
  (5634, 3, parse("cmpq %r10,%r14")),
  (5637, 4, parse("leaq 0x1(%r14),%r14")),
  (5641, 6, parse("je u5502")),
  (5647, 4, parse("cmpq $0x8,%rbx")),
  (5651, 6, parse("movl $0x8,%r15d")),
  (5657, 4, [.instr (.regular .W64 .W64 (.cmovcc .c (.low .r15 .W64) (.reg (.low .rbx .W64))))]),
  (5661, 8, [.instr (.regular .W64 .W64 (.lea (.low .rax .W64) { base := none, idx := some ⟨.r14, .W64⟩, disp := .int64 (0) }))]),
  (5669, 3, parse("cmpq %rax,%rbp")),
  (5672, 2, parse("je u5619")),
  (5674, 3, parse("movq %r11,%rax")),
  (5677, 2, parse("xorl %ecx,%ecx")),
  (5679, 3, parse("xorl %r12d,%r12d")),
  (5682, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (5692, 4, [.instr (.regular .W64 .W64 (.nop 4))]),
  (5696, 3, parse("cmpq %rsi,%rax")),
  (5699, 6, parse("jae boundsPanic")),
  (5705, 5, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .r13 .W32)) (.mem (w := .W8) { base := some (.reg .rdx), idx := some ⟨.rax, .W8⟩, disp := .int64 (0) })))]),
  (5710, 3, parse("shlq %cl,%r13")),
  (5713, 3, parse("orq %r13,%r12")),
  (5716, 4, parse("addq $0x8,%rcx")),
  (5720, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64))))]),
  (5723, 3, parse("decq %r15")),
  (5726, 2, parse("jne u5696")),
  (5728, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-108)))))]),
  (7706, 7, parse("movl $0x8000,0x48(%rdi)")),
  (7713, 7, parse("movq $0x1,(%rdi)")),
  (7720, 7, parse("addq $0x138,%rsp")),
  (7727, 1, parse("popq %rbx")),
  (7728, 2, parse("popq %r12")),
  (7730, 2, parse("popq %r13")),
  (7732, 2, parse("popq %r14")),
  (7734, 2, parse("popq %r15")),
  (7736, 1, parse("popq %rbp")),
  (7737, 1, parse("retq "))]

def labels : List (String × Nat) := [
  ("boolScope", 1580),
  ("boolZero", 2663),
  ("boolBad", 2674),
  ("u1152", 1152),
  ("u2462", 2462),
  ("u2529", 2529),
  ("u2538", 2538),
  ("u2659", 2659),
  ("u2776", 2776),
  ("u2800", 2800),
  ("u2851", 2851),
  ("u2896", 2896),
  ("u2918", 2918),
  ("u5354", 5354),
  ("u5370", 5370),
  ("u5468", 5468),
  ("u5499", 5499),
  ("u5502", 5502),
  ("u5619", 5619),
  ("u5696", 5696),
  ("boundsPanic", 7773)]

/-- Parser failures and non-instruction directives are excluded from selected rows. -/
theorem all_instructions : program.all (fun row => match row.2.2 with
    | [.instr _] => true
    | _ => false) = true := by decide

def directives (row : Nat × Nat × Program) : List (Directive × Nat) :=
  ((labels.filter (fun item => item.2 == row.1)).map
    (fun item => (Directive.label item.1, 0))) ++
  row.2.2.map (fun instruction => (instruction, row.2.1))

structure CodeAt (e : Executable) (base : Int64) : Prop where
  fetch : ∀ row ∈ program,
    e.directivesAtAddress (base + Int64.ofNat row.1) = directives row
  targets : ∀ item ∈ labels, e.labels.label item.1 = base + Int64.ofNat item.2

@[instance_reducible]
def layout (e : Executable) : Layout :=
  { start := e.1, size := fun i => (e.2[i]?.map Prod.snd).getD 0 }

abbrev step (e : Executable) := @step1 (layout e) e

theorem step_at (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ program)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  simp only [step, step1, Executable.step, hc.fetch row hr]

theorem bool_codeAt (e : Executable) (base : Int64) (hc : CodeAt e base) :
    SszX86.BoolCodec.CodeAt e base := by
  have hrows : SszX86.BoolCodec.program.all (fun row => program.any (fun candidate =>
      decide (candidate = row ∧ directives candidate = SszX86.BoolCodec.directives row))) = true := by
    decide
  have hlabels : SszX86.BoolCodec.labels.all (fun item => decide (item ∈ labels)) = true := by decide
  constructor
  · intro row hr
    obtain ⟨candidate, hm, heq⟩ := List.any_eq_true.mp (List.all_eq_true.mp hrows row hr)
    obtain ⟨heq, hd⟩ := of_decide_eq_true heq
    subst candidate
    simpa only [hd] using hc.fetch row hm
  · intro item hi
    exact hc.targets item (of_decide_eq_true (List.all_eq_true.mp hlabels item hi))

end SszX86.UintCodec
