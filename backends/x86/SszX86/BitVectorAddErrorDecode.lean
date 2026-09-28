import SszX86.BitVectorDecode
import SszX86.BitVectorPadding

namespace SszX86.BitVector
open Kraken.X64.Parser

/-- Concrete selected rows only; the decoded-step macro kernel-checks membership. -/
macro "bitvector_remaining_step " row:num " using " hc:term : tactic => do
  if row.getNat == 85 then
    return ← `(tactic| bitvector_decoded_step 85 at 1942 size 5 code
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 5773))))] using $hc)
  if row.getNat == 142 then
    return ← `(tactic| bitvector_decoded_step 142 at 4827 size 5 code
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 2888))))] using $hc)
  let entries : List (Nat × Nat × Nat × String) := [
    (55, 1776, 5, "movq 0x48(%rsp),%rcx"),
    (56, 1781, 8, "movq %rcx,0xb0(%rsp)"),
    (57, 1789, 5, "movq 0x40(%rsp),%rcx"),
    (58, 1794, 8, "movq %rcx,0xa8(%rsp)"),
    (59, 1802, 5, "movq 0x38(%rsp),%rdx"),
    (60, 1807, 8, "movq %rdx,0xa0(%rsp)"),
    (61, 1815, 5, "movq 0x30(%rsp),%rsi"),
    (62, 1820, 8, "movq %rsi,0x98(%rsp)"),
    (63, 1828, 5, "movq 0x28(%rsp),%rdi"),
    (64, 1833, 8, "movq %rdi,0x90(%rsp)"),
    (65, 1841, 5, "movq 0x20(%rsp),%r8"),
    (66, 1846, 8, "movq %r8,0x88(%rsp)"),
    (67, 1854, 5, "movq 0x10(%rsp),%r9"),
    (68, 1859, 5, "movq 0x18(%rsp),%r10"),
    (69, 1864, 8, "movq %r10,0x80(%rsp)"),
    (70, 1872, 5, "movq %r9,0x78(%rsp)"),
    (71, 1877, 5, "movl 0x54(%rsp),%r11d"),
    (72, 1882, 8, "movq 0xb0(%rsp),%rbx"),
    (73, 1890, 5, "movq 0x8(%rsp),%r14"),
    (74, 1895, 4, "movq %rbx,0x40(%r14)"),
    (75, 1899, 4, "movq %rcx,0x38(%r14)"),
    (76, 1903, 4, "movq %rdx,0x30(%r14)"),
    (77, 1907, 4, "movq %rsi,0x28(%r14)"),
    (78, 1911, 4, "movq %rdi,0x20(%r14)"),
    (79, 1915, 4, "movq %r8,0x18(%r14)"),
    (80, 1919, 4, "movq %r10,0x10(%r14)"),
    (81, 1923, 4, "movq %r9,0x8(%r14)"),
    (82, 1927, 4, "movl %eax,0x48(%r14)"),
    (83, 1931, 4, "movl %r11d,0x4c(%r14)"),
    (84, 1935, 7, "movq $0x1,(%r14)"),
    (96, 4650, 5, "movq 0x8(%rsp),%rax"),
    (97, 4655, 4, "leaq 0x8(%rax),%rdi"),
    (98, 4659, 5, "leaq 0x10(%rsp),%rsi"),
    (99, 4664, 5, "movl $0x9,%ecx"),
    (100, 4669, 5, "leaq -0x8(%rsp),%rsp"),
    (101, 4674, 4, "movq %r11,(%rsp)"),
    (102, 4678, 3, "movq (%rsi),%r11"),
    (103, 4681, 3, "movq %r11,(%rdi)"),
    (104, 4684, 4, "leaq 0x8(%rsi),%rsi"),
    (105, 4688, 4, "leaq 0x8(%rdi),%rdi"),
    (106, 4692, 3, "movq (%rsi),%r11"),
    (107, 4695, 3, "movq %r11,(%rdi)"),
    (108, 4698, 4, "leaq 0x8(%rsi),%rsi"),
    (109, 4702, 4, "leaq 0x8(%rdi),%rdi"),
    (110, 4706, 3, "movq (%rsi),%r11"),
    (111, 4709, 3, "movq %r11,(%rdi)"),
    (112, 4712, 4, "leaq 0x8(%rsi),%rsi"),
    (113, 4716, 4, "leaq 0x8(%rdi),%rdi"),
    (114, 4720, 3, "movq (%rsi),%r11"),
    (115, 4723, 3, "movq %r11,(%rdi)"),
    (116, 4726, 4, "leaq 0x8(%rsi),%rsi"),
    (117, 4730, 4, "leaq 0x8(%rdi),%rdi"),
    (118, 4734, 3, "movq (%rsi),%r11"),
    (119, 4737, 3, "movq %r11,(%rdi)"),
    (120, 4740, 4, "leaq 0x8(%rsi),%rsi"),
    (121, 4744, 4, "leaq 0x8(%rdi),%rdi"),
    (122, 4748, 3, "movq (%rsi),%r11"),
    (123, 4751, 3, "movq %r11,(%rdi)"),
    (124, 4754, 4, "leaq 0x8(%rsi),%rsi"),
    (125, 4758, 4, "leaq 0x8(%rdi),%rdi"),
    (126, 4762, 3, "movq (%rsi),%r11"),
    (127, 4765, 3, "movq %r11,(%rdi)"),
    (128, 4768, 4, "leaq 0x8(%rsi),%rsi"),
    (129, 4772, 4, "leaq 0x8(%rdi),%rdi"),
    (130, 4776, 3, "movq (%rsi),%r11"),
    (131, 4779, 3, "movq %r11,(%rdi)"),
    (132, 4782, 4, "leaq 0x8(%rsi),%rsi"),
    (133, 4786, 4, "leaq 0x8(%rdi),%rdi"),
    (134, 4790, 3, "movq (%rsi),%r11"),
    (135, 4793, 3, "movq %r11,(%rdi)"),
    (136, 4796, 4, "leaq 0x8(%rsi),%rsi"),
    (137, 4800, 4, "leaq 0x8(%rdi),%rdi"),
    (138, 4804, 7, "movq $0x0,%rcx"),
    (139, 4811, 4, "movq (%rsp),%r11"),
    (140, 4815, 5, "leaq 0x8(%rsp),%rsp"),
    (141, 4820, 7, "movq $0x1,(%rax)")]
  let some (_, pc, bytes, assembly) := entries.find? (fun entry => entry.1 == row.getNat)
    | Lean.Macro.throwErrorAt row "not a selected native error row"
  let pc := Lean.Syntax.mkNumLit (toString pc)
  let bytes := Lean.Syntax.mkNumLit (toString bytes)
  let assembly := Lean.Syntax.mkStrLit assembly
  `(tactic| bitvector_decoded_step $row at $pc size $bytes code (parse($assembly)) using $hc)

macro "bitvector_remaining_output " row:num " at " off:num " width " byteCount:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if off.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 80) (byteCount := $byteCount))
  else
    `(tactic| apply UintCodec.Large.mapped_load (capacity := 80)
      («offset» := $off) («width» := $byteCount))
  `(tactic|
    (bitvector_remaining_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply UintCodec.Large.mapped_store
       · decide
     simp only [Effects.All]))

end SszX86.BitVector
