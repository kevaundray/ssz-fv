#!/usr/bin/env python3
"""Exercise DIV results, register/stack frames and real #DE boundaries on x86-64.

Original and lowered instructions are separate CPU oracles. Undefined DIV flags
and precise fault context are deliberately not compared. Generated files are
confined to a temporary directory; this is execution evidence, not an ISA proof.
"""
from pathlib import Path
import subprocess
import tempfile

from lower_x86 import lower


def main():
    cases = []
    for width, suffix, reg in ((16, "w", "%r9w"), (32, "l", "%r9d"), (64, "q", "%r9")):
        accumulator = {16: "%ax", 32: "%eax", 64: "%rax"}[width]
        for operand, mode in ((reg, 0), (accumulator, 1), ("8(%rsp)", 2)):
            cases.append((f"div{suffix} {operand}", width, mode))
    cases.append(("divq %rsp", 64, 3))
    assembly = [".text"]
    declarations, rows = [], []
    for i, (instruction, width, mode) in enumerate(cases):
        for variant in ("original", "lowered"):
            name = f"{variant}_{i}"
            declarations.append(f"extern void {name}(uint64_t,uint64_t,uint64_t,uint64_t*);")
            body = f"\t{instruction}\n"
            if variant == "lowered":
                # One invocation per function is safe: each local label is scoped
                # with a unique prefix before concatenating the assembler input.
                body = lower(body).replace(".Lssz_x86_lower_", f".Lcase_{i}_")
            assembly.append(f""".global {name}
{name}:
 pushq %rbx
 subq $16,%rsp
 movq %rcx,%rbx
 movq %rdx,8(%rsp)
 movq %rdx,%r9
 movq %rdi,%rax
 movq %rsi,%rdx
 movabsq $0x8123456789abcdef,%r8
 movabsq $0x923456789abcdef0,%r10
 movabsq $0xa3456789abcdef01,%r11
 movabsq $0xb456789abcdef012,%rcx
 btq $0,%rdi
{body}
 movq %rax,0(%rbx)
 movq %rdx,8(%rbx)
 movq %rdi,16(%rbx)
 movq %rsi,24(%rbx)
 movq %rcx,32(%rbx)
 movq %r8,40(%rbx)
 movq %r9,48(%rbx)
 movq %r10,56(%rbx)
 movq %r11,64(%rbx)
 movq %rsp,72(%rbx)
 movq 8(%rsp),%rax
 movq %rax,80(%rbx)
 addq $16,%rsp
 popq %rbx
 ret
""")
        rows.append(f'{{"{instruction}",{width},{mode},{{original_{i},lowered_{i}}}}}')
    assembly.append('.section .note.GNU-stack,"",@progbits')
    source = """#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <signal.h>
#include <setjmp.h>
#include <stdlib.h>
""" + "\n".join(declarations) + """
typedef void (*Fn)(uint64_t,uint64_t,uint64_t,uint64_t*);
static struct { const char *name; unsigned width,mode; Fn fn[2]; } cases[]={
""" + ",\n".join(rows) + """
};
static sigjmp_buf recovery;
static void arithmetic_fault(int signal) { siglongjmp(recovery,signal); }
static uint64_t state=UINT64_C(0x67b9de05810423af);
static uint64_t random_word(void) { state^=state<<13;state^=state>>7;state^=state<<17;return state; }
static uint64_t output[2][11];
static const uint64_t edges[]={0,1,2,3,0x7fff,0xffff,0x10000,0x7fffffff,
  0xffffffff,UINT64_C(0x8000000000000000),UINT64_MAX};
int main(void) {
 struct sigaction action={0}; action.sa_handler=arithmetic_fault;
 sigemptyset(&action.sa_mask); if(sigaction(SIGFPE,&action,0)) return 2;
 unsigned executions=0,faults=0;
 for(unsigned c=0;c<sizeof(cases)/sizeof(cases[0]);c++) {
  unsigned width=cases[c].width;
  uint64_t mask=width==64?UINT64_MAX:(UINT64_C(1)<<width)-1;
  for(unsigned sample=0;sample<1011;sample++) {
   uint64_t lo=sample<11?edges[sample]:random_word();
   uint64_t divisor=(sample<11?edges[10-sample]:random_word())&mask;
   if(!divisor) divisor=1;
   if(cases[c].mode==1) { if(!(lo&mask)) lo|=1;divisor=lo&mask; }
   uint64_t hi=random_word();
   hi=(hi&~mask)|((hi&mask)%divisor);
   if(cases[c].mode==3) hi=0;
   for(unsigned variant=0;variant<2;variant++)
    cases[c].fn[variant](lo,hi,divisor,output[variant]);
   for(unsigned word=0;word<11;word++) if(output[0][word]!=output[1][word]) {
    fprintf(stderr,"%s sample %u word %u: %llx != %llx\\n",cases[c].name,sample,word,
      (unsigned long long)output[0][word],(unsigned long long)output[1][word]);return 1;
   }
   executions++;
  }
  for(unsigned kind=0;kind<2;kind++) {
   if(cases[c].mode==3 && kind==0) continue; /* SP itself cannot be zero here. */
   for(unsigned variant=0;variant<2;variant++) {
    uint64_t lo=kind?7:0,divisor=kind?3:0,hi=kind?3:0;
    if(cases[c].mode==1) hi=lo;
    if(cases[c].mode==3) hi=UINT64_MAX;
    int signal=sigsetjmp(recovery,1);
    if(!signal) {
     cases[c].fn[variant](lo,hi,divisor,output[variant]);
     fprintf(stderr,"%s failed to raise #DE\\n",cases[c].name);return 1;
    }
    if(signal!=SIGFPE) return 1;
    faults++;
   }
  }
 }
 printf("x86 lowering: %u original/lowered division results and frames agree; %u real #DE boundaries passed\\n",executions,faults);
 return 0;
}
"""
    with tempfile.TemporaryDirectory(prefix="ssz-x86-lowering-") as directory:
        temp = Path(directory)
        (temp / "check.s").write_text("\n".join(assembly) + "\n")
        (temp / "check.c").write_text(source)
        subprocess.run(["cc", "-O2", "-no-pie", str(temp / "check.s"), str(temp / "check.c"), "-o", str(temp / "check")], check=True)
        subprocess.run([str(temp / "check")], check=True, timeout=120)


if __name__ == "__main__":
    main()
