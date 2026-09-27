/* Process entry and Linux output for freestanding smoke executables.
 * All memory operations are linked from asm/<arch>. */
#include <stddef.h>

/* Kernel entry has no C return address. Align x86's stack BEFORE calling C,
 * rather than assuming an ordinary C function prologue is a valid _start. */
#if defined(__x86_64__)
__asm__(".text\n.global _start\n.type _start,@function\n_start:\n"
        "xor %ebp,%ebp\nandq $-16,%rsp\ncall smoke_main\n"
        "mov %eax,%edi\nmov $60,%eax\nsyscall\nud2\n");
#elif defined(__aarch64__)
__asm__(".text\n.global _start\n.type _start,%function\n_start:\n"
        "mov x29,xzr\nmov x30,xzr\nbl smoke_main\n"
        "mov x8,#93\nsvc #0\nbrk #0\n");
#else
#error Unsupported architecture
#endif

void smoke_write(const char *data, size_t size) {
    while (size != 0) {
        long written;
#if defined(__x86_64__)
        __asm__ volatile ("syscall" : "=a"(written)
            : "a"(1L), "D"(2L), "S"(data), "d"(size)
            : "rcx", "r11", "memory");
#else
        register long result __asm__("x0") = 2;
        register const char *buffer __asm__("x1") = data;
        register size_t length __asm__("x2") = size;
        register long number __asm__("x8") = 64;
        __asm__ volatile ("svc #0" : "+r"(result)
            : "r"(buffer), "r"(length), "r"(number) : "memory");
        written = result;
#endif
        if (written == -4) continue; /* Linux EINTR */
        if (written <= 0) return;
        data += (size_t)written;
        size -= (size_t)written;
    }
}
