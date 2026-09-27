module

public import Kraken.X64.Parser
public import Kraken.X64.OmniSemantics

@[expose] public section

namespace SszX86

open Kraken.X64.Parser

/-- System V ABI: `rdi` is the caller-owned input pointer; `rax` is the result.
The compiler-binding check must compare this program with `asm/x86/uint64.o`.
Kraken parses assembly, not machine bytes; that binding remains a trust boundary. -/
def loadProgram : Program := parse("
  movq (%rdi), %rax
  ret
")

/-- System V ABI: `rdi` is the caller-owned output pointer; `rsi` is the value.
Neither kernel performs a length check or constitutes a public SSZ deserializer. -/
def storeProgram : Program := parse("
  movq %rsi, (%rdi)
  ret
")

end SszX86
