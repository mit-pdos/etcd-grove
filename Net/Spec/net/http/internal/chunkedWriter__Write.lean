/-
`cw.Write(data)` (Go 1.27.3's `net/http/internal/chunked.go`) on a `*chunkedWriter` whose `Wire` is a
chunk sink (`chunkSink wi W B`, `ChunkedDefs.lean`) at `W out`: one chunk of `data`'s bytes `xs`
(`chunkWire xs`: its length in hexadecimal by `fmt.Fprintf("%x\r\n", len(data))`, the bytes, `"\r\n"`
by `io.WriteString`; nothing for no bytes) accepted by the sink, then, for a
`*FlushAfterChunkWriter` sink, its `Flush`; `(len(data), nil)` and `W (out ++ chunkWire xs)`, or an
error with the sink broken (`B err`). `data` is only read. `io.ErrShortWrite` is not returned: a
sink accepts all of a `Write`'s bytes or fails. Proved in
`Net/Proof/net/http/internal/chunkedWriter__Write.lean`.
-/
module

public import Net.Proof.net.http.internal.ChunkedDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http.internal

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.internal.Assumptions]

/-- See the file header. -/
abbrev chunkedWriter.Write.spec : Prop :=
  ∀ (cw : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (B : GoInterface → IProp GF)
    (out : List w8) (p : GoSlice) (xs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      chunkedW cw wi ∗
      chunkSink wi W B ∗ W out ∗ p ↦*{dq} xs }}
    (App (Val #(methods (go.GoType.PointerType chunkedWriter.ty) go!"Write" #cw)) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); chunkedW cw wi ∗ p ↦*{dq} xs ∗
      ((⌜err = interface.nil ∧ sint.Z n = xs.length⌝ ∗ W (out ++ chunkWire xs)) ∨
        (⌜err ≠ interface.nil⌝ ∗ B err)) }}

end spec

end net.http.internal
end Perennial

