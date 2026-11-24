/-
`cw.Close()` (Go 1.27.3's `net/http/internal/chunked.go`) on a `*chunkedWriter` whose `Wire` is a
chunk sink at `W out`: the last chunk `"0\r\n"` (`lastChunk`) by `io.WriteString`, accepted, or an error
with the sink broken. Proved in `Net/Proof/net/http/internal/chunkedWriter__Close.lean`.
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
abbrev chunkedWriter.Close.spec : Prop :=
  ∀ (cw : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (B : GoInterface → IProp GF)
    (out : List w8),
  {{ chunkedW cw wi ∗
      chunkSink wi W B ∗ W out }}
    (App (Val #(methods (go.GoType.PointerType chunkedWriter.ty) go!"Close" #cw)) (Val #()))
  {{ (err : GoInterface), RET #err; chunkedW cw wi ∗
      ((⌜err = interface.nil⌝ ∗ W (out ++ lastChunk)) ∨ (⌜err ≠ interface.nil⌝ ∗ B err)) }}

end spec

end net.http.internal
end Perennial

