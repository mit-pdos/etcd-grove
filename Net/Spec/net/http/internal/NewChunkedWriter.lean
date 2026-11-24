/-
`internal.NewChunkedWriter(w)` (Go 1.27.3's `net/http/internal/chunked.go`): a `*chunkedWriter`
whose `Wire` is `w` (`chunkedW`, `ChunkedDefs.lean`), as an `io.WriteCloser`. Proved in
`Net/Proof/net/http/internal/NewChunkedWriter.lean`.
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
abbrev NewChunkedWriter.spec : Prop :=
  ∀ (wi : GoInterfaceOk),
  {{ (True : IProp GF) }}
    (App (Val (@! net.http.internal.NewChunkedWriter)) (Val #(interface.ok wi)))
  {{ (cw : Loc), RET #(interface.mkOk (go.GoType.PointerType chunkedWriter.ty) #cw); chunkedW cw wi }}

end spec

end net.http.internal
end Perennial

