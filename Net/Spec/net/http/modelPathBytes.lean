/-
`modelPathBytes(s)` (`textproto_model.go`): whether every byte of `s` is a `pathByte`
(`Net/Proof/net/http/RequestDefs.lean`). Proved in `Net/Proof/net/http/modelPathBytes.lean`.
-/
module

public import Net.Proof.net.http.RequestDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
abbrev modelPathBytes.spec : Prop :=
  ∀ (s : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! net.http.modelPathBytes)) (Val #s))
  {{ RET #(s.all pathByte); True }}

end spec

end net.http
end Perennial
