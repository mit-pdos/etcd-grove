/-
`modelPathByte(c)` (`textproto_model.go`): `pathByte c` (`Net/Proof/net/http/RequestDefs.lean`).
Proved in `Net/Proof/net/http/modelPathByte.lean`.
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
abbrev modelPathByte.spec : Prop :=
  ∀ (c : w8),
  {{ (True : IProp GF) }}
    (App (Val (@! net.http.modelPathByte)) (Val #c))
  {{ RET #(pathByte c); True }}

end spec

end net.http
end Perennial
