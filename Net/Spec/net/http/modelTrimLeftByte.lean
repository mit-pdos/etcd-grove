/-
`modelTrimLeftByte(s, c)` (the model's `strings.TrimLeft(s, string(c))`, `textproto_model.go`): `s`
without its leading `c`s (`trimLeftByte`). Proved in `Net/Proof/net/http/modelTrimLeftByte.lean`.
-/
module

public import Net.Proof.net.http.Defs

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
abbrev modelTrimLeftByte.spec : Prop :=
  ∀ (s : GoString) (c : w8),
  {{ (True : IProp GF) }}
    (App (App (Val (@! net.http.modelTrimLeftByte)) (Val #s)) (Val #c))
  {{ RET #(trimLeftByte s c); True }}

end spec

end net.http
end Perennial
