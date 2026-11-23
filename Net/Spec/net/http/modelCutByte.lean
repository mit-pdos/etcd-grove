/-
`modelCutByte(s, sep)` (the model's `strings.Cut(s, string(sep))`, `textproto_model.go`): `cutByte s sep`
(`Net/Proof/net/http/Defs.lean`): the bytes before and after the first `sep`, and `true`; or `s`,
`""`, `false`. Proved in `Net/Proof/net/http/modelCutByte.lean`.
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
abbrev modelCutByte.spec : Prop :=
  ∀ (s : GoString) (sep : w8),
  {{ (True : IProp GF) }}
    (App (App (Val (@! net.http.modelCutByte)) (Val #s)) (Val #sep))
  {{ RET (PairV (PairV #(cutByte s sep).1 #(cutByte s sep).2.1) #(cutByte s sep).2.2); True }}

end spec

end net.http
end Perennial
