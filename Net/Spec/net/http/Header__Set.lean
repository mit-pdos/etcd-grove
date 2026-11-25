/-
`h.Set(key, value)` on an `http.Header` map `h` (`textproto.MIMEHeader(h).Set(key, value)`), `key`
already canonical (`canonQuick`): `key`'s lines replaced by `key: value` (`hdrSetL`). Proved in
`Net/Proof/net/http/Header__Set.lean`. Lean-first.
-/
module

public import Net.Proof.net.http.WireDefs

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
abbrev Header.Set.spec : Prop :=
  ∀ (h : Loc) (hb : List HdrLine) (key value : GoString), canonQuick key = true →
  {{ hdrOwn (GF := GF) h hb }}
    (App (App (Val #(methods net.http.Header.ty go!"Set" #h)) (Val #key)) (Val #value))
  {{ RET #(); hdrOwn h (hdrSetL hb key value) }}

end spec
end net.http
end Perennial
