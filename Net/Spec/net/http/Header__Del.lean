/-
`h.Del(key)` on an `http.Header` map `h` (`textproto.MIMEHeader(h).Del(key)`), `key` already canonical
(`canonQuick`): `key`'s entry deleted. Proved in `Net/Proof/net/http/Header__Del.lean`.
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
abbrev Header.Del.spec : Prop :=
  ∀ (h : Loc) (m : GMap GoString GoSlice) (key : GoString),
  {{ (⌜canonQuick key = true⌝ ∗ h ↦$ m : IProp GF) }}
    (App (Val #(methods net.http.Header.ty go!"Del" #h)) (Val #key))
  {{ RET #(); h ↦$ (GMap.delete key m) }}

end spec

end net.http
end Perennial
