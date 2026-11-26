/-
`h.Set(key, value)` on a `textproto.MIMEHeader` map `h` (Go 1.27.3), `key` already canonical
(`canonQuick`): `key`'s entry set to a fresh slice `[value]`. Proved in
`Net/Proof/net/textproto/MIMEHeader__Set.lean`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.textproto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.textproto.Assumptions]

/-- See the file header. -/
abbrev MIMEHeader.Set.spec : Prop :=
  ∀ (h : Loc) (ms : GMap GoString GoSlice) (key value : GoString),
  {{ (⌜net.http.canonQuick key = true⌝ ∗ h ↦$ ms : IProp GF) }}
    (App (App (Val #(methods net.textproto.MIMEHeader.ty go!"Set" #h)) (Val #key)) (Val #value))
  {{ (s : GoSlice), RET #(); h ↦$ (<[key := s]> ms) ∗ s ↦* ([value] : List GoString) }}

end spec

end net.textproto
end Perennial
