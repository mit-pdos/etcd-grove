/-
`h.Del(key)` on a `textproto.MIMEHeader` map `h` (Go 1.27.3), `key` already canonical (`canonQuick`):
`key`'s entry deleted. Proved in `Net/Proof/net/textproto/MIMEHeader__Del.lean`.
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
abbrev MIMEHeader.Del.spec : Prop :=
  ∀ (h : Loc) (m : GMap GoString GoSlice) (key : GoString),
  {{ (⌜net.http.canonQuick key = true⌝ ∗ h ↦$ m : IProp GF) }}
    (App (Val #(methods net.textproto.MIMEHeader.ty go!"Del" #h)) (Val #key))
  {{ RET #(); h ↦$ (GMap.delete key m) }}

end spec

end net.textproto
end Perennial
