/-
`t.parseTransferEncoding()` on a `transferReader` whose header is empty (no `Transfer-Encoding`):
`nil`, nothing changed. Proved in `Net/Proof/net/http/transferReader__parseTransferEncoding.lean`.
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
abbrev transferReader.parseTransferEncoding.spec : Prop :=
  ∀ (t : Loc) (tr : net.http.transferReader),
  {{ (t ↦ tr ∗ tr.Header' ↦$ (∅ : GMap GoString GoSlice) : IProp GF) }}
    (App (Val (t @!! go.GoType.PointerType net.http.transferReader.ty @!! go!"parseTransferEncoding"))
      (Val #()))
  {{ RET #interface.nil; t ↦ tr ∗ tr.Header' ↦$ (∅ : GMap GoString GoSlice) }}

end spec

end net.http
end Perennial
