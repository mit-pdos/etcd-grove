/-
`s.MatchesObjectAttributes(l, f)` (`selection_predicate.go:113-121`): `true` if both selectors
are empty, else the label selector's and the field selector's answers on the sets. Proved from the translated body (stage 7e-2, `notes/k8s-7e-2-draft.md` §4.3). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.SelDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI k8s

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.SelectionPredicate.MatchesObjectAttributes.spec : Prop :=
  ∀ (pp : Loc) (dq : DFrac) (p : k8s_io.apiserver.pkg.storage.SelectionPredicate) (le fe : Bool) (lm fm : GMap GoString GoString → Bool)
    (lp fp : Loc) (L F : GMap GoString GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ pp ↦{dq} p ∗
      labelSelOk p.Label' le lm ∗ fieldSelOk p.Field' fe fm ∗ mapRO lp L ∗ mapRO fp F }}
    (App (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty @!! go!"MatchesObjectAttributes")) (Val #lp)) (Val #fp))
  {{ RET #((le && fe) || (lm L && fm F)); pp ↦{dq} p }}

end spec

end EtcdGrove
end Perennial
