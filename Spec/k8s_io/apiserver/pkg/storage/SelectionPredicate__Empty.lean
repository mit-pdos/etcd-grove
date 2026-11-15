/-
`s.Empty()` (`selection_predicate.go:149-151`) of a predicate with no shard selector: both
selectors empty. Proved from the translated body (stage 7e-2, `notes/k8s-7e-2-draft.md` §4.3). Lean-first (no
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
abbrev storage.SelectionPredicate.Empty.spec : Prop :=
  ∀ (pp : Loc) (dq : DFrac) (p : k8s_io.apiserver.pkg.storage.SelectionPredicate) (le fe : Bool) (lm fm : GMap GoString GoString → Bool),
  p.ShardSelector' = GoInterface.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ pp ↦{dq} p ∗
      labelSelOk p.Label' le lm ∗ fieldSelOk p.Field' fe fm }}
    (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty @!! go!"Empty")) (Val #()))
  {{ RET #(le && fe); pp ↦{dq} p }}

end spec

end EtcdGrove
end Perennial
