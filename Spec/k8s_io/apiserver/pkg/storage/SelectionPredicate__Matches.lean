/-
`s.Matches(obj)` (`selection_predicate.go:96-111`) of a predicate with no shard selector, on an
object held as `objAt x o` (any object predicate; the store's `S.objAt _ _ rv`): `true` if both
selectors are empty (`GetAttrs` not called), else the selectors' answers on `GetAttrs`' sets; no
error. Replaces 7e-3b's driver-specialized hypothesis (#22). Proved from the translated body (stage 7e-2, `notes/k8s-7e-2-draft.md` §4.3). Lean-first (no
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
abbrev storage.SelectionPredicate.Matches.spec : Prop :=
  ∀ (O : Type) (objAt : GoInterface → O → IProp GF) (pp : Loc) (dq : DFrac) (p : k8s_io.apiserver.pkg.storage.SelectionPredicate)
    (le fe : Bool) (lm fm : GMap GoString GoString → Bool) (lab fld : O → GMap GoString GoString)
    (x : GoInterface) (o : O),
  p.ShardSelector' = GoInterface.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ pp ↦{dq} p ∗
      labelSelOk p.Label' le lm ∗ fieldSelOk p.Field' fe fm ∗ getAttrsOk objAt p.GetAttrs' lab fld ∗
      objAt x o }}
    (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty @!! go!"Matches")) (Val #x))
  {{ RET (PairV #((le && fe) || (lm (lab o) && fm (fld o))) #GoInterface.nil);
      pp ↦{dq} p ∗ objAt x o }}

end spec

end EtcdGrove
end Perennial
