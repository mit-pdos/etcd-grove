/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/newBtreeStore.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.newBtreeStore
public import Spec.k8s_io.utils.third_party.forked.golang.btree.New

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.storage.cacher.store

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem newBtreeStore.wp_proof
    (wp_New : btree.New.spec (GF := GF) (hG := hG)) :
    newBtreeStore.spec (GF := GF) (hG := hG) := by
  intro degree h1 h2
  wp_start
  ihave #Pb : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_New elemOrder degree _ h1 h2) $$ [] as %t Ht
  · iframe #
    unfold btree.isLess
    iintro %a %b %ka %kb
    simp only [elemOrder, isElem]
    wp_start as ⟨⟨%ea, #Ha, %Hka⟩, ⟨%eb, #Hb, %Hkb⟩⟩
    icases typedPointsto_split _ _ _ $$ Ha with Ha
    try simp only [TypedPointsto.typedPointstoDef]
    icases Ha with ⟨Hka', -⟩
    icases typedPointsto_split _ _ _ $$ Hb with Hb
    try simp only [TypedPointsto.typedPointstoDef]
    icases Hb with ⟨Hkb', -⟩
    subst Hka Hkb
    (try wp_auto)
    iapply HΦ
    ipureintro
    exact decide_eq_true_iff
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end cacher
end EtcdGrove
end Perennial
