/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/btreeStore__deleteElem.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__deleteElem
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Delete

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

theorem btreeStore.deleteElem.wp_proof
    (wp_Delete : btree.BTree.Delete.spec (GF := GF) (hG := hG)) :
    btreeStore.deleteElem.spec (GF := GF) (hG := hG) := by
  intro p s rv0 e k rv
  wp_start as ⟨Hs, #He⟩
  ihave #Pb : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree $$ []
  · iPkgInit
  unfold ownStore
  icases Hs with ⟨%t, Htr, Hrv, Ht⟩
  (try wp_auto)
  wp_apply (wp_Delete elemOrder t s e k) $$ [$Ht] as Ht
  · iframe #
  (try wp_auto)
  unfold lookupElem
  iapply HΦ
  iexists t; iframe

end proof

end cacher
end EtcdGrove
end Perennial
