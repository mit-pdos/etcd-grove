/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/btreeStore__getByKey.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__getByKey
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Get

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

theorem btreeStore.getByKey.wp_proof
    (wp_Get : btree.BTree.Get.spec (GF := GF) (hG := hG)) :
    btreeStore.getByKey.spec (GF := GF) (hG := hG) := by
  intro p dq s rv key
  wp_start as Hs
  ihave #Pb : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree $$ []
  · iPkgInit
  unfold ownStore
  icases Hs with ⟨%t, Htr, Hrv, Ht⟩
  (try wp_auto)
  icases typedPointsto_split _ _ _ $$ «$r0» with Hke
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hke with ⟨Hkey, -, -, -⟩
  ipersist Hkey
  (try wp_auto)
  wp_apply (wp_Get elemOrder t dq s «$r0_ptr» key) $$ [$Ht] as Ht
  · simp only [elemOrder]; iframe #
  (try wp_auto)
  unfold lookupElem
  iapply HΦ
  iexists t; iframe

end proof

end cacher
end EtcdGrove
end Perennial
