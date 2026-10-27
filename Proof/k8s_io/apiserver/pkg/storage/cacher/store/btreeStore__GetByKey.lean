/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/btreeStore__GetByKey.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__GetByKey
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__getByKey

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

theorem btreeStore.GetByKey.wp_proof
    (wp_getByKey : btreeStore.getByKey.spec (GF := GF) (hG := hG)) :
    btreeStore.GetByKey.spec (GF := GF) (hG := hG) := by
  intro p dq s rv key
  wp_start as Hs
  (try wp_auto)
  wp_apply (wp_getByKey p dq s rv key) $$ [$Hs] as Hs
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end cacher
end EtcdGrove
end Perennial
