/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/watchCache__checkSnapshotResourceVersion.lean`. Lean-first (no Rocq counterpart).
The snapshot's version is the expected one: the first branch returns.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.watchCache__checkSnapshotResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__ResourceVersion

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.storage.cacher

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]
variable [store_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]

theorem watchCache.checkSnapshotResourceVersion.wp_proof
    (wp_ResourceVersion : btreeStore.ResourceVersion.spec (GF := GF) (hG := hG)) :
    watchCache.checkSnapshotResourceVersion.spec (GF := GF) (hG := hG) := by
  intro wc p s rv
  wp_start as #Hs
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_ResourceVersion p DFrac.discard s rv) $$ [] as -
  · iframe #
    iunfold isSnap at Hs
    iexact Hs
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end cacher
end EtcdGrove
end Perennial
