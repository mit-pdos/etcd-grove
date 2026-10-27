/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/btreeStore__ResourceVersion.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__ResourceVersion

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.storage.cacher.store

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem btreeStore.ResourceVersion.wp_proof :
    btreeStore.ResourceVersion.spec (GF := GF) (hG := hG) := by
  intro p dq s rv
  wp_start as Hs
  unfold ownStore
  icases Hs with ⟨%t, Htr, Hrv, Ht⟩
  (try wp_auto)
  iapply HΦ
  iexists t; iframe

end proof

end cacher
end EtcdGrove
end Perennial
