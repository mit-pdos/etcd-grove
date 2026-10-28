/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/btreeStore__Clone.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__Clone
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Clone

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

theorem btreeStore.Clone.wp_proof
    (wp_Clone : btree.BTree.Clone.spec (GF := GF) (hG := hG)) :
    btreeStore.Clone.spec (GF := GF) (hG := hG) := by
  intro p s rv
  wp_start as Hs
  ihave #Pb : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree $$ []
  · iPkgInit
  unfold ownStore
  icases Hs with ⟨%t, Htr, Hrv, Ht⟩
  wp_auto
  wp_apply (wp_Clone elemOrder t s) $$ [$Ht] as %t2 ⟨Ht, Ht2⟩
  irename «$r0» => Hp2
  generalize «$r0_ptr» = p2 at *
  icases typedPointsto_split _ _ _ $$ Hp2 with Hp2
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hp2 with ⟨Htr2, Hrv2, -⟩
  (try wp_auto)
  iapply HΦ
  isplitl [Htr Hrv Ht]
  · iexists t; iframe
  iexists t2; iframe

end proof

end cacher
end EtcdGrove
end Perennial
