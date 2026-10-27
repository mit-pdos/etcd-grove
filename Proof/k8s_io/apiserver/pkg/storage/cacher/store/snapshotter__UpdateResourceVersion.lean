/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/snapshotter__UpdateResourceVersion.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.snapshotter__UpdateResourceVersion

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

theorem snapshotter.UpdateResourceVersion.wp_proof :
    snapshotter.UpdateResourceVersion.spec (GF := GF) (hG := hG) := by
  intro l rv0 rv hle
  wp_start as Hs
  unfold ownSnapshotter
  icases Hs with ⟨%t, %srv, %en, %ss, Ht_, Ht, #Hss, Hsrv, Hen, %Hle⟩
  (try wp_auto)
  cases en
  · (try wp_auto)
    iapply HΦ
    iexists t, srv, false, ss
    iframe
    iframe #
    ipureintro; omega
  (try wp_auto)
  wp_if_destruct
  · exfalso; word
  (try wp_auto)
  wp_apply (wp_max_uint64 srv rv)
  rw [show (if uint.Z rv < uint.Z srv then srv else rv) = rv from ite_cond_eq_false _ _ (eq_false (by omega))]
  (try wp_auto)
  iapply HΦ
  iexists t, _, true, ss
  iframe
  iframe #
  ipureintro; omega

end proof

end cacher
end EtcdGrove
end Perennial
