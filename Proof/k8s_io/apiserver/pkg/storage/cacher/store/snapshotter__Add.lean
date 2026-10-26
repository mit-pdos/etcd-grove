/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/snapshotter__Add.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.snapshotter__Add
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__ReplaceOrInsert
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Lemmas.Insert

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

theorem snapshotter.Add.wp_proof
    (wp_ReplaceOrInsert : btree.BTree.ReplaceOrInsert.spec (GF := GF) (hG := hG)) :
    snapshotter.Add.spec (GF := GF) (hG := hG) := by
  intro l rv0 p s rv hlt
  wp_start as ⟨Hs, #Hsnap⟩
  ihave #Pb : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree $$ []
  · iPkgInit
  unfold ownSnapshotter
  icases Hs with ⟨%t, %srv, %en, %ss, Ht_, Ht, #Hss, Hsrv, Hen, %Hle⟩
  ihave #Hsnap' := Hsnap
  unfold isSnap ownStore
  icases Hsnap' with ⟨%tp, #Htp, #Hrvp, -⟩
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
  wp_apply (wp_ReplaceOrInsert snapOrder t ss p rv) $$ [$Ht] as Ht
  · simp only [snapOrder]; iframe #
  (try wp_auto)
  wp_apply (wp_max_uint64 srv rv)
  rw [show (if uint.Z rv < uint.Z srv then srv else rv) = rv from ite_cond_eq_false _ _ (eq_false (by omega))]
  (try wp_auto)
  iapply HΦ
  iexists t, _, true, _
  iframe
  isplitr
  · iintro !> %x %Hx
    rcases btree.InsertLemmas.model_mem_insert ss (p, rv) x Hx with h | h
    · iapply Hss; ipureintro; exact h
    · subst h; iexists s; iexact Hsnap
  ipureintro; omega

end proof

end cacher
end EtcdGrove
end Perennial
