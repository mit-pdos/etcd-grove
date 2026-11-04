/-
The proof of `Spec/go_etcd_io/bbolt/DB__freepages.lean` (U10e, `notes/bbolt-proof-plan.md`): a
read transaction on the spare pair (`DB.beginTx_s`), the check `recursivelyCheckBucket` in a
forked goroutine (`Tx.recursivelyCheckBucket_root`, `Commit/CheckSpec`), which sends nothing and,
at its deferred `close(ech)`, hands the reader and the reachable map back to the receiver
(`Commit/CheckChan`'s close-only channel: Perennial's channel specs are `HasLC.hasLC`-only); the
receive loop sees the close; the scan of `[2, hwm)` appends the ids no page covers
(`freeIdsBelow`, `Commit/FreepagesScan`); the deferred `Rollback` gives the spare pair back.
-/
module

public import Spec.go_etcd_io.bbolt.DB__freepages
public import Spec.go_etcd_io.bbolt.DB__beginTx_s
public import Spec.go_etcd_io.bbolt.Tx__Rollback_r
public import Spec.go_etcd_io.bbolt.DB__meta
public import Proof.go_etcd_io.bbolt.Commit.FreepagesScan
public import Proof.go_etcd_io.bbolt.Commit.CheckChan

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.freepages.wp_proof
    (wp_beginTx_s : DB.beginTx_s.spec (GF := GF) (hG := hG))
    (wp_Rollback_r : Tx.Rollback_r.spec (GF := GF) (hG := hG))
    (wp_meta : DB.meta.spec (GF := GF) (hG := hG))
    (wp_Pgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (wp_check : Tx.recursivelyCheckBucket_root.spec (GF := GF) (hG := hG)) :
    DB.freepages.spec (GF := GF) (hG := hG) := by
  intro K C b l hok htree hhwm
  wp_start as ⟨#Hcore, Hpair, Hcur, Hmap, Hmc, Hop⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply wp_beginTx_s K C b l hok htree $$ [Hpair Hcur Hmap Hop] as %tx %err ⟨%He, Hrd, Hcur, Hmap, Hop⟩
  · iframe; iframe #
  subst He
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %rm Hrm
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %fm Hfm
  try wp_auto
  wp_apply (cc_wp_make1 (V := GoInterface)
    iprop(rdTxK K tx PairSrc.spare 1 (TxView.ro (View.ofC b C).data) (View.ofC b C) ∗
      (∃ M, rm ↦$ M ∗ ⌜reachOK (View.ofC b C).pages M⌝) ∗ fm ↦$ (∅ : GMap w64 Bool)))
    as %ch %γ ⟨#Hcc, Hrv, Hcl⟩
  try wp_auto
  ipersist tx
  ipersist reachable
  ipersist nofreed
  ipersist ech
  wp_apply wp_fork_tok_body $$ [Hrd Hrm Hfm Hcl]
  · iintro Htt
    wp_auto
    wp_bind (App (Val wrapDefer) _)
    wp_apply wp_with_defer as %d2 d2
    try wp_auto
    wp_apply wp_HexKVStringer
    try wp_auto
    rw [show structFieldRef Tx go!"root" tx = txRoot (GF := GF) tx from rfl]
    wp_apply wp_check K tx PairSrc.spare 1 _ _ rm fm ch $$ [Hrd Hrm Hfm] as ⟨Hrd, HM, Hfm⟩
    · iframe
    try wp_auto
    wp_apply (cc_wp_close (V := GoInterface) ch γ
        iprop(rdTxK K tx PairSrc.spare 1 (TxView.ro (View.ofC b C).data) (View.ofC b C) ∗
          (∃ M, rm ↦$ M ∗ ⌜reachOK C.pages M⌝) ∗ fm ↦$ (∅ : GMap w64 Bool)))
      $$ [Hcc Hcl Hrd HM Hfm]
    · rw [show (View.ofC b C).pages = C.pages from rfl]
      iframe Hcc Hcl Hrd Hfm
      iexact HM
    try wp_auto
    iframe
  try wp_auto
  wp_for
  try rw [ite_eq_left (by simp)]
  try wp_auto
  wp_apply (cc_wp_receive (V := GoInterface) (t := go.error) ch γ
      iprop(rdTxK K tx PairSrc.spare 1 (TxView.ro (View.ofC b C).data) (View.ofC b C) ∗
        (∃ M, rm ↦$ M ∗ ⌜reachOK C.pages M⌝) ∗ fm ↦$ (∅ : GMap w64 Bool)))
    $$ [Hcc Hrv] as ⟨Hrd, ⟨%M, Hrm, %HM⟩, Hfm⟩
  · iframe; iframe #
  try wp_auto
  wp_for_post
  try wp_auto
  done

end proof

end bbolt
end EtcdGrove
end Perennial
