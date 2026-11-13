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
public import Proof.go_etcd_io.bbolt.Read.Open

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
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
  -- the scan of `[2, hwm)`
  ihave #Hpkg := rdTxK_pkgInit K tx PairSrc.spare 1 _ _ $$ Hrd
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  have hhwm64 : C.hwm < 2 ^ 64 := by omega
  ihave IH : (∃ (j : w64) (fs : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "fids" ∷ fids_ptr ↦ fs ∗ "Hfs" ∷ fs ↦* freeIdsBelow C j.toNat ∗
      "Hcap" ∷ ownSliceCap w64 fs (DFrac.own 1) ∗ "%Hj" ∷ ⌜2 ≤ j.toNat ∧ j.toNat ≤ C.hwm⌝ ∗
      "Hrd" ∷ rdTxK K tx PairSrc.spare 1 (TxView.ro (View.ofC b C).data) (View.ofC b C) ∗
      "Hrm" ∷ rm ↦$ M ∗ "Hmc" ∷ metaCellsQ (Qp.half 1).half (some (b, l)) C ∗
      "Hmap" ∷ ghostVar K.B.map (Qp.half 1) (some (b, l)) ∗ "db" ∷ db_ptr ↦ K.db : IProp GF)
    $$ [i fids Hrd Hrm Hmc Hmap db]
  · iexists W64 2, slice.nil
    simp only [named]
    rw [show (W64 2).toNat = 2 from rfl, freeIdsBelow_two]
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    ipureintro
    have := htree.2.2.2.1
    have h2 : 2 ≤ C.hwm := by
      obtain ⟨⟨hwf, -⟩, -⟩ := htree
      rcases hwf with ⟨_, _, h2, hlt, _⟩
      omega
    exact ⟨Nat.le_refl 2, h2⟩
  wp_for IH
  icases rdTxK_mapFields_acc K tx PairSrc.spare 1 _ _ _ _ $$ [Hrd Hmap]
    with ⟨%dq, %l', %Hms, Hmf, Hmap, Hback⟩
  · iframe
  have hl' : l' = l := by
    simp only [View.ofC, Option.some.injEq, Prod.mk.injEq] at Hms; exact Hms.2.symm
  subst hl'
  rw [show (View.ofC b C).base = b from rfl]
  wp_apply wp_meta K.db b l' C dq _ hok $$ [Hmf Hmc] as ⟨Hmf, Hmc⟩
  · iframe
  wp_apply wp_meta_Pgid wp_Pgid b l' C _ hok $$ [Hmc] as Hmc
  · iframe
  ihave Hrd := Hback $$ Hmf
  try wp_auto
  have hjz : uint.Z j = (j.toNat : Int) := rfl
  have hwz : uint.Z (W64 (C.hwm : Int)) = (C.hwm : Int) := by
    rw [show uint.Z (W64 (C.hwm : Int)) = ((W64 (C.hwm : Int)).toNat : Int) from rfl,
      toNat_W64_of_lt _ hhwm64]
  rw [hjz, hwz]
  by_cases hlt : j.toNat < C.hwm
  · rw [decide_eq_true (show (j.toNat : Int) < (C.hwm : Int) by omega)]
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    wp_apply (wp_map_lookup2 _ _ rm M j (DFrac.own 1)) $$ Hrm as Hrm
    try wp_auto
    have hsucc : (j + W64 1).toNat = j.toNat + 1 := by
      rw [BitVec.toNat_add]; simp; omega
    by_cases hc : coversSlot C.pages j.toNat
    · rw [decide_eq_true ((HM j).2 hc)]
      simp only [Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists (j + W64 1), fs
      simp only [named]
      rw [hsucc, freeIdsBelow_succ C _ Hj.1, ite_eq_left hc, List.append_nil]
      iframe
      ipureintro; omega
    · have hns : ¬ (M !! j).isSome = true := fun h => hc ((HM j).1 h)
      rw [decide_eq_false hns]
      simp only [Bool.not_false]
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hfs $Hcap $Hsl1] as %fs' ⟨Hfs, Hcap, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists (j + W64 1), fs'
      simp only [named]
      rw [hsucc, freeIdsBelow_succ C _ Hj.1, ite_eq_right hc]
      have hjw : W64 ((j.toNat : Nat) : Int) = j := by simp
      rw [hjw]
      iframe
      ipureintro; omega
  · have hjh : j.toNat = C.hwm := by omega
    rw [decide_eq_false (show ¬ (j.toNat : Int) < (C.hwm : Int) by omega)]
    try simp only [val_bool_eq, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    try simp only [_root_.decide_true, ↓reduceIte]
    try wp_auto
    wp_apply wp_Rollback_r K tx PairSrc.spare _ _ $$ [Hrd] as %err' ⟨%He, -, Hpair⟩
    · iexact Hrd
    subst He
    try wp_auto
    iapply HΦ
    rw [hjh, freeIdsBelow_hwm]
    iframe
    isplitr
    · ipureintro; exact freeIdsOf_facts C hhwm
    unfold pairBack at *; iexact Hpair

end proof

end bbolt
end EtcdGrove
end Perennial
