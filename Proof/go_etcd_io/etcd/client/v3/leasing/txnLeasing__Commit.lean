/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__Commit.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__Commit
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__validateDeleteOps
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__eval
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__serverTxn
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingCommitLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem txnLeasing.Commit.wp_proof
    (hvdo : leasingKV.validateDeleteOps.spec (GF := GF) (hG := hG))
    (heval : txnLeasing.eval.spec (GF := GF) (hG := hG))
    (hsrv : txnLeasing.serverTxn.spec (GF := GF) (hG := hG)) :
    txnLeasing.Commit.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx ctx cs b lo
  wp_start as ⟨Htxn, Hrd, #Hcc, #Hlo, %Hbnd⟩
  -- etcd#22118: `validateDeleteOps` of both branches first.
  icases ownTxnLeasing_acc $$ Htxn with ⟨%csl, %tsl, %esl, %tops0, %eops0, Hl, Hc, Hcs, Hts, Hes,
    #⟨Hlkv, -, -, Hthen, Helse⟩, %Hops0, Hback⟩
  obtain ⟨Ht0, He0⟩ := Hops0
  ihave ⟨%kv0, -, -, #Hpfx, %Hpne⟩ := isLeasingKV_kv lkv γ pfx $$ Hlkv
  ihave ⟨%tvs, #Htvs, Htl⟩ := opsAt_gather tsl b.thenOs tops0 Ht0 $$ Hthen
  ihave ⟨%evs, #Hevs, Hel⟩ := opsAt_gather esl b.elseOs eops0 He0 $$ Helse
  (try wp_auto)
  wp_apply hvdo $$ [$Hpfx $Htvs $Htl] as %e1 %He1
  simp only [leavesL_leaves] at He1
  cases e1 with
  | ok e =>
    (try wp_auto)
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact LeaseDeleteGuard.of_ne_nil (by simp)
    unfold commitOutcome
    iright
    iexists tops0, eops0
    isplitr
    · ipureintro; exact ⟨Ht0, He0⟩
    unfold txnCommitResult
    ileft; ipureintro; simp
  | nil =>
  (try wp_auto)
  wp_apply hvdo $$ [$Hpfx $Hevs $Hel] as %e2 %He2
  simp only [leavesL_leaves] at He2
  cases e2 with
  | ok e =>
    (try wp_auto)
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact LeaseDeleteGuard.of_ne_nil (by simp)
    unfold commitOutcome
    iright
    iexists tops0, eops0
    isplitr
    · ipureintro; exact ⟨Ht0, He0⟩
    unfold txnCommitResult
    ileft; ipureintro; simp
  | nil =>
  have Hguard : ∀ err, LeaseDeleteGuard pfx (b.thenOs ++ b.elseOs) err := fun _ =>
    LeaseDeleteGuard.of_none Hpne (by
      intro o ho
      rcases List.mem_append.1 ho with ho | ho
      · exact He1.1 rfl o ho
      · exact He2.1 rfl o ho)
  ihave HΦ : iprop(∀ (resp : Loc) (err : GoInterface), lkvReader lkv γ pfx ∗
      commitOutcome γ lo b resp err -∗ Φ (PairV #resp #err)) $$ [HΦ]
  · iintro %resp %err ⟨Hrd, Hd⟩
    iapply HΦ
    iframe
    ipureintro; exact Hguard err
  ihave Htxn := Hback $$ [$Hl] [$Hc] [$Hcs] [$Hts] [$Hes]
  wp_auto_lc 1
  wp_apply heval $$ [$Htxn $Hrd] as %resp %err ⟨Htxn, Hrd, Hres⟩
  · ipureintro; exact Hbnd
  icases Hres with (%Hn | ⟨%Hn, Hev⟩)
  · subst Hn
    cases err with
    | nil =>
      wp_auto
      wp_apply hsrv $$ [$Htxn $Hrd $Hcc $Hlo] as %resp %err ⟨Hrd, %tops, %eops, %Hops, Hres⟩
      iapply HΦ
      iframe
      unfold commitOutcome
      iright
      iexists tops, eops
      iframe
      ipureintro; exact Hops
    | ok e =>
      wp_auto
      ihave %Hops := ownTxnLeasing_ops $$ Htxn
      obtain ⟨tops, eops, h1, h2⟩ := Hops
      iapply HΦ
      iframe
      unfold commitOutcome
      iright
      iexists tops, eops
      isplitr
      · ipureintro; exact ⟨h1, h2⟩
      unfold txnCommitResult
      ileft; ipureintro; simp
  · obtain ⟨Hn, rfl⟩ := Hn
    simp only [Hn, decide_false]
    wp_auto
    iapply HΦ
    iframe
    unfold commitOutcome
    ileft
    iframe
    ipureintro; exact ⟨rfl, Hn⟩

/-- **etcd#22118's spec is compatible**: same precondition, a stronger postcondition (the guard
`LeaseDeleteGuard` added), so it implies the spec before the PR. -/
theorem txnLeasing.Commit.spec_implies_old (h : txnLeasing.Commit.spec (GF := GF) (hG := hG)) :
    txnLeasing.Commit.spec_old (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx ctx cs b lo
  iintro %Φ Hpre HΦ
  iapply h txn lkv γ pfx ctx cs b lo $$ [Hpre]
  · iexact Hpre
  iintro %resp %err
  inext
  iintro ⟨Hrd, -, Hd⟩
  iapply HΦ
  iframe

end proof

end leasing
end EtcdGrove
end Perennial
