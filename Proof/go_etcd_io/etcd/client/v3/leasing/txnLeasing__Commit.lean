/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__Commit.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__Commit
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem txnLeasing.Commit.wp_proof (heval : txnLeasing.eval.spec (GF := GF) (hG := hG))
    (hsrv : txnLeasing.serverTxn.spec (GF := GF) (hG := hG)) :
    txnLeasing.Commit.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx ctx cs b lo
  wp_start as ⟨Htxn, Hrd, #Hcc, #Hlo, %Hbnd⟩
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

end proof

end leasing
end EtcdGrove
end Perennial
