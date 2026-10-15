/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stm__commit.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__commit
public import Spec.go_etcd_io.etcd.client.v3.concurrency.writeSet__puts
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTMCommit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

private theorem B_conv {PROP : Type _} [BI PROP] (B : TxnBuild → PROP) (b b' : TxnBuild)
    (h : b = b') : B b ⊢ B b' := h ▸ .rfl

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem stm.commit.wp_proof (hPuts : writeSet.puts.spec (GF := GF) (hG := hG)) :
    stm.commit.spec (GF := GF) (hG := hG) := by
  intro lvl b pfx st lo
  wp_start as ⟨#Henv, Hrs, Hws, #Hcf, #Hlo⟩
  iunfold stmEnv at Henv
  icases Henv with ⟨%c, %ctx, %cs, #Hc, #Hcl, #Hctx, #Hcs⟩
  iunfold isEtcdSTMClient at Hcl
  icases Hcl with ⟨%kv, %cctx, %ccs, #HKV, #HTxn, -, -, -⟩
  iunfold stmConflictsAt at Hcf
  icases Hcf with ⟨%f, #Hf, #Hfs⟩
  iunfold stmRsetOwn at Hrs
  icases Hrs with ⟨%rm, %rsMap, Hrf, Hrm, #Hreads⟩
  iunfold stmWsetOwn at Hws
  icases Hws with ⟨%wm, %wsMap, Hwf, Hwm, #Hwrites⟩
  wp_auto
  wp_method_call
  wp_auto
  wp_apply hPuts wm (DFrac.own 1) pfx wsMap st.writes $$ [$Hpkg $Hwm $Hwrites] as %osl ⟨Hwm, %os, %ops, #Hos, %Hops⟩
  ihave Hrs : stmRsetOwn pfx b st.reads $$ [Hrf Hrm]
  · iunfold stmRsetOwn; iexists rm, rsMap; iframe; iframe Hreads
  ihave Hws : stmWsetOwn pfx b st.writes $$ [Hwf Hwm]
  · iunfold stmWsetOwn; iexists wm, wsMap; iframe; iframe Hwrites
  iunfold conflictsSpec at Hfs
  wp_apply Hfs $$ %st.reads %st.writes [$Hrs $Hws] as %csl ⟨Hrs, Hws, %ms, #Hms, %Hms⟩
  iunfold isEtcdTxnKV at HTxn
  wp_apply HTxn $$ %ctx %cs [$Hcs] as %t ⟨%B, HB, #HBs⟩
  iunfold txnBuilderSpec at HBs
  icases HBs with ⟨#HIf, #HThen, -, #HCommit, -⟩
  wp_apply_raw HIf $$ %TxnBuild.empty %csl %ms [$HB]
  · iframe Hms; ipureintro; simp [TxnBuild.empty]
  inext
  iintro HB
  (try wp_auto)
  wp_apply_raw HThen $$ %_ %osl %os %ops [$HB]
  · iframe Hos; ipureintro; exact ⟨Hops.1, rfl, rfl⟩
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv B _ ({ model := { cmps := ms, thenOps := ops, elseOps := [] }, cif := true, cthen := true, celse := false } : TxnBuild) (by simp [TxnBuild.empty, TxnModel.empty]) $$ HB
  ihave #Hfacts := readsAt_readFacts pfx rsMap st.reads $$ Hreads
  ihave %Hru := readFacts_under pfx st.reads $$ Hfacts
  ihave %Hwu := writesAt_under pfx wsMap st.writes $$ Hwrites
  wp_apply HCommit $$ %({ model := { cmps := ms, thenOps := ops, elseOps := [] }, cif := true, cthen := true, celse := false } : TxnBuild) %lo [$HB $Hlo] as %resp %err Hres
  · ipureintro; exact stmTxn_under pfx lvl Hru Hwu Hms Hops.2 (by simp)
  ihave #Hres := txnCommitResultTok_result _ _ _ _ _ $$ Hres
  iunfold txnCommitResult at Hres
  icases Hres with (%Hne | ⟨%Heq, %r, %s0, #Hresp, #Hr, %Hrr, #Hts⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    (try wp_auto)
    wp_apply wp_panic
    iapply HΦ
    iapply stmRet_abort _ (by simp)
  subst Heq
  have hm : ({ model := { cmps := ms, thenOps := ops, elseOps := [] }, cif := true, cthen := true, celse := false } : TxnBuild).model =
      ({ cmps := ms, thenOps := ops, elseOps := [] } : TxnModel) := rfl
  rw [hm]
  obtain ⟨Hlin, Hr0, Hrmax, Hwf0⟩ := Hrr
  ihave #Hresp' := Hresp
  iunfold txnRespAt at Hresp'
  icases Hresp' with ⟨%hdr, %rsl, %ps, -, -, -, #HSucc, -⟩
  (try wp_auto)
  cases hok : (runTxn r s0 { cmps := ms, thenOps := ops, elseOps := [] }).1
  · have hok' : ms.all (cmpHolds s0) = false := hok
    rw [hok']
    (try wp_auto)
    iapply HΦ
    iapply stmRet_ret
    iframe
    ileft; ipureintro; rfl
  · have hok' : ms.all (cmpHolds s0) = true := hok
    rw [hok']
    (try wp_auto)
    iapply HΦ
    iapply stmRet_ret
    iframe
    by_cases hnull : resp = null
    · ileft; ipureintro; exact hnull
    iright
    isplitr
    · ipureintro; exact hnull
    iapply stmCommit_outcome pfx lvl lo st resp ms ops [] r s0 hok Hms Hops.2 Hlin Hr0 Hrmax Hwf0
    rw [hok]
    iframe Hfacts Hr Hts Hresp

end proof

end concurrency
end EtcdGrove
end Perennial
