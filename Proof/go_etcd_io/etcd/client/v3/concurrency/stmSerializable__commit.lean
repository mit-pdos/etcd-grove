/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stmSerializable__commit.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__commit
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__gets
public import Spec.go_etcd_io.etcd.client.v3.concurrency.writeSet__puts
public import Spec.go_etcd_io.etcd.client.v3.concurrency.readSet__add
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem stmSerializable.commit.wp_proof
    (hGets : stmSerializable.gets.spec (GF := GF) (hG := hG))
    (hPuts : writeSet.puts.spec (GF := GF) (hG := hG))
    (hAdd : readSet.add.spec (GF := GF) (hG := hG)) :
    stmSerializable.commit.spec (GF := GF) (hG := hG) := by
  intro lvl p pfx st lo
  wp_start as ⟨Hst, #Hlo, %Hser⟩
  have hb : stmBase lvl p = structFieldRef stmSerializable go!"stm" p := by simp [stmBase, Hser]
  unfold stmState stmStale
  rw [hb]
  simp only [Hser, ite_true]
  icases Hst with ⟨#Henv, Hrs, Hws, ⟨%gs, Hopts, %Hgs⟩, #Hcf, ⟨%pre, Hpre, %Hpre⟩⟩
  wp_auto
  wp_apply hGets p pfx st.reads $$ [$Hpkg $Hrs] as %ksl %osl ⟨Hrs, %ks, #Hks, #Hosl, %Hksl⟩
  ihave #Henv' := Henv
  iunfold stmEnv at Henv'
  icases Henv' with ⟨%c, %ctx, %cs, #Hc, #Hcl, #Hctx, #Hcs⟩
  ihave #Hcl' := Hcl
  iunfold isEtcdSTMClient at Hcl'
  icases Hcl' with ⟨%kv, %cctx, %ccs, #HKV, #HTxn, -, -, -⟩
  ihave #Hcf' := Hcf
  iunfold stmConflictsAt at Hcf'
  icases Hcf' with ⟨%f, #Hf, #Hfs⟩
  iunfold stmRsetOwn at Hrs
  icases Hrs with ⟨%rm, %rsMap, Hrf, Hrm, #Hreads⟩
  iunfold stmWsetOwn at Hws
  icases Hws with ⟨%wm, %wsMap, Hwf, Hwm, #Hwrites⟩
  wp_method_call
  wp_auto
  wp_apply hPuts wm (DFrac.own 1) pfx wsMap st.writes $$ [$Hpkg $Hwm $Hwrites] as %wsl ⟨Hwm, %os, %ops, #Hos, %Hops⟩
  ihave Hrs : stmRsetOwn pfx (structFieldRef stmSerializable go!"stm" p) st.reads $$ [Hrf Hrm]
  · iunfold stmRsetOwn; iexists rm, rsMap; iframe; iframe Hreads
  ihave Hws : stmWsetOwn pfx (structFieldRef stmSerializable go!"stm" p) st.writes $$ [Hwf Hwm]
  · iunfold stmWsetOwn; iexists wm, wsMap; iframe; iframe Hwrites
  iunfold conflictsSpec at Hfs
  wp_apply Hfs $$ %st.reads %st.writes [$Hrs $Hws] as %csl ⟨Hrs, Hws, %ms, #Hms, %Hms⟩
  iunfold isEtcdTxnKV at HTxn
  wp_apply HTxn $$ %ctx %cs [$Hcs] as %t ⟨%B, HB, #HBs⟩
  iunfold txnBuilderSpec at HBs
  icases HBs with ⟨#HIf, #HThen, #HElse, #HCommit, -⟩
  wp_apply_raw HIf $$ %TxnBuild.empty %csl %ms [$HB]
  · iframe Hms; ipureintro; simp [TxnBuild.empty]
  inext
  iintro HB
  (try wp_auto)
  wp_apply_raw HThen $$ %_ %wsl %os %ops [$HB]
  · iframe Hos; ipureintro; exact ⟨Hops.1, rfl, rfl⟩
  inext
  iintro HB
  (try wp_auto)
  wp_apply_raw HElse $$ %_ %osl %(ks.map keyOp) %((ks.map keyOp).map TxnOp.get) [$HB]
  · iframe Hosl; ipureintro; exact ⟨keyOps_txnOpOf ks, rfl⟩
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv B _ ({ model := { cmps := ms, thenOps := ops, elseOps := (ks.map keyOp).map TxnOp.get }, cif := true, cthen := true, celse := true } : TxnBuild) (by simp [TxnBuild.empty, TxnModel.empty]) $$ HB
  ihave #Hfacts := readsAt_readFacts pfx rsMap st.reads $$ Hreads
  ihave %Hru := readFacts_under pfx st.reads $$ Hfacts
  ihave %Hwu := writesAt_under pfx wsMap st.writes $$ Hwrites
  have hks : ∀ k ∈ ks, pfx <+: k := by
    intro k hk
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 ((Hksl.2 k).1 hk)
    exact Hru k e he
  wp_apply HCommit $$ %({ model := { cmps := ms, thenOps := ops, elseOps := (ks.map keyOp).map TxnOp.get }, cif := true, cthen := true, celse := true } : TxnBuild) %lo [$HB $Hlo] as %resp %err Hres
  · ipureintro; exact stmTxn_under pfx lvl Hru Hwu Hms Hops.2 (keyOps_under pfx ks hks)
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
  have hm : ({ model := { cmps := ms, thenOps := ops, elseOps := (ks.map keyOp).map TxnOp.get }, cif := true, cthen := true, celse := true } : TxnBuild).model =
      ({ cmps := ms, thenOps := ops, elseOps := (ks.map keyOp).map TxnOp.get } : TxnModel) := rfl
  rw [hm]
  obtain ⟨Hlin, Hr0, Hrmax, Hwf0⟩ := Hrr
  ihave #Hresp' := Hresp
  iunfold txnRespAt at Hresp'
  icases Hresp' with ⟨%hdr, %rsl, %ps, -, -, -, #HSucc, #HRs, #Hps, %Hlens, #Hops⟩
  (try wp_auto)
  cases hok : (runTxn r s0 { cmps := ms, thenOps := ops, elseOps := (ks.map keyOp).map TxnOp.get }).1
  · have hok' : ms.all (cmpHolds s0) = false := hok
    rw [hok']
    have hrun : runTxn r s0 { cmps := ms, thenOps := ops, elseOps := (ks.map keyOp).map TxnOp.get } =
        (false, s0, (ks.map keyOp).map (fun o => TxnOpResult.range (rangeSel s0 o) (rangeIn s0 o).length)) := by
      simp only [runTxn, hok', TxnModel.branch, Bool.false_eq_true, ite_false, runOps_gets]
    rw [hrun] at Hlens
    rw [hrun, txnWrote_gets]
    simp only [TxnModel.branch, Bool.false_eq_true, ite_false] at Hlens ⊢
    have hlen : ps.length = ks.length := by simp at Hlens; omega
    ihave #Hs := txnStates_noWrite pfx r s0 s0 $$ Hts
    ihave ⟨%es, %Hes, #Hrd⟩ := elseResps_reads pfx r s0 ks ps Hwf0 hks hlen $$ [Hs Hops]
    · isplitr
      · imodintro; iexact Hs
      · iexact Hops
    iunfold stmRsetOwn at Hrs
    icases Hrs with ⟨%rm2, %rsMap2, Hrf, Hrm, #Hreads2⟩
    iunfold stmPreOwn at Hpre
    icases Hpre with ⟨%pm, %preMap, Hpf, -, -⟩
    iunfold stmOptsOwn at Hopts
    icases Hopts with ⟨%gsl, Hgf, -⟩
    iclear HTxn HIf HThen HElse HCommit Hfs
    wp_auto
    wp_method_call
    wp_auto
    wp_apply hAdd rm2 pfx rsMap2 st.reads ksl ks resp rsl ps es $$ [$Hpkg $Hrm $Hreads2 $Hks $HRs $Hps $Hrd] as ⟨%rsMap3, Hrm, #Hreads3⟩
    · ipureintro; omega
    iapply HΦ
    iapply stmRet_ret
    isplitl
    · iunfold stmWsetOwn at Hws
      icases Hws with ⟨%wm', %wsMap', Hwf', -, -⟩
      iframe Henv Hcf
      isplitl [Hrf]
      · iexists rm2; iframe
      isplitl [Hwf']
      · iexists wm'; iframe
      isplitl [Hgf]
      · iexists ([] : List (OpFull → OpFull))
        isplitl
        · unfold stmOptsOwn
          iexists slice.nil
          iframe Hgf
          iapply optsAt_nil
        · ipureintro; simp [GetOptsOk, Hser]
      · iexists readsAdd st.reads (ks.zip es)
        unfold stmPreOwn
        iexists rm2, rsMap3
        iframe Hpf Hrm Hreads3
    · ileft; ipureintro; rfl
  · have hok' : ms.all (cmpHolds s0) = true := hok
    rw [hok']
    (try wp_auto)
    iapply HΦ
    iapply stmRet_ret
    isplitl
    · iunfold stmRsetOwn at Hrs
      icases Hrs with ⟨%rm', %rsMap', Hrf', -, -⟩
      iunfold stmWsetOwn at Hws
      icases Hws with ⟨%wm', %wsMap', Hwf', -, -⟩
      iframe Henv Hcf
      isplitl [Hrf']
      · iexists rm'; iframe
      isplitl [Hwf']
      · iexists wm'; iframe
      isplitl [Hopts]
      · iexists gs; iframe; ipureintro; exact Hgs
      · iexists pre; iframe
    by_cases hnull : resp = null
    · ileft; ipureintro; exact hnull
    iright
    isplitr
    · ipureintro; exact hnull
    iapply stmCommit_outcome pfx lvl lo st resp ms ops _ r s0 hok Hms Hops.2 Hlin Hr0 Hrmax Hwf0
    rw [hok]
    iframe Hfacts Hr Hts Hresp

end proof

end concurrency
end EtcdGrove
end Perennial
