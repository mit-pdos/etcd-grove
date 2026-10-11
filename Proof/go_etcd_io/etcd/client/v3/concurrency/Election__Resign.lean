/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Resign.lean`. Lean-first (no Rocq
counterpart).

The guarded delete (`resignTxn`): if the guard held, the key is deleted (as a plain delete,
`deleteTxn_absent`); otherwise the key was not there with that create revision
(`createGuard_false`). For a key outside the prefix, the `txnAnyResult` triple.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Resign
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.OpDelete

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

private theorem B_conv {PROP : Type _} [BI PROP] (B : TxnBuild → PROP) (b b' : TxnBuild)
    (h : b = b') : B b ⊢ B b' := h ▸ .rfl

/-- A failed guard `CreateRevision(key) = rev` on a sorted state: `key` is not there with create
revision `rev`. -/
theorem createGuard_false_resign (pfx key : GoString) (rev : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf pfx s) (h : cmpHolds s (createGuard key rev) = false) :
    ¬ HasKeyAt key rev s := by
  rintro ⟨w, hw, hk, hc⟩
  have hf := filter_key_single s hwf.1 key (fun v => inRange key [] v.key)
    (fun v => by simp [inRange]) w hw hk
  simp [cmpHolds, createGuard, compareM, cmpKeyM, hf, cmpKv, int64Cmp, cmpSign, CmpOp.holds,
    hc] at h

theorem deleteOp_txnOpOf (key : GoString) :
    txnOpOf (opDeleteModel key []) = some (.delete (opDeleteModel key [])) := by
  simp [opDeleteModel, opFold, OpFull.deleteInit, OpFull.newOp, OpModel.zero, txnOpOf]

theorem resignTxn_under (pfx key : GoString) (rev : w64) (hk : pfx <+: key) :
    (resignTxn key rev).Under pfx := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [resignTxn, List.mem_singleton] at hc
    subst hc
    exact keyRangeUnder_key pfx key hk
  · intro op hop
    simp only [resignTxn, List.mem_singleton] at hop
    subst hop
    show KeyRangeUnder pfx (opDeleteModel key []).key (opDeleteModel key []).base.rangeEnd
    rw [(deleteOp_fields key).1, (deleteOp_fields key).2]
    exact keyRangeUnder_key pfx key hk
  · intro op hop
    simp [resignTxn] at hop

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- After `Resign`'s transaction, the key is not there with create revision `rev`. -/
theorem resignTxn_notLeader (pfx key : GoString) (rev r : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf pfx s) :
    txnStates (GF := GF) pfx r s (runTxn r s (resignTxn key rev)).2.1
      (txnWrote (runTxn r s (resignTxn key rev)).2.2) ⊢ notLeaderAt pfx key rev r := by
  cases hok : cmpHolds s (createGuard key rev)
  · have e : runTxn r s (resignTxn key rev) = (false, s, []) := by
      simp [runTxn, resignTxn, TxnModel.branch, hok, runOps]
    rw [e]
    unfold txnStates notLeaderAt
    simp only [txnWrote, List.any_nil, Bool.false_eq_true, ↓reduceIte]
    iintro #H
    iexists s
    iframe H
    ipureintro; exact createGuard_false_resign pfx key rev s hwf hok
  · have e : (runTxn r s (resignTxn key rev)).2 =
        (runTxn r s (deleteTxn (opDeleteModel key []))).2 := by
      simp [runTxn, resignTxn, deleteTxn, TxnModel.branch, hok]
    rw [e]
    iintro #H
    ihave #Habs := deleteTxn_absent pfx key r s $$ H
    unfold etcdAbsent notLeaderAt
    icases Habs with ⟨%s', #Hs', %Ha⟩
    iexists s'
    iframe Hs'
    ipureintro
    rintro ⟨w, hw, hk, -⟩
    exact Ha w hw hk

end lemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Election.Resign.wp_proof (hCl : Session.Client.spec (GF := GF) (hG := hG))
    (hCR : EtcdGrove.CreateRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hDel : EtcdGrove.OpDelete.spec (GF := GF) (hG := hG)) :
    Election.Resign.spec (GF := GF) (hG := hG) := by
  intro e s γ client id pfx st ctx cs lo
  wp_start as ⟨#He, Hst, #Hctx, #Hlo⟩
  ihave #He' := He
  iunfold isElection at He'
  icases He' with ⟨#Hes, #Hepfx, %Hpfx, #Hsess, #Hcl⟩
  unfold electionState
  icases Hst with ⟨Hk, Hrv, Hls, Hh, %Hsess⟩
  wp_auto
  wp_if_destruct
  · -- no leader session
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact ⟨Hif, rfl⟩
    iframe
    ipureintro; exact Hsess
  have Hnn : st.sess ≠ null := Hif
  wp_apply hCl s γ client id $$ [$Hpkg $Hsess]
  (try wp_auto)
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hCR st.key $$ [$Hcv] as %c0 #Hc0
  (try wp_auto)
  wp_apply hCmp c0 _ go!"=" .eq _ (.num st.rev) $$ [$Hcv $Hc0] as %c1 #Hc1
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
  (try wp_auto)
  ihave #Hnil := optsAt_nil (GF := GF)
  wp_apply hDel st.key slice.nil [] $$ [$Hcv $Hnil] as %opD #HopD
  · ipureintro; exact deleteOp_not_panics st.key
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opD])
  isplitr
  · ipureintro; rfl
  iintro %slT ⟨HslT, -⟩
  ipersist HslT
  (try wp_auto)
  wp_apply wp_slice_literal (l := [c1])
  isplitr
  · ipureintro; rfl
  iintro %slC ⟨HslC, -⟩
  ipersist HslC
  ihave #Hcl' := Hcl
  iunfold isEtcdMutexClient at Hcl'
  icases Hcl' with ⟨%kv, %wt, %cctx, %ccs, #HKV, -, -, -, -, #HTxn, -, -⟩
  (try wp_auto)
  iunfold isEtcdTxnKV at HTxn
  wp_apply HTxn $$ %ctx %cs [$Hctx] as %t ⟨%B, HB, #HBs⟩
  iunfold txnBuilderSpec at HBs
  icases HBs with ⟨#HIf, #HThen, -, #HCommit, #HCommitAny⟩
  wp_apply_raw HIf $$ %TxnBuild.empty %_ %([compareM (cmpKeyM .create st.key) .eq (.num st.rev)] : List CmpModel) [$HB]
  · isplitl
    · unfold cmpsAt
      iexists [c1]
      iframe HslC
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %c %mm %Hc %Hmm
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hc Hmm; subst Hc Hmm; iexact Hc1
      · simp at Hc
    · ipureintro; simp [TxnBuild.empty]
  inext
  iintro HB
  (try wp_auto)
  wp_apply_raw HThen $$ %_ %_ %([opDeleteModel st.key []] : List OpFull) %([.delete (opDeleteModel st.key [])] : List TxnOp) [$HB]
  · isplitl
    · unfold opsAt
      iexists [opD]
      iframe HslT
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %v %o %Hv %Ho
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho; iexact HopD
      · simp at Hv
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      simp only [List.map_cons, List.map_nil, deleteOp_txnOpOf]
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv B _ ({ model := resignTxn st.key st.rev, cif := true, cthen := true, celse := false } : TxnBuild) (by rfl) $$ HB
  by_cases Hk : pfx <+: st.key
  · wp_apply HCommit $$ %({ model := resignTxn st.key st.rev, cif := true, cthen := true, celse := false } : TxnBuild) %lo [$HB $Hlo] as %resp %err #Hres
    · ipureintro; exact resignTxn_under pfx st.key st.rev Hk
    iunfold txnCommitResult at Hres
    icases Hres with (%Hne | ⟨%Heq, %r, %s0, #Hresp, #Hr, %Hrr, #Hts⟩)
    · obtain ⟨g, rfl⟩ : ∃ g, err = GoInterface.ok g := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok g => exact ⟨g, rfl⟩
      wp_auto
      iapply HΦ
      iright; iright
      isplitr
      · ipureintro; exact ⟨Hnn, Hne⟩
      iframe
      ipureintro; simp
    subst Heq
    iunfold txnRespAt at Hresp
    icases Hresp with ⟨%hdr, %rsl, %ps, #HH, %Hhdr, #HRev, -⟩
    ihave #Hnl := resignTxn_notLeader pfx st.key st.rev r s0 Hrr.2.2.2 $$ Hts
    wp_auto
    iapply HΦ
    iright; ileft
    isplitr
    · ipureintro; exact ⟨Hnn, rfl⟩
    iexists hdr
    iframe
    isplitr
    · ipureintro; simp
    iright
    iexists r
    iframe Hr Hnl
    isplitr
    · unfold hdrRevAt; iframe HRev; ipureintro; exact Hhdr
    ipureintro; exact Hrr.1 rfl
  · wp_apply HCommitAny $$ %({ model := resignTxn st.key st.rev, cif := true, cthen := true, celse := false } : TxnBuild) [$HB] as %resp %err #Hres
    iunfold txnAnyResult at Hres
    icases Hres with (%Hne | ⟨%Heq, %hdr, %ok, #HH, -⟩)
    · obtain ⟨g, rfl⟩ : ∃ g, err = GoInterface.ok g := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok g => exact ⟨g, rfl⟩
      wp_auto
      iapply HΦ
      iright; iright
      isplitr
      · ipureintro; exact ⟨Hnn, Hne⟩
      iframe
      ipureintro; simp
    subst Heq
    wp_auto
    iapply HΦ
    iright; ileft
    isplitr
    · ipureintro; exact ⟨Hnn, rfl⟩
    iexists hdr
    iframe
    isplitr
    · ipureintro; simp
    ileft; ipureintro; exact Hk

end proof

end concurrency
end EtcdGrove
end Perennial
