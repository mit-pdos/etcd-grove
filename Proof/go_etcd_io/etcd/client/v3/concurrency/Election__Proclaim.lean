/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Proclaim.lean`. Lean-first (no Rocq
counterpart).

The guarded put (`proclaimTxn`): if the guard held, the transaction wrote (a put), and etcd's
states at `r - 1` and `r` are a `ProclaimStep`; otherwise it wrote nothing and the key was not there
with that create revision (`createGuard_false`). For a key outside the prefix, the
`txnAnyResult` triple.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Proclaim
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Lease
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.WithLease
public import Spec.go_etcd_io.etcd.client.v3.OpPut

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
theorem createGuard_false (pfx key : GoString) (rev : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf pfx s) (h : cmpHolds s (createGuard key rev) = false) :
    ¬ HasKeyAt key rev s := by
  rintro ⟨w, hw, hk, hc⟩
  have hf := filter_key_single s hwf.1 key (fun v => inRange key [] v.key)
    (fun v => by simp [inRange]) w hw hk
  simp [cmpHolds, createGuard, compareM, cmpKeyM, hf, cmpKv, int64Cmp, cmpSign, CmpOp.holds,
    hc] at h

/-- `OpPut(key, val, WithLease(id))` in a transaction. -/
theorem putValOp_txnOpOf (key val : GoString) (id : w64) :
    txnOpOf (opPutModel key val [withLeaseM id]) = some (.put key val id) := by
  simp [opPutModel, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero, txnOpOf]

theorem putValOp_not_panics (key val : GoString) (id : w64) :
    ¬ (opPutModel key val [withLeaseM id]).putPanics := by
  simp [opPutModel, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero,
    OpFull.putPanics]

theorem proclaimTxn_under (pfx key : GoString) (rev : w64) (val : GoString) (id : w64)
    (hk : pfx <+: key) : (proclaimTxn key rev val id).Under pfx := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [proclaimTxn, List.mem_singleton] at hc
    subst hc
    exact keyRangeUnder_key pfx key hk
  · intro op hop
    simp only [proclaimTxn, List.mem_singleton] at hop
    subst hop
    exact hk
  · intro op hop
    simp [proclaimTxn] at hop

theorem proclaimTxn_run (key : GoString) (rev : w64) (val : GoString) (id r : w64)
    (s : List EtcdKv) :
    (cmpHolds s (createGuard key rev) = true ∧
      runTxn r s (proclaimTxn key rev val id) = (true, putKv r key val id s, [.put])) ∨
    (cmpHolds s (createGuard key rev) = false ∧
      runTxn r s (proclaimTxn key rev val id) = (false, s, [])) := by
  cases hok : cmpHolds s (createGuard key rev)
  · right; refine ⟨rfl, ?_⟩
    simp [runTxn, proclaimTxn, TxnModel.branch, hok, runOps]
  · left; refine ⟨rfl, ?_⟩
    simp [runTxn, proclaimTxn, TxnModel.branch, hok, runOps, applyTxnOp]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Election.Proclaim.wp_proof (hCl : Session.Client.spec (GF := GF) (hG := hG))
    (hCR : EtcdGrove.CreateRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hLe : Session.Lease.spec (GF := GF) (hG := hG))
    (hWL : EtcdGrove.WithLease.spec (GF := GF) (hG := hG))
    (hPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG)) :
    Election.Proclaim.spec (GF := GF) (hG := hG) := by
  intro e s γ client id pfx st ctx cs val lo
  rcases st with ⟨key, rev, sess, hdr0⟩
  wp_start as ⟨#He, Hst, #Hctx, #Hlo⟩
  ihave #He' := He
  iunfold isElection at He'
  icases He' with ⟨#Hes, #Hepfx, %Hpfx, #Hsess, #Hcl⟩
  ihave Hci : (concurrencyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, -, -, ⟨%eNL, #HeNL⟩, -⟩
  unfold electionState
  icases Hst with ⟨Hk, Hrv, Hls, Hh, %Hss⟩
  simp only at Hss ⊢
  wp_auto
  wp_if_destruct
  · -- no leader session
    iapply HΦ
    iright; ileft
    isplitr
    · unfold isPkgErr; iframe HeNL; ipureintro; simp
    ileft
    isplitr
    · ipureintro; simp
    iframe
    ipureintro; simp
  have Hnn : sess ≠ null := Hif
  obtain rfl : sess = s := Hss.resolve_left Hnn
  wp_apply hCl sess γ client id $$ [$Hpkg $Hsess]
  (try wp_auto)
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hCR key $$ [$Hcv] as %c0 #Hc0
  (try wp_auto)
  wp_apply hCmp c0 _ go!"=" .eq _ (.num rev) $$ [$Hcv $Hc0] as %c1 #Hc1
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
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
  wp_apply_raw HIf $$ %TxnBuild.empty %_ %([compareM (cmpKeyM .create key) .eq (.num rev)] : List CmpModel) [$HB]
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
  wp_apply hLe sess γ client id $$ [$Hpkg $Hsess]
  (try wp_auto)
  wp_apply hWL id $$ [$Hcv] as %f0 #Hf0
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f0])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  (try wp_auto)
  ihave #Hopts : optsAt (GF := GF) _ [withLeaseM id] $$ []
  · unfold optsAt
    iexists [f0]
    iframe Hslo
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf Hg; subst Hf Hg; iexact Hf0
    · simp at Hf
  wp_apply hPut key val _ [withLeaseM id] $$ [$Hcv $Hopts] as %opPut #HopPut
  · ipureintro; exact putValOp_not_panics key val id
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opPut])
  isplitr
  · ipureintro; rfl
  iintro %slT ⟨HslT, -⟩
  ipersist HslT
  (try wp_auto)
  wp_apply_raw HThen $$ %_ %_ %([opPutModel key val [withLeaseM id]] : List OpFull) %([.put key val id] : List TxnOp) [$HB]
  · isplitl
    · unfold opsAt
      iexists [opPut]
      iframe HslT
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %v %o %Hv %Ho
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho; iexact HopPut
      · simp at Hv
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      simp only [List.map_cons, List.map_nil, putValOp_txnOpOf]
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv B _ ({ model := proclaimTxn key rev val id, cif := true, cthen := true, celse := false } : TxnBuild) (by rfl) $$ HB
  by_cases Hk : pfx <+: key
  · wp_apply HCommit $$ %({ model := proclaimTxn key rev val id, cif := true, cthen := true, celse := false } : TxnBuild) %lo [$HB $Hlo] as %resp %err Hres
    · ipureintro; exact proclaimTxn_under pfx key rev val id Hk
    ihave #Hres := txnCommitResultTok_result _ _ _ _ _ $$ Hres
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
      · ipureintro; exact Hne
      iframe
      ipureintro; simp
    subst Heq
    have hm : ({ model := proclaimTxn key rev val id, cif := true, cthen := true, celse := false } :
        TxnBuild).model = proclaimTxn key rev val id := rfl
    rw [hm]
    rcases proclaimTxn_run key rev val id r s0 with ⟨hok, e⟩ | ⟨hok, e⟩
    · rw [e]
      simp only [txnWrote, List.any_cons, TxnOpResult.wrote, Bool.true_or]
      unfold txnStates
      simp only [↓reduceIte]
      icases Hts with ⟨#Hs0, #Hs1⟩
      iunfold txnRespAt at Hresp
      icases Hresp with ⟨%hdr, %rsl, %ps, #HH, %Hhdr, #HRev, #HSucc, -⟩
      wp_auto
      iapply HΦ
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hnn⟩
      iexists hdr
      iframe
      isplitr
      · ipureintro; simp
      iright
      iexists r
      iframe Hr
      isplitr
      · unfold hdrRevAt; iframe HRev; ipureintro; exact Hhdr
      isplitr
      · unfold proclaimedAt
        iexists s0, putKv r key val id s0
        iframe Hs0 Hs1
        ipureintro; exact ⟨hok, rfl⟩
      ipureintro; exact Hrr.1 rfl
    · rw [e]
      simp only [txnWrote, List.any_nil]
      unfold txnStates
      simp only [Bool.false_eq_true, ↓reduceIte]
      iunfold txnRespAt at Hresp
      icases Hresp with ⟨%hdr, %rsl, %ps, #HH, %Hhdr, #HRev, #HSucc, -⟩
      wp_auto
      iapply HΦ
      iright; ileft
      isplitr
      · unfold isPkgErr; iframe HeNL; ipureintro; simp
      iright
      isplitr
      · ipureintro; exact Hnn
      iframe
      isplitr
      · ipureintro; simp
      iright
      iexists r
      iframe Hr
      isplitr
      · unfold notLeaderAt
        iexists s0
        iframe Hts
        ipureintro; exact createGuard_false pfx key rev s0 Hrr.2.2.2 hok
      ipureintro; exact Hrr.1 rfl
  · wp_apply HCommitAny $$ %({ model := proclaimTxn key rev val id, cif := true, cthen := true, celse := false } : TxnBuild) [$HB] as %resp %err #Hres
    iunfold txnAnyResult at Hres
    icases Hres with (%Hne | ⟨%Heq, %hdr, %ok, #HH, #HSucc⟩)
    · obtain ⟨g, rfl⟩ : ∃ g, err = GoInterface.ok g := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok g => exact ⟨g, rfl⟩
      wp_auto
      iapply HΦ
      iright; iright
      isplitr
      · ipureintro; exact Hne
      iframe
      ipureintro; simp
    subst Heq
    wp_auto
    cases ok
    · wp_auto
      iapply HΦ
      iright; ileft
      isplitr
      · unfold isPkgErr; iframe HeNL; ipureintro; simp
      iright
      isplitr
      · ipureintro; exact Hnn
      iframe
      isplitr
      · ipureintro; simp
      ileft; ipureintro; exact Hk
    · wp_auto
      iapply HΦ
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hnn⟩
      iexists hdr
      iframe
      isplitr
      · ipureintro; simp
      ileft; ipureintro; exact Hk

end proof

end concurrency
end EtcdGrove
end Perennial
