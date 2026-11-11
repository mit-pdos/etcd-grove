/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart). (Strict M1, 2026-11-05: over
the lessor's `revokeClause`, `lessor.Revoke.spec`'s shape, its one update built by the server's
builders, `envAus`, for a live lease only: otherwise the writer's half is kept, decided by the
coordinator, 2026-11-06; `notes/mvcc-migration/server.md`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- The backend's post of a KV method (`kvPost` at the chain `backend`: no chain resources, the
trivial classes). -/
theorem apply.kvPost_backend {E : apply.AEnv GF} {a : GoInterface}
    {info : go_etcd_io.etcd.server.v3.auth.AuthInfo} {rq : apply.IRRModel} {log : mvcc.Log}
    {R : apply.Outcome → IProp GF} {Pre Post : IProp GF} :
    (∃ oc : apply.Outcome, ⌜apply.chainStep apply.backendStep .backend rq log oc⌝ ∗ R oc ∗
      apply.kvOwn E (oc.logAfter log) ∗ apply.chainRes .backend a info ∗ (Post ∨ Pre)) ⊢
      apply.kvPost E .backend a info rq log R Pre Post := by
  iintro ⟨%oc, %H, HR, Hkv, Hres, HPP⟩
  unfold apply.kvPost
  iexists oc
  iframe HR Hkv Hres HPP
  isplitr
  · ipureintro; exact H
  isplitr
  · iapply apply.chainClass_backend
  simp only [apply.chainLeaseClass]; itrivial

/-- **`a.LeaseRevoke(lc)`** (the lease-revoke plan, 2026-10-31; until then vacuous, D14h): the
lessor's `Revoke` (the contract's clause), then a response with `newHeader()`'s header. -/
theorem apply.applierV3backend.LeaseRevoke.wp_proof
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.LeaseRevoke.spec (GF := GF) (hG := hG) := by
  intro E p r rq id log T rs Pre Q Post info
  -- the proof over the API (`revokeClause`, `envAus`) with `lean`'s revoke-open (`revokeRes`'s
  -- revocable lessor and half of the live set `T`, the post by the outcome, X6's answer)
  wp_start as ⟨#Hb, Htt, Hpre⟩
  iunfold apply.revokePre at Hpre
  icases Hpre with ⟨%Hrq, #Hcp, #Hr, Hpre, Hrr⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨⟨%c, Hw⟩, Hlive, Hard, Hres, %B, Hbk, #Hhk, Htie, Hcs⟩
  iunfold apply.revokeRes at Hrr
  icases Hrr with ⟨Hrdat, #Hrev, HltT, HRO, %Hlm⟩
  have Hlgt : E.lg = true := apply.AEnv.lg_true_of_lm (by rw [Hlm]; decide)
  iunfold apply.leasesLive at Hlive
  icases Hlive with ⟨%L, #Hknown, Hu, HltL⟩
  ihave %HLT := apply.ltHalf_agree E L T Hlgt $$ [HltL HltT]
  · iframe HltL HltT
  subst HLT
  iunfold lease.lessorUser at Hu
  icases Hu with ⟨Hown, Hlrd, Hrvk⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨#Hlg, -, -, #Haus, #Hle, -⟩
  iunfold apply.envAus at Haus
  icases Haus with ⟨#HauB, -, #HauE, -, #Hfacts, -⟩
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨-, %li, %Hli, -, #HRv, -, -⟩
  iunfold apply.leaseRevokeIs at Hr
  icases Hr with ⟨%Hrn, #HrID⟩
  have hstep : apply.backendStep rq log (.applied (apply.revokeLog log id) false) := by
    unfold apply.backendStep; rw [Hrq.2.1]; exact ⟨id, Hrq.1, rfl⟩
  ihave Hnx := apply.certPre_backend_applied E rq log (apply.revokeLog log id) false hstep $$ Hcp
  -- the writer's facts: its state reachable
  imod Hfacts $$ %log %c Hw with ⟨Hw, -, -, -, %Hreach⟩
  -- the revocation's update, for a live lease only: the deleter's begin, its payload the end of
  -- the lease's deletions; otherwise the writer's half kept
  ihave Hau2 : (if decide (id ∈ L) then srvApi.auBegin E.γ (srvApi.stAt log c)
      (srvApi.auEnd E.γ (srvApi.stAt log c)
        (mvcc.leaseDels (mvcc.stateAfter (srvApi.stAt log c).log) id)
        (srvApi.wSt E.γs (apply.revokeLog log id) c)) else iprop(True)) ∗
      (if decide (id ∈ L) then iprop(True) else srvApi.wSt E.γs log c) $$ [Hw Hnx]
  · by_cases hid : id ∈ L
    · simp only [hid, decide_true, ↓reduceIte]
      isplitl
      · iapply HauB $$ %log %c %_ Hw
        iintro Hw
        rw [show (srvApi.stAt log c).log = log from rfl]
        iapply HauE $$ %log %c %_ Hw Hnx
      itrivial
    · simp only [hid, decide_false, Bool.false_eq_true, ↓reduceIte]
      isplitr
      · itrivial
      iexact Hw
  icases Hau2 with ⟨Hau, Hwr⟩
  have hsl : (srvApi.stAt log c).log = log := rfl
  ihave Hown : lease.leaseOwn (mvcc.api.mvccLeases E.γ) L
      (mvcc.leaseItemsOf (mvcc.stateAfter (srvApi.stAt log c).log)) $$ [Hown]
  · rw [hsl]; iexact Hown
  ihave #Hknown0 : txn.leasesKnown L (mvcc.stateAfter (srvApi.stAt log c).log) $$ []
  · rw [hsl]; iexact Hknown
  iStructNamed Hopts
  wp_auto
  rw [Hli]
  wp_auto
  iunfold apply.revokeClause at HRv
  iunfold apply.rdHeld at Hrdat
  iunfold apply.applyTok at Htt
  icases Htt with Hmr
  wp_apply HRv $$ [$Hmr $Hrdat $Hrev $Hbk $Hhk $Htie $Hcs $Hau $Hown $Hrvk $Hknown0 $HRO]
    as %err ⟨Hmr, Hrdat, Hbk, Htie, #Herr, Hcase⟩
  · ipureintro
    exact ⟨rfl, Hrq.2.2.2, Hreach⟩
  ihave Htt : apply.applyTok E $$ [Hmr]
  · iunfold apply.applyTok; iframe Hmr
  icases Hcase with
    (⟨⟨%Hnf, %Hnd⟩, ⟨%e, #He, %Hee⟩, HPre, Hown, Hrvk, -, HRO⟩ |
     ⟨%Hok, Hw, HPost, Hown, Hrvk, #Hknown', HRO⟩)
  · -- not live: the error, nothing changed (the live set's filter the identity)
    -- the writer's half, kept: no update was taken for a lease not live
    ihave Hw : srvApi.wSt E.γs log c $$ [Hwr]
    · simp only [Hnf, decide_false, Bool.false_eq_true, ↓reduceIte]
      iexact Hwr
    have hlog : apply.revokeLog log id = log := by
      try simp only [srvApi.stAt] at Hnd
      unfold apply.revokeLog; rw [Hnd]; rfl
    have hflt : L.filter (· != id) = L :=
      List.filter_eq_self.2 (fun a ha => by
        have : a ≠ id := fun h => Hnf (h ▸ ha)
        simpa using this)
    (try wp_auto)
    wp_apply (hHdr E p log c) $$ [$Hb $Htt $Hw] as %h ⟨Htt, Hw, %Hh, -⟩
    icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨Hr0, %Hnn⟩
    iStructNamed Hr0
    iapply HΦ
    iframe Htt
    iapply apply.kvPost_backend
    iexists (.applied (apply.revokeLog log id) false)
    isplitr
    · ipureintro; exact hstep
    simp only [apply.revokeOutcomeIs, apply.Outcome.logAfter]
    rw [hlog]
    isplitl [Hrdat HltT HRO]
    · isplitr
      · isplitr
        · ipureintro; exact Hnn
        iframe Herr
        iunfold apply.revokeErrIs
        iright; iexists e; iframe He; ipureintro; exact Hee
      iunfold apply.revokeResAfter
      rw [apply.revokeIds_applied rq id _ _ L Hrq.2.1 Hrq.1, hflt,
        apply.revokeRest_applied L rq id _ _ rs Hrq.2.1 Hrq.1, if_neg Hnf]
      iframe Hrev HltT HRO
      isplitl [Hrdat]
      · iunfold apply.rdHeld; iexact Hrdat
      iapply apply.revokeAnswer_err E rq _ err (by rw [Hee]; intro h; cases h)
    isplitr [HPre]
    · iapply (apply.kvOwn_of_split E log B c)
      iframe Hw Htie
      iunfold apply.kvRest
      iframe Hbk Hhk Hard
      iunfold apply.leasesLive
      iexists L
      iframe Hknown HltL
      iunfold lease.lessorUser
      simp only [srvApi.stAt]
      iframe
    isplitr
    · simp only [apply.chainRes]; itrivial
    iright; iexact HPre
  · -- live: the lease's keys deleted, the lease gone from both halves of the live set
    simp only [srvApi.stAt] at *
    imod apply.ltHalf_update E L L (L.filter (· != id)) $$ HltL HltT with ⟨HltL, HltT⟩
    (try wp_auto)
    iapply wp_fupd
    wp_apply (hHdr E p (apply.revokeLog log id) c) $$ [$Hb $Htt $Hw]
      as %h ⟨Htt, Hw, %Hh, Hhf, Hrv, Hnxh, Hlbh, %Hlen⟩
    icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨Hr0, %Hnn⟩
    iStructNamed Hr0
    ipersist Header
    ipersist Hrv
    iapply HΦ
    iframe Htt
    iapply apply.kvPost_backend
    iexists (.applied (apply.revokeLog log id) false)
    isplitr
    · ipureintro; exact hstep
    simp only [apply.revokeOutcomeIs, apply.Outcome.logAfter]
    isplitl [Hhf Hnxh Hlbh Hrdat HltT HRO]
    · isplitr
      · isplitr
        · ipureintro; exact Hnn
        iframe Herr
        iunfold apply.revokeErrIs
        ileft; ipureintro; exact Hok.2
      iunfold apply.revokeResAfter
      rw [apply.revokeIds_applied rq id _ _ L Hrq.2.1 Hrq.1,
        apply.revokeRest_applied L rq id _ _ rs Hrq.2.1 Hrq.1, if_pos Hok.1]
      iframe Hrev HltT HRO
      isplitl [Hrdat]
      · iunfold apply.rdHeld; iexact Hrdat
      -- (X6) the answer: the response's header, `newHeader`'s at the log after
      iunfold apply.revokeAnswer
      rw [Hrq.1]
      iexists _
      isplitr
      · ipureintro; rfl
      ileft
      isplitr
      · ipureintro; exact Hok.2
      iunfold apply.revokeRespIs
      isplitr
      · ipureintro; exact Hnn
      iexists (apply.revokeLog log id)
      iunfold apply.grantHdr
      isplitl [Hhf]
      · iunfold txn.respHdrOwn
        iexists h
        iframe Header
        isplitr
        · ipureintro; exact Hh
        iunfold apply.hdrFields at Hhf
        iexact Hhf
      iexists h, _
      iframe Header Hrv Hnxh Hlbh
      ipureintro
      refine ⟨?_, Hlen.1, Hlen.2⟩
      word
    isplitr [HPost]
    · iapply (apply.kvOwn_of_split E _ B c)
      iframe Hw Htie
      iunfold apply.kvRest
      iframe Hbk Hhk Hard
      iunfold apply.leasesLive
      iexists (L.filter (· != id))
      iframe Hknown' HltL
      iunfold lease.lessorUser
      iframe
    isplitr
    · simp only [apply.chainRes]; itrivial
    ileft; iexact HPost

end proof

end EtcdGrove
end Perennial
