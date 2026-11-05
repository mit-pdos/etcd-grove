/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVLemmas

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
  wp_start as ⟨#Hb, Hpre⟩
  iunfold apply.revokePre at Hpre
  iunfold apply.mPre at Hpre
  iunfold apply.kvOwn at Hpre
  icases Hpre with ⟨%Hrq, #Hcp, #Hr, Hwt, ⟨⟨Hrd, Hsw, Hlive, Hard⟩, Hres, Hcs⟩, Hrr⟩
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
  icases Hok with ⟨%Hlg, -, -, #Hle, -⟩
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨-, %li, %Hli, -, #HRv, -, -⟩
  iunfold apply.leaseRevokeIs at Hr
  icases Hr with ⟨%Hrn, #HrID⟩
  have hstep : apply.backendStep rq log (.applied (apply.revokeLog log id) false) := by
    unfold apply.backendStep; rw [Hrq.2.1]; exact ⟨id, Hrq.1, rfl⟩
  ihave #Hcert : mvcc.certOkNext E.γ log (mvcc.leaseDels (mvcc.stateAfter log) id) $$ []
  · iapply apply.certOkNext_of_commitLog
    iapply (apply.certPre_backend_applied E rq log (apply.revokeLog log id) false hstep) $$ Hcp
  iStructNamed Hopts
  wp_auto
  rw [Hli]
  wp_auto
  iunfold apply.revokeClause at HRv
  wp_apply HRv $$ [$Hcs $Hsw $Hrd $Hwt $Hown $Hrvk $Hrdat $HRO] as %err ⟨Hrd, Hrdat, #Herr, Hcase⟩
  · iframe #; ipureintro; exact Hrq.2.2
  icases Hcase with
    (⟨%Hnf, ⟨%e, #He, %Hee⟩, HPre, Hwt, Hsw, Hown, Hrvk, -, HRO⟩ |
     ⟨%Hok, HPost, Hsw, Hown, Hrvk, #Hknown', HRO⟩)
  · -- not live: the error, nothing changed (the live set's filter the identity)
    have hlog : apply.revokeLog log id = log := by
      unfold apply.revokeLog; rw [Hnf.2]; rfl
    have hflt : L.filter (· != id) = L :=
      List.filter_eq_self.2 (fun a ha => by
        have : a ≠ id := fun h => Hnf.1 (h ▸ ha)
        simpa using this)
    (try wp_auto)
    wp_apply hHdr $$ [$Hrd $Hsw] as %h ⟨Hrd, Hsw, %Hh, -⟩
    · iexact Hb
    icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨Hr0, %Hnn⟩
    iStructNamed Hr0
    iapply HΦ
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
        apply.revokeRest_applied L rq id _ _ rs Hrq.2.1 Hrq.1, if_neg Hnf.1]
      iframe Hrdat Hrev HltT HRO
      iapply apply.revokeAnswer_err E rq _ err (by rw [Hee]; intro h; cases h)
    isplitr [HPre]
    · iunfold apply.kvOwn
      iframe Hrd Hsw Hard
      iunfold apply.leasesLive
      iexists L
      iframe Hknown HltL
      iunfold lease.lessorUser
      iframe
    isplitr
    · simp only [apply.chainRes]; itrivial
    iright; iexact HPre
  · -- live: the lease's keys deleted, the lease gone from both halves of the live set
    imod apply.ltHalf_update E L L (L.filter (· != id)) $$ HltL HltT with ⟨HltL, HltT⟩
    (try wp_auto)
    iapply wp_fupd
    wp_apply hHdr $$ [$Hrd $Hsw] as %h ⟨Hrd, Hsw, %Hh, Hhf, Hrv, #Hcok, %Hlen⟩
    · iexact Hb
    ihave ⟨Hsw, #Hcert⟩ := txn.kvWriter_cert E.s E.γ _ $$ Hsw
    icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨Hr0, %Hnn⟩
    iStructNamed Hr0
    ipersist Header
    ipersist Hrv
    imodintro
    iapply HΦ
    iapply apply.kvPost_backend
    iexists (.applied (apply.revokeLog log id) false)
    isplitr
    · ipureintro; exact hstep
    simp only [apply.revokeOutcomeIs, apply.Outcome.logAfter]
    isplitl [Hhf Hrdat HltT HRO]
    · isplitr
      · isplitr
        · ipureintro; exact Hnn
        iframe Herr
        iunfold apply.revokeErrIs
        ileft; ipureintro; exact Hok.2
      iunfold apply.revokeResAfter
      rw [apply.revokeIds_applied rq id _ _ L Hrq.2.1 Hrq.1,
        apply.revokeRest_applied L rq id _ _ rs Hrq.2.1 Hrq.1, if_pos Hok.1]
      iframe Hrdat Hrev HltT HRO
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
      iframe Header Hrv Hcert Hcok
      ipureintro
      refine ⟨?_, Hlen.1, Hlen.2⟩
      word
    isplitr [HPost]
    · iunfold apply.kvOwn
      iframe Hrd Hsw Hard
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
