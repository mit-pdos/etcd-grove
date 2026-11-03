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
  intro E p r rq id log rs Pre Q Post info
  wp_start as ⟨#Hb, Hpre⟩
  iunfold apply.revokePre at Hpre
  iunfold apply.mPre at Hpre
  iunfold apply.kvOwn at Hpre
  icases Hpre with ⟨%Hrq, #Hcp, #Hr, Hwt, ⟨⟨Hrd, Hsw, Hlive, Hard⟩, Hres, Hcs⟩, Hrr⟩
  iunfold apply.revokeRes at Hrr
  icases Hrr with ⟨Hrdat, HRO⟩
  iunfold apply.leasesLive at Hlive
  icases Hlive with ⟨%L, #Hknown, Hu⟩
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
  · -- not live: the error, nothing changed
    have hlog : apply.revokeLog log id = log := by
      unfold apply.revokeLog; rw [Hnf.2]; rfl
    (try wp_auto)
    wp_apply hHdr $$ [$Hrd $Hsw] as %h ⟨Hrd, Hsw, %Hh⟩
    · iexact Hb
    icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨Hr0, %Hnn⟩
    iStructNamed Hr0
    iapply HΦ
    isplitr [Hrdat HRO]
    · iapply apply.kvPost_backend
      iexists (.applied (apply.revokeLog log id) false)
      isplitr
      · ipureintro; exact hstep
      simp only [apply.revokeOutcomeIs, apply.Outcome.logAfter]
      rw [hlog]
      isplitl [Header]
      · isplitr
        · ipureintro; exact Hnn
        isplitl [Header]
        · iexists h; iframe Header; ipureintro; exact Hh
        iframe Herr
        iunfold apply.revokeErrIs
        iright; iexists e; iframe He; ipureintro; exact Hee
      isplitr [HPre]
      · iunfold apply.kvOwn
        iframe Hrd Hsw Hard
        iunfold apply.leasesLive
        iexists L
        iframe Hknown
        iunfold lease.lessorUser
        iframe
      isplitr
      · simp only [apply.chainRes]; itrivial
      iright; iexact HPre
    · iunfold apply.revokeResAfter
      iframe Hrdat
      subst Hee
      simp only [reduceCtorEq, ↓reduceIte]
      iexact HRO
  · -- live: the lease's keys deleted, the lease gone
    (try wp_auto)
    wp_apply hHdr $$ [$Hrd $Hsw] as %h ⟨Hrd, Hsw, %Hh⟩
    · iexact Hb
    icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨Hr0, %Hnn⟩
    iStructNamed Hr0
    iapply HΦ
    isplitr [Hrdat HRO]
    · iapply apply.kvPost_backend
      iexists (.applied (apply.revokeLog log id) false)
      isplitr
      · ipureintro; exact hstep
      simp only [apply.revokeOutcomeIs, apply.Outcome.logAfter]
      isplitl [Header]
      · isplitr
        · ipureintro; exact Hnn
        isplitl [Header]
        · iexists h; iframe Header; ipureintro; exact Hh
        iframe Herr
        iunfold apply.revokeErrIs
        ileft; ipureintro; exact Hok.2
      isplitr [HPost]
      · iunfold apply.kvOwn
        iframe Hrd Hsw Hard
        iunfold apply.leasesLive
        iexists (L.filter (· != id))
        iframe Hknown'
        iunfold lease.lessorUser
        iframe
      isplitr
      · simp only [apply.chainRes]; itrivial
      ileft; iexact HPost
    · iunfold apply.revokeResAfter
      iframe Hrdat
      rw [if_pos Hok.2]
      iexact HRO

end proof

end EtcdGrove
end Perennial
