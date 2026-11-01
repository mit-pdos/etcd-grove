/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePuts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthLemmas

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

theorem apply.authApplierV3.LeaseRevoke.wp_proof
    (hLP : apply.checkLeasePuts.spec (GF := GF) (hG := hG)) :
    apply.authApplierV3.LeaseRevoke.spec (GF := GF) (hG := hG) := by
  intro E c inner p r rq id log rs Pre Q Post info
  wp_start as ⟨#Hauth, #Hinner, Hpre⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, ⟨%le, #Hlef, #Hle⟩, -⟩
  iunfold apply.revokePre at Hpre
  icases Hpre with ⟨%Hk, #Hcp, #Hr, Hwt, Hm, Hrr⟩
  ihave #Hcp := apply.certPre_auth E E.authOn c rq log $$ Hcp
  iunfold apply.mPre at Hm
  icases Hm with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hlive, Hard, Hwo⟩
  iunfold apply.leasesLive at Hlive
  icases Hlive with ⟨%L, #Hknown, Hu⟩
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
  ihave #Hle' := apply.isApplyLessorAny_of _ _ _ _ _ _ _ $$ Hle
  ihave #Hr' := Hr
  iunfold apply.leaseRevokeIs at Hr'
  icases Hr' with ⟨%Hrn, #HrID⟩
  have hk : apply.authChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  wp_auto
  wp_apply (hLP st le E.γ E.P E.f E.RD E.authMode E.RW _ info (DFrac.own 1) id L
      (mvcc.leaseItemsOf (mvcc.stateAfter log))) $$ [$Hst $Hle' $Hinfo $Hard $Hu]
    as %err ⟨Hinfo, Hard, Hu, #HeI, %Hoff, #Hlc⟩
  ihave Hkv : apply.kvOwn E log $$ [Hrd Hsw Hu Hard Hwo]
  · iunfold apply.kvOwn
    iframe Hrd Hsw Hard Hwo
    iunfold apply.leasesLive
    iexists L
    iframe Hknown Hu
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    isplitr [Hrr]
    · iapply apply.auth_reject_kvPost E E.authOn c p inner info rq log _ Pre Q Post hk
        (Or.inl (by cases h : E.authOn <;> first | rfl | cases Hoff h)) $$ Happ [] Hkv Hinfo Hres Hcs
      simp only [apply.revokeOutcomeIs, apply.rejErrIs]
      isplitr
      · ipureintro; trivial
      · iframe HeI; ipureintro; simp
    · iunfold apply.revokeRes at Hrr
      iunfold apply.revokeResAfter
      simp only [reduceCtorEq, ↓reduceIte]
      iexact Hrr
  | nil =>
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, #HRevI, -⟩
  iunfold apply.chainResAny at Hres
  icases Hres with ⟨%info', Hres⟩
  wp_auto
  wp_apply HRevI $$ %r %rq %id %log %rs %Pre %Q %Post %info' [Hwt Hkv Hres Hcs Hrr]
    as %resp %err ⟨Hpost, Hra⟩
  · iunfold apply.revokePre
    iunfold apply.mPre
    iframe
    iframe #
    ipureintro; exact Hk
  iapply HΦ
  iframe Hra
  ihave #Hrc : apply.reqClass (GF := GF) E.authMode info rq $$ []
  · simp only [apply.reqClass, Hk.2.1]; itrivial
  ihave #Hrl : apply.reqLeaseClass (GF := GF) E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) rq $$ []
  · simp only [apply.reqLeaseClass, Hk.2.1]
    iexists id
    isplitr
    · ipureintro; exact Hk.1
    iapply Hlc; rfl
  iapply apply.auth_pass_kvPost E E.authOn c p (.ok bi) info info' rq log _ Pre Post $$ Happ Hpost Hinfo Hrc Hrl

end proof

end EtcdGrove
end Perennial
