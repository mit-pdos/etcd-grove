/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__LeaseRevoke
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
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
  intro E c inner p r rq id log T rs Pre Q Post info
  -- over `mPreRest` with `lean`'s revocation post by the outcome (`mPreRest_lend` keeps the half
  -- of the live set `ltHalf` inside its way back)
  wp_start as ⟨#Hauth, #Hinner, Htt, Hpre⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, ⟨%le, #Hlef, #Hle⟩, -⟩
  iunfold apply.revokePre at Hpre
  icases Hpre with ⟨%Hk, #Hcp, #Hr, Hm, Hrr⟩
  ihave #Hcp := apply.certPre_auth E E.authOn c rq log $$ Hcp
  icases apply.mPre_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hm, Hres⟩
  ihave ⟨Hard, %L, Hu, Hkv⟩ := apply.mPreRest_lend E log Pre Q Post $$ Hm
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
  ihave #Hle' := apply.isApplyLessorAny_of _ _ _ _ _ _ _ $$ Hle
  ihave #Hr' := Hr
  iunfold apply.leaseRevokeIs at Hr'
  icases Hr' with ⟨%Hrn, #HrID⟩
  have hk : apply.authChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  wp_auto
  wp_apply (hLP st le E.γ E.Pk E.f E.BkTie E.RD E.authMode E.RW _ info (DFrac.own 1) id L
      (mvcc.leaseItemsOf (mvcc.stateAfter log))) $$ [$Hst $Hle' $Hinfo $Hard $Hu]
    as %err ⟨Hinfo, Hard, Hu, #HeI, %Hoff, #Hlc⟩
  ihave Hkv := Hkv $$ Hard Hu
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iframe Htt
    icases apply.mPreRest_reject_cs _ _ _ _ _ $$ Hkv with ⟨Hkv, %B, Hcs⟩
    iapply apply.auth_reject_kvPost E E.authOn c p inner info rq log _ _ Pre Q Post hk
      (Or.inl (by cases h : E.authOn <;> first | rfl | cases Hoff h)) $$ Happ [Hrr] Hkv Hinfo Hres Hcs
    simp only [apply.revokeOutcomeIs, apply.rejErrIs]
    iunfold apply.revokeRes at Hrr
    icases Hrr with ⟨Hrdat, Hrev, HltT, HRO, -⟩
    iunfold apply.revokeResAfter
    rw [apply.revokeIds_rejected, apply.revokeRest_rejected]
    ihave #Hra := apply.revokeAnswer_err (GF := GF) E rq null (GoInterface.ok e')
      (by intro h; cases h)
    iframe Hrdat Hrev HltT HRO Hra
    isplitr
    · ipureintro; trivial
    · iframe HeI; ipureintro; simp
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
  wp_apply HRevI $$ %r %rq %id %log %T %rs %Pre %Q %Post %info' [Htt Hkv Hres Hrr]
    as %resp %err ⟨Hpost, Htt⟩
  · iframe Htt
    iunfold apply.revokePre
    iframe # Hrr
    isplitr
    · ipureintro; exact Hk
    iapply apply.mPre_of_rest
    iframe
  iapply HΦ
  iframe Htt
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
