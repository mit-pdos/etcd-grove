/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__DeleteRange
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.authApplierV3.DeleteRange.wp_proof :
    apply.authApplierV3.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro E c inner p r rq o log Pre Q Post
  wp_start as ⟨#Hauth, #Hinner, Hpre⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, -, -⟩
  iunfold apply.deletePre at Hpre
  icases Hpre with ⟨%Hk, #Hr, Hm⟩
  iunfold apply.mPre at Hm
  icases Hm with ⟨Hkv, Hres, Hcs⟩
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner $$ Happ Hres
  iunfold apply.authInfoOwn at Hinfo
  icases Hinfo with ⟨%info, Hinfo⟩
  ihave #Hst' := Hst
  iunfold apply.isAuthStore at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, #HRange, #HDel, -⟩
  iunfold apply.permCheck3 at HRange
  iunfold apply.permCheck3 at HDel
  ihave #Hr' := Hr
  iunfold txn.deleteRangeRequestIs at Hr'
  icases Hr' with ⟨%Hrn, %ksl, %esl, %k, %e, %pk, #HK, #Hk, #HE, #He, #HPK, -⟩
  subst Hsti
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, #HDelI, -⟩
  have hk : apply.authChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  wp_auto
  wp_apply HDel $$ %_ %info %(DFrac.own 1) %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hinfo]
    as %err ⟨Hinfo, -, -, #HeI⟩
  · iframe; iframe #
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iapply apply.auth_reject_kvPost E c p (.ok bi) rq log _ Pre Q Post hk $$ Happ [] Hkv [Hinfo]
      Hres Hcs
    · simp only [apply.deleteAnswerIs, apply.deleteOutcomeIs, apply.rejErrIs]
      isplitr
      · ipureintro; trivial
      · iframe HeI; ipureintro; simp
    · iunfold apply.authInfoOwn; iexists info; iexact Hinfo
  | nil =>
  wp_auto
  cases pk
  · wp_auto
    wp_apply HDelI $$ %r %rq %o %log %Pre %Q %Post [Hkv Hres Hcs] as %resp %trace %err Hpost
    · iunfold apply.deletePre
      iunfold apply.mPre
      iframe
      iframe #
      ipureintro; exact Hk
    iapply HΦ
    iapply apply.auth_pass_kvPost E c p (.ok bi) rq log _ Pre Post $$ Happ Hpost
    iunfold apply.authInfoOwn; iexists info; iexact Hinfo
  wp_auto
  wp_apply HRange $$ %_ %info %(DFrac.own 1) %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hinfo]
    as %err ⟨Hinfo, -, -, #HeI⟩
  · iframe; iframe #
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iapply apply.auth_reject_kvPost E c p (.ok bi) rq log _ Pre Q Post hk $$ Happ [] Hkv [Hinfo]
      Hres Hcs
    · simp only [apply.deleteAnswerIs, apply.deleteOutcomeIs, apply.rejErrIs]
      isplitr
      · ipureintro; trivial
      · iframe HeI; ipureintro; simp
    · iunfold apply.authInfoOwn; iexists info; iexact Hinfo
  | nil =>
  wp_auto
  wp_apply HDelI $$ %r %rq %o %log %Pre %Q %Post [Hkv Hres Hcs] as %resp %trace %err Hpost
  · iunfold apply.deletePre
    iunfold apply.mPre
    iframe
    iframe #
    ipureintro; exact Hk
  iapply HΦ
  iapply apply.auth_pass_kvPost E c p (.ok bi) rq log _ Pre Post $$ Happ Hpost
  iunfold apply.authInfoOwn; iexists info; iexact Hinfo

end proof

end EtcdGrove
end Perennial
