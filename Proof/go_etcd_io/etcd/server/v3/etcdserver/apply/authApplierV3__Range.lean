/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Range
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging

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

theorem apply.authApplierV3.Range.wp_proof :
    apply.authApplierV3.Range.spec (GF := GF) (hG := hG) := by
  intro E c inner p r rq o log
  wp_start as ⟨#Hauth, #Hinner, Hpre⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, -, -⟩
  iunfold apply.rangePre at Hpre
  icases Hpre with ⟨%Hk, #Hr, Hkv, Hres⟩
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner $$ Happ Hres
  iunfold apply.authInfoOwn at Hinfo
  icases Hinfo with ⟨%info, Hinfo⟩
  ihave #Hst' := Hst
  iunfold apply.isAuthStore at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, #HRange, -⟩
  iunfold apply.permCheck3 at HRange
  ihave #Hr' := Hr
  iunfold txn.rangeRequestIs at Hr'
  icases Hr' with ⟨%Hrn, %ksl, %esl, %k, %e, %x1, %x2, %x3, %x4, %x5, %x6, %x7, %x8, %x9, %x10,
    %x11, #HK, #Hk, #HE, #He, -⟩
  subst Hsti
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, #HRangeI, -⟩
  wp_auto
  wp_apply HRange $$ %_ %info %(DFrac.own 1) %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hinfo]
    as %err ⟨Hinfo, -⟩
  · iframe; iframe #
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iunfold apply.rangePost
    iexists (.rejected .auth)
    isplitr
    · ipureintro
      simp [apply.chainStep, apply.authChecks, Hk.2.1]
    simp only [apply.rangeOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
    iframe Hkv
    isplitr
    · isplitr
      · ipureintro; trivial
      · ipureintro; simp
    iapply apply.chainRes_auth_in c p (.ok bi) $$ Happ [Hinfo] Hres
    iunfold apply.authInfoOwn
    iexists info; iexact Hinfo
  | nil =>
  wp_auto
  wp_apply HRangeI $$ %r %rq %o %log [Hkv Hres] as %resp %trace %err Hpost
  · iunfold apply.rangePre
    iframe
    iframe #
    ipureintro; exact Hk
  iapply HΦ
  iunfold apply.rangePost at Hpost
  iunfold apply.rangePost
  icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres⟩
  iexists oc
  iframe HR Hkv
  isplitr
  · ipureintro
    simp only [apply.chainStep, apply.authChecks, Hk.2.1]
    simp [Hst]
  iapply apply.chainRes_auth_in c p (.ok bi) $$ Happ [Hinfo] Hres
  iunfold apply.authInfoOwn
  iexists info; iexact Hinfo

end proof

end EtcdGrove
end Perennial
