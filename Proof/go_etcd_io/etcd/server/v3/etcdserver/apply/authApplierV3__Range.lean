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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.authApplierV3.Range.wp_proof :
    apply.authApplierV3.Range.spec (GF := GF) (hG := hG) := by
  intro E c inner p r rq o log info
  wp_start as ⟨#Hauth, #Hinner, Hpre⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, -, -⟩
  iunfold apply.rangePre at Hpre
  icases Hpre with ⟨%Hk, #Hr, Hkv, Hres⟩
  ihave ⟨Hard, Hkv⟩ := apply.kvOwn_rd E log $$ Hkv
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
  ihave #Hst' := Hst
  iunfold apply.isAuthStore at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, #HRange, -⟩
  iunfold apply.permCheck3 at HRange
  ihave #Hr' := Hr
  iunfold txn.rangeRequestIs at Hr'
  icases Hr' with ⟨%Hrn, %ksl, %esl, %k, %e, %x1, %x2, %x3, %x4, %x5, %x6, %x7, %x8, %x9, %x10,
    %x11, #HK, #Hk, #HE, #He, -, -, -, -, -, -, -, -, -, -, -, %Ho, %Hkb⟩
  ihave %Hel := ownSlice_len _ _ _ $$ He
  have hkey : o.key = k := by rw [Ho]; simp only [txn.rangeOpOf.proj_key]
  have hre : o.base.rangeEnd = txn.rangeEndOf esl e := by rw [Ho]; simp only [txn.rangeOpOf.proj_base]
  subst Hsti
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, #HRangeI, -⟩
  wp_auto
  wp_apply HRange $$ %_ %info %(DFrac.own 1) %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hinfo Hard]
    as %err ⟨Hinfo, -, -, Hard, #HeI, %Hoff, #Hpv⟩
  · iframe; iframe #; try (ipureintro; exact Hkb)
  ihave Hkv := Hkv $$ Hard
  cases err with
  | ok e' =>
    have hon : E.authOn = true := by cases h : E.authOn <;> first | rfl | cases Hoff h
    wp_auto
    iapply HΦ
    isplitl
    rotate_left
    · iapply apply.traceRes_null
    iunfold apply.rangePost
    iexists (.rejected .auth)
    isplitr
    · ipureintro
      simp [apply.chainStep, apply.authChecks, Hk.2.1, apply.authMayReject, hon]
    simp only [apply.rangeOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
    iframe Hkv
    isplitr
    · isplitr
      · ipureintro; trivial
      · iframe HeI; ipureintro; simp
    isplitl [Hinfo Hres]
    · iapply apply.chainRes_auth_in c p (.ok bi) info $$ Happ Hinfo Hres
    iapply apply.chainClass_auth_rejected
  | nil =>
  wp_auto
  ihave #Hrc' : apply.rangeClass (GF := GF) E.authMode info o $$ []
  · rw [← hkey]
    iapply (apply.rangeClass_of_verdict E.authMode info o esl e Hel.1 hre) $$ Hpv
  ihave #Hrc := apply.reqClass_range E.authMode info rq o Hk.1 Hk.2.1 $$ Hrc'
  iunfold apply.chainResAny at Hres
  icases Hres with ⟨%info', Hres⟩
  wp_apply HRangeI $$ %r %rq %o %log %info' [Hkv Hres] as %resp %trace %err ⟨Hpost, Htrc⟩
  · iunfold apply.rangePre
    iframe
    iframe #
    ipureintro; exact Hk
  iapply HΦ
  isplitr [Htrc]
  rotate_left
  · iexact Htrc
  iunfold apply.rangePost at Hpost
  iunfold apply.rangePost
  icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, -⟩
  iexists oc
  iframe HR Hkv
  isplitr
  · ipureintro
    simp only [apply.chainStep, apply.authChecks, Hk.2.1]
    simp [Hst]
  ihave Hres := apply.chainResAny_of c _ info' $$ Hres
  isplitl [Hinfo Hres]
  · iapply apply.chainRes_auth_in c p (.ok bi) info $$ Happ Hinfo Hres
  iapply apply.chainClass_auth_pass $$ Hrc

end proof

end EtcdGrove
end Perennial
