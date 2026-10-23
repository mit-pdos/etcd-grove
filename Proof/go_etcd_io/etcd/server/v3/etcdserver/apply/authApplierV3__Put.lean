/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkPutAuth
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

theorem apply.authApplierV3.Put.wp_proof
    (hPut : apply.checkPutAuth.spec (GF := GF) (hG := hG)) :
    apply.authApplierV3.Put.spec (GF := GF) (hG := hG) := by
  intro E c inner p r rq o log F Pre Q Post
  wp_start as ⟨#Hauth, #Hinner, Hpre, #HF⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, ⟨%le, #Hlef, #Hle⟩, -⟩
  iunfold apply.putPre at Hpre
  icases Hpre with ⟨%Hk, #Hcp, #Hr, Hwt, Hm⟩
  ihave #Hcp := apply.certPre_auth E E.authOn c rq log $$ Hcp
  iunfold apply.mPre at Hm
  icases Hm with ⟨Hkv, Hres, Hcs⟩
  ihave ⟨Hard, Hkv⟩ := apply.kvOwn_rd E log $$ Hkv
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner $$ Happ Hres
  iunfold apply.authInfoOwn at Hinfo
  icases Hinfo with ⟨%info, Hinfo⟩
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HI, -⟩
  have hk : apply.authChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  wp_auto
  ihave #HleA := apply.isApplyLessorAny_of _ _ _ _ _ _ $$ Hle
  wp_apply (hPut st le E.γ E.P E.f E.RD E.authMode E.RW _ info (DFrac.own 1) r o) $$ [$Hst $HleA $Hinfo $Hard $Hr] as %err ⟨Hinfo, Hard, #HeI, %Hoff, -⟩
  ihave Hkv := Hkv $$ Hard
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    isplitl
    rotate_left
    · iapply apply.traceRes_null
    iapply apply.auth_reject_kvPostF E E.authOn c p (.ok bi) rq log F _ Pre Q Post hk (Or.inl (by cases h : E.authOn <;> first | rfl | cases Hoff h)) $$ Happ [] Hkv [Hinfo]
      Hres Hcs
    · simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.rejErrIs]
      isplitr
      · ipureintro; trivial
      · iframe HeI; ipureintro; simp
    · iunfold apply.authInfoOwn; iexists info; iexact Hinfo
  | nil =>
  wp_auto
  wp_apply HI $$ %r %rq %o %log %F %Pre %Q %Post [Hwt Hkv Hres Hcs] as %resp %trace %err ⟨Hpost, Htrc⟩
  · iunfold apply.putPre
    iunfold apply.mPre
    iframe
    iframe #
    ipureintro; exact Hk
  iapply HΦ
  isplitr [Htrc]
  rotate_left
  · iexact Htrc
  iapply apply.auth_pass_kvPostF E E.authOn c p (.ok bi) rq log F _ Pre Post $$ Happ Hpost
  iunfold apply.authInfoOwn; iexists info; iexact Hinfo

end proof

end EtcdGrove
end Perennial
