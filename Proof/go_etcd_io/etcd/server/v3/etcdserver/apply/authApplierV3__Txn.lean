/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.CheckTxnAuth
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

theorem apply.authApplierV3.Txn.wp_proof
    (hTxn : apply.CheckTxnAuth.spec (GF := GF) (hG := hG)) :
    apply.authApplierV3.Txn.spec (GF := GF) (hG := hG) := by
  intro E c inner p r skip rq t log Pre Q Post
  wp_start as ⟨#Hauth, #Hinner, Hpre⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, ⟨%le, #Hlef, #Hle⟩, -⟩
  iunfold apply.txnPre at Hpre
  icases Hpre with ⟨%Hk, #Hr, Hm⟩
  iunfold apply.mPre at Hm
  icases Hm with ⟨Hkv, Hres, Hcs⟩
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner $$ Happ Hres
  iunfold apply.authInfoOwn at Hinfo
  icases Hinfo with ⟨%info, Hinfo⟩
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, #HI, -⟩
  have hk : apply.authChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  wp_auto
  wp_apply (hTxn st le E.γ E.P E.f _ info (DFrac.own 1) r t) $$ [$Hst $Hle $Hinfo $Hr] as %err Hinfo
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iapply apply.auth_reject_kvPost E c p (.ok bi) rq log _ Pre Q Post hk $$ Happ [] Hkv [Hinfo]
      Hres Hcs
    · simp only [apply.txnOutcomeIs, apply.rejErrIs]
      isplitr
      · ipureintro; trivial
      · ipureintro; simp
    · iunfold apply.authInfoOwn; iexists info; iexact Hinfo
  | nil =>
  wp_auto
  wp_apply HI $$ %r %skip %rq %t %log %Pre %Q %Post [Hkv Hres Hcs] as %resp %trace %err Hpost
  · iunfold apply.txnPre
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
