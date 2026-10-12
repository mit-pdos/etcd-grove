/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Capped__Txn
public import Spec.go_etcd_io.etcd.server.v3.storage.BackendQuota__Cost
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

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

theorem apply.applierV3Capped.Txn.wp_proof
    (hCost : storage.BackendQuota.Cost.spec (GF := GF) (hG := hG)) :
    apply.applierV3Capped.Txn.spec (GF := GF) (hG := hG) := by
  intro E c inner p r skip rq t log Pre Q Post
  wp_start as ⟨Hc, #Hin, Hpre⟩
  iunfold apply.cappedIs at Hc
  ipersist Hc
  ihave #He : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors $$ []
  · iPkgInit
  ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ He
  icases Hei with ⟨%eN, #HeN, %HeNp⟩
  wp_auto
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, #HTxn, -⟩
  iunfold apply.txnPre at Hpre
  icases Hpre with ⟨%Hk, #Hr, Hm⟩
  iunfold apply.mPre at Hm
  icases Hm with ⟨Hkv, Hres, Hcs⟩
  wp_apply hCost
  · ipureintro; exact Or.inr (Or.inl rfl)
  iintro %cost -
  wp_auto
  wp_if_destruct
  · -- the request costs: `ErrNoSpace`
    iapply HΦ
    iunfold apply.kvPost
    iexists (.rejected .noSpace)
    isplitr
    · ipureintro
      simp only [apply.chainStep, apply.cappedRejects, Hk.2.1, ↓reduceIte]
      simp
    simp only [apply.txnOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
    iframe Hkv Hres
    isplitl []
    · isplitl []
      · ipureintro; trivial
      iunfold txn.errVarIs
      iexists eN
      iframe HeN
      ipureintro; rfl
    iright
    iapply apply.csContract_pre $$ Hcs
  · -- the inner applier's `Txn`
    ihave Hres := apply.chainRes_capped_out c p (.ok bi) $$ Hc Hres
    wp_apply HTxn $$ %r %skip %rq %t %log %Pre %Q %Post [Hkv Hres Hcs]
      as %resp %trace %err Hpost
    · iunfold apply.txnPre
      iunfold apply.mPre
      iframe
      iframe #
      ipureintro; exact Hk
    iapply HΦ
    iunfold apply.kvPost at Hpost
    iunfold apply.kvPost
    icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, HPP⟩
    iexists oc
    iframe HR Hkv HPP
    isplitr
    · ipureintro
      simp only [apply.chainStep, apply.cappedRejects, Hk.2.1, ↓reduceIte]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact Or.inr Hst
    iapply apply.chainRes_capped_in c p (.ok bi) $$ Hc Hres

end proof

end EtcdGrove
end Perennial
