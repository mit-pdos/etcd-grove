/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Txn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.authApplierV3.Txn.wp_proof
    (hTxn : apply.CheckTxnAuth.spec (GF := GF) (hG := hG)) :
    apply.authApplierV3.Txn.spec (GF := GF) (hG := hG) := by
  intro E c inner p r skip rq t log F Pre Q Post info
  wp_start as ⟨#Hauth, #Hinner, Hpre, #HF, Htt⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, ⟨%le, #Hlef, #Hle⟩, -⟩
  iunfold apply.txnPre at Hpre
  icases Hpre with ⟨%Hk, #Hcp, #Hr, Hm⟩
  ihave #Hcp := apply.certPre_auth E E.authOn c rq log $$ Hcp
  icases apply.mPre_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hm, Hres⟩
  ihave ⟨Hard, %L, Hu, Hkv⟩ := apply.mPreRest_lend E log Pre Q Post $$ Hm
  ihave Hu : apply.lessorView (mvcc.api.mvccLeases E.γ) (some (L, mvcc.leaseItemsOf (mvcc.stateAfter log))) $$ [Hu]
  · rw [apply.lessorView_some]; iexact Hu
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, #HI, -⟩
  have hk : apply.authChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  wp_auto
  ihave #HleA := apply.isApplyLessorAny_of _ _ _ _ _ _ $$ Hle
  wp_apply (hTxn st le E.γ E.Pk E.f E.BkTie E.RD E.authMode E.RW _ info (DFrac.own 1) r t
      (some (L, mvcc.leaseItemsOf (mvcc.stateAfter log)))) $$ [$Hst $HleA $Hinfo $Hard $Hu $Hr]
    as %err ⟨Hinfo, Hard, Hu, #HeI, %Hoff, #Hcls⟩
  · ipureintro; intro h; cases h
  ihave Hu : lease.lessorUser (mvcc.api.mvccLeases E.γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log)) $$ [Hu]
  · rw [← apply.lessorView_some]; iexact Hu
  ihave Hkv := Hkv $$ Hard Hu
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iframe Htt
    isplitl
    rotate_left
    · iapply apply.traceRes_null
    icases apply.mPreRest_reject_cs _ _ _ _ _ $$ Hkv with ⟨Hkv, %B, Hcs⟩
    iapply apply.auth_reject_kvPostF E E.authOn c p (.ok bi) info rq log F _ _ Pre Q Post hk (Or.inl (by cases h : E.authOn <;> first | rfl | cases Hoff h)) $$ Happ [] Hkv Hinfo
      Hres Hcs
    · simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.rejErrIs]
      isplitr
      · ipureintro; trivial
      · iframe HeI; ipureintro; simp
  | nil =>
  wp_auto
  ihave ⟨#Hcls, #Hlk⟩ := Hcls $$ %rfl
  ihave #Hrc := apply.reqClass_txn E.authMode info rq t Hk.1 Hk.2.1 $$ Hcls
  ihave #Hlk' : apply.txnLeaseClass (GF := GF) E.authMode info
      (mvcc.leaseItemsOf (mvcc.stateAfter log)) t $$ []
  · rw [← apply.viewClass_some L (mvcc.leaseItemsOf (mvcc.stateAfter log))
      (fun I => apply.txnLeaseClass E.authMode info I t)]
    iexact Hlk
  ihave #Hrl := apply.reqLeaseClass_txn E.authMode info _ rq t Hk.1 Hk.2.1 $$ Hlk'
  iunfold apply.chainResAny at Hres
  icases Hres with ⟨%info', Hres⟩
  wp_apply HI $$ %r %skip %rq %t %log %F %Pre %Q %Post %info' [Htt Hkv Hres] as %resp %trace %err ⟨Hpost, Htrc, Htt⟩
  · iframe Htt
    iunfold apply.txnPre
    iframe #
    isplitr
    · ipureintro; exact Hk
    iapply apply.mPre_of_rest
    iframe
  iapply HΦ
  iframe Htt
  isplitr [Htrc]
  rotate_left
  · iexact Htrc
  iapply apply.auth_pass_kvPostF E E.authOn c p (.ok bi) info info' rq log F _ Pre Post $$ Happ Hpost Hinfo Hrc Hrl

end proof

end EtcdGrove
end Perennial
