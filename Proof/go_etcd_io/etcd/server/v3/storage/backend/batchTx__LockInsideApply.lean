/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__LockInsideApply.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__LockInsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__lock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.ValidateCalledInsideApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

theorem backend.batchTx.LockInsideApply.wp_proof
    (hlock : backend.batchTx.lock.spec (GF := GF) (hG := hG))
    (hValidate : backend.ValidateCalledInsideApply.spec (GF := GF) (hG := hG)) :
    backend.batchTx.LockInsideApply.spec (GF := GF) (hG := hG) := by
  intro γ P WR b t qo f Q
  wp_start as ⟨#Hb, #Ht, Ho, Hpl, Hf⟩
  unfold bOpen
  icases Ho with ⟨Ho, Hcls⟩
  icases isBackend_bt γ P WR b t $$ [Hb Ht] with
    ⟨%db, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb, %HP⟩
  · iframe #
  wp_auto
  wp_apply (hlock γ P WR b t qo.half) $$ [$Ho] as ⟨%st, Hl, %Hfo, HWR, Ho⟩
  · iframe #
  unfold batchLocked batchLockedAt batchPhys
  icases Hl with ⟨%t', %db', #Ht', Hown, ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb', Hwtx, #Htxdb, Hmu⟩, Hg, %Hwf⟩
  icombine Ht Ht' gives %Heq
  subst Heq
  unfold plHook
  icombine Hpl Hhk gives % ⟨_, Hhkeq⟩
  subst Hhkeq
  wp_auto
  icases Hf with (⟨%Hfn, HQ⟩ | ⟨%Hfn, Hwp⟩)
  · subst Hfn
    wp_auto
    iapply HΦ
    iexists st
    isplitl [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb' Hwtx Hmu Hg]
    · iexists t, db'
      iframe Ht' Hown Hg
      isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb' Hwtx Hmu]
      · iexists _
        iframe
        iframe #
      · ipureintro
        exact Hwf
    iframe
    ipureintro
    exact Hfo.1
  · rw [decide_eq_false Hfn]
    wp_auto
    wp_apply hValidate
    wp_bind (App (Val #f) (Val #()))
    iapply wp_wand $$ Hwp
    iintro %v ⟨%Hv, HQ⟩
    subst Hv
    wp_auto
    iapply HΦ
    iexists st
    isplitl [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb' Hwtx Hmu Hg]
    · iexists t, db'
      iframe Ht' Hown Hg
      isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb' Hwtx Hmu]
      · iexists _
        iframe
        iframe #
      · ipureintro
        exact Hwf
    iframe
    ipureintro
    exact Hfo.1

end proof

end EtcdGrove
end Perennial
