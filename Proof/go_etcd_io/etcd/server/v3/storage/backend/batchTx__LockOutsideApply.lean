/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__LockOutsideApply.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__LockOutsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__lock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.ValidateCalledOutSideApply

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

theorem backend.batchTx.LockOutsideApply.wp_proof
    (hValidate : backend.ValidateCalledOutSideApply.spec (GF := GF) (hG := hG))
    (hlock : backend.batchTx.lock.spec (GF := GF) (hG := hG)) :
    backend.batchTx.LockOutsideApply.spec (GF := GF) (hG := hG) := by
  intro γ P WR b t qo
  wp_start as ⟨#Hb, #Ht, Ho⟩
  unfold bOpen
  icases Ho with ⟨Ho, Hcls⟩
  icases isBackend_bt γ P WR b t $$ [Hb Ht] with
    ⟨%db, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb, %HP⟩
  · iframe #
  wp_auto
  wp_apply hValidate
  wp_apply (hlock γ P WR b t qo.half) $$ [$Ho] as ⟨%st, Hl, %Hfo, HWR, Ho⟩
  · iframe #
  iapply HΦ
  iexists st
  iframe
  ipureintro
  exact Hfo.1

end proof

end EtcdGrove
end Perennial
