/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__commit.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__unsafeCommit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__Lock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__Unlock

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

theorem backend.batchTxBuffered.commit.wp_proof
    (hLock : backend.readTx.Lock.spec (GF := GF) (hG := hG))
    (hUC : backend.batchTxBuffered.unsafeCommit.spec (GF := GF) (hG := hG))
    (hUnlock : backend.readTx.Unlock.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.commit.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t rt st win stop m u
  wp_start as ⟨#Hb, #Ht, #Hrt, Hl, HWR, %Hc, Hpay⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #-⟩
  · iframe #
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t', %rt', %db1, %lg', #-, #Hrt', #-, %-, #-, #-, #-, #Hrg, #-⟩
  icombine Hrt Hrt' gives %Heq
  subst Heq
  wp_auto
  wp_apply (hLock γ P rt) $$ [$Hrg] as ⟨Hwl, Hrr⟩
  wp_apply (hUC γ P W Pk b t rt st win stop m u) $$ [$Hl $HWR $Hrr $Hpay] as ⟨Hrr, HWR, Hpo, Hpost⟩
  · iframe #
    ipureintro
    exact Hc
  wp_apply (hUnlock γ P rt) $$ [$Hwl $Hrr]
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
