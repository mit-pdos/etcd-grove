/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__lock.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__lock

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

theorem backend.batchTx.lock.wp_proof :
    backend.batchTx.lock.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t qo
  wp_start as ⟨#Hb, #Ht, Ho⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb, %HP⟩
  · iframe #
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hm] as ⟨Hown, Hfree⟩
  unfold batchFree
  icases Hfree with (⟨%st, %db1, Hph, Hg, %Hfo, HWR⟩ | Hs)
  · ihave %Hp0 := batchGhostAt_p0 γ P st $$ Hg
    ihave Hg := batchGhostAt_take γ P st $$ Hg
    iapply HΦ
    iexists st
    iframe HWR Ho
    unfold batchLocked batchLockedAt
    isplitl [Hown Hph Hg]
    · iexists t, db1
      iframe
      iframe #
      ipureintro
      exact Hfo.1
    · ipureintro
      exact ⟨Hfo, Hp0⟩
  · unfold bStopped
    icombine Ho Hs gives %H
    exact absurd H.2 (by decide)

end proof

end EtcdGrove
end Perennial
