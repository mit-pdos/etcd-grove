/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__Commit.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__lock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__Unlock
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CommitLemmas

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

theorem backend.batchTxBuffered.Commit.wp_proof
    (hlock : backend.batchTx.lock.spec (GF := GF) (hG := hG))
    (hC : backend.batchTxBuffered.commit.spec (GF := GF) (hG := hG))
    (hBU : backend.batchTx.Unlock.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t qo
  wp_start as ⟨#Hb, #Ht, Ho, Htok⟩
  unfold bOpen
  icases Ho with ⟨Ho, Hcls⟩
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t2, %rt, %db1, %lg2, #Ht2, #Hrt, #-, %-, #Hmi, #-, #-, #Hrg, #-, #-, #Hci, %-⟩
  wp_auto
  wp_method_call
  wp_call
  wp_apply (hlock γ P W Pk b t qo.half) $$ [$Ho] as ⟨%st, Hl, %Hfo, ⟨HWv, HWR⟩, Ho⟩
  · iframe #
  ihave Hl := batchLocked_W γ P b st $$ Hl
  wp_apply (hC γ P W Pk b t rt st false false 0 0) $$ [$Hl $HWR Htok] as ⟨HWR, -, Hpost⟩
  · iframe #
    isplitr
    · ipureintro
      exact ⟨Hfo.2, Hfo.1.2.2.2, fun _ => vData_free P st Hfo.1.1 Hfo.1.2.2.1 Hfo.1.2.2.2⟩
    unfold payIn
    rw [if_neg (by decide), if_pos rfl]
    iexact Htok
  try simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hpost with ⟨%st2, %db2, Hown, Hph2, Hg2, %Hfin, -⟩
  wp_method_call
  wp_call
  unfold batchPhys
  icases Hph2 with ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb, Hwtx, #Htxdb, Hmu⟩
  rw [Hfin.2.2]
  wp_auto
  wp_apply (hBU γ P W Pk b t) $$ [$Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hg2 HWv HWR]
  · iframe #
    ileft
    iexists st2, db2
    iframe HWv HWR Hg2
    isplitl
    · unfold batchPhys
      iexists hk
      rw [Hfin.2.2]
      iframe
      iframe #
    · ipureintro
      exact Hfin.1
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
