/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__Unlock.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__Unlock

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

theorem backend.batchTx.Unlock.wp_proof :
    backend.batchTx.Unlock.spec (GF := GF) (hG := hG) := by
  intro γ P WR b t
  wp_start as ⟨#Hb, #Ht, Hown, Hfree⟩
  icases isBackend_bt γ P WR b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb0, %HP⟩
  · iframe #
  icases Hfree with (⟨%st, %db, Hph, Hg, %Hfo, HWR⟩ | ⟨Hpend, #Hbs⟩)
  · unfold batchPhys
    icases Hph with ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb, Hwtx, #Htxdb, Hmu⟩
    wp_auto
    wp_if_destruct
    · exfalso
      have := Hfo.2.1
      omega
    wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hg HWR]
    · inext
      unfold batchFree
      ileft
      iexists st, db
      iframe Hg HWR
      isplitl
      · unfold batchPhys
        iexists hk
        iframe
        iframe #
      · ipureintro
        exact Hfo
    iapply HΦ
    itrivial
  · wp_auto
    wp_if_destruct
    · exfalso
      have := HP.2.1
      simp only [show sint.Z (W64 0) = 0 from rfl] at Hif
      omega
    wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hown]
    · inext
      unfold batchFree
      iright
      iexact Hbs
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
