/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/sharedBoltTx__reset.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__reset
public import Spec.go_etcd_io.bbolt.Tx__Rollback_kv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions]

theorem backend.sharedBoltTx.reset.wp_proof
    (hRollback : bbolt.Tx.Rollback_kv.spec (GF := GF) (hG := hG)) :
    backend.sharedBoltTx.reset.spec (GF := GF) (hG := hG) := by
  intro γ st cm tx wg lg
  wp_start as ⟨Hcm, Htx, Hwg, Hr⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_join iprop(rtxOf st ↦ tx ∗ rwgOf st ↦ wg ∗ st_ptr ↦ st) with [Htx Hwg st Hr]
    as ⟨Htx, Hwg, st⟩
  · -- a bbolt read transaction: the rollback goroutine
    icases Hr with (Hr | %Hnull)
    rotate_left
    · exact absurd Hnull Hif
    wp_apply wp_fork $$ [Hr]
    · wp_auto
      wp_apply (wp_rollback_Wait γ tx wg) $$ [$Hsync $Hr] as ⟨%D, Hl1, #Hsn⟩
      wp_apply (hRollback tx D) $$ [$Hl1 $Hsn] as -
      itrivial
    wp_join_done
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %cm' Hcm'
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
