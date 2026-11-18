/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/authBatchTx__Unlock.lean`. Lean-first (no Rocq
counterpart); the authstore-noax stage (2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__Unlock

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.authBatchTx.Unlock.wp_proof
    (hU : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hC : backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG)) :
    schema.authBatchTx.Unlock.spec (GF := GF) (hG := hG) := by
  intro atl γ P W Pk b t st Q S r qo X Y hw hroom
  wp_start as ⟨#Htx, #HB, #Ht, Hl, Hwb1, Hrb, Hd, Hwb2, Ho, HX, #Hcr⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  wp_auto
  wp_apply (hU γ P W Pk b t st Q S r hw hroom) $$ [$Hbpkg $HB $Ht $Hl $Hwb1 $Hrb $Hd] as ⟨HQ, Hrb⟩
  (try wp_auto)
  wp_apply (hC γ P W Pk b t qo X Y) $$ [$Hbpkg $HB $Ht $Ho $Hwb2 $HX $Hcr] as ⟨Ho, HY⟩
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
