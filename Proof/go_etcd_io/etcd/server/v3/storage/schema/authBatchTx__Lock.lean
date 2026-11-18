/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/authBatchTx__Lock.lean`. Lean-first (no Rocq
counterpart); the authstore-noax stage (2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__Lock

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

theorem schema.authBatchTx.Lock.wp_proof
    (hL : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG)) :
    schema.authBatchTx.Lock.spec (GF := GF) (hG := hG) := by
  intro atl γ P W Pk b t qo dq f Pre Q
  wp_start as ⟨#Htx, #HB, #Ht, Ho, Hh, HPre, Hk⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  wp_auto
  wp_apply (hL γ P W Pk b t qo dq f Pre Q) $$ [$Hbpkg $HB $Ht $Ho $Hh $HPre $Hk] as H
  (try wp_auto)
  iapply HΦ $$ H

end proof

end EtcdGrove
end Perennial
