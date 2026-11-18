/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/authBatchTx__UnsafeGetAllUsers.lean`. Lean-first (no Rocq
counterpart); the authstore-noax stage (2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeGetAllUsers
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.unsafeGetAllUsers

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

theorem schema.authBatchTx.UnsafeGetAllUsers.wp_proof
    (hF : schema.unsafeGetAllUsers.spec (GF := GF) (hG := hG)) :
    schema.authBatchTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG) := by
  intro atl lg r H
  wp_start as ⟨#Htx, #Hlg, HH, #HFE⟩
  wp_auto
  wp_apply (hF lg r H) $$ [$HH $HFE] as %s ⟨HH, Hs⟩
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
