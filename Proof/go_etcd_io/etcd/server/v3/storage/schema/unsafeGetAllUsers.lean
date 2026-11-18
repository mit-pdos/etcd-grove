/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/unsafeGetAllUsers.lean`. Lean-first (no Rocq
counterpart); the authstore-noax stage (2026-11-18).
-/
module

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

theorem schema.unsafeGetAllUsers.wp_proof :
    schema.unsafeGetAllUsers.spec (GF := GF) (hG := hG) := by
  intro lg r H
  wp_start as ⟨HH, #HFE⟩
  iunfold schema.forEachUsersEmpty at HFE
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, ⟨%ub, #HU, -⟩, -⟩
  wp_auto
  wp_apply HFE $$ [$HH $HU] as %err ⟨%Herr, HH⟩
  subst Herr
  wp_auto
  iapply HΦ
  iframe HH
  iapply ownSlice_nil

end proof

end EtcdGrove
end Perennial
