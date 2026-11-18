/-
`(*authBackend).BatchTx()` (`auth.go`) over the real backend: a new `*authBatchTx` over the
backend's batch transaction with the backend's logger, as an `auth.AuthBatchTx`.
Lean-first (no Rocq counterpart); the authstore-noax stage (2026-11-18, `notes/decisions.md`,
"authstore-noax").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBackendReal
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__BatchTx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- An `authBackend` over the real backend `b` with the logger `lg`: a new `*authBatchTx` (its
fields read-only) over the backend's batch transaction `t`. -/
abbrev schema.authBackend.BatchTx.spec : Prop :=
  ∀ (abe : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (b lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      schema.abeF go!"be" abe ↦□ (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b : GoInterface) ∗
      schema.abeF go!"lg" abe ↦□ lg ∗ isBackend γ P W Pk b }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"BatchTx")) (Val #()))
  {{ (tx : GoInterface), RET #tx; ∃ (atl t : Loc),
      ⌜tx = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty) #atl⌝ ∗
      schema.abtF go!"tx" atl ↦□ (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) #t : GoInterface) ∗ schema.abtF go!"lg" atl ↦□ lg ∗ bF go!"batchTx" b ↦□ t }}

end spec

end EtcdGrove
end Perennial
