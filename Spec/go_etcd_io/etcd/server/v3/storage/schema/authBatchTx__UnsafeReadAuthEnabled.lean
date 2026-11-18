/-
`(*authBatchTx).UnsafeReadAuthEnabled()` (`auth.go`): `unsafeReadAuthEnabled` on the transaction's `tx`.
Lean-first (no Rocq counterpart); the authstore-noax stage (2026-11-18, `notes/decisions.md`,
"authstore-noax").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBackendReal

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

/-- An `authBatchTx` whose `tx` is the reader `rt` over the auth buckets `D` under `H`: as
`unsafeReadAuthEnabled`. -/
abbrev schema.authBatchTx.UnsafeReadAuthEnabled.spec : Prop :=
  ∀ (atl : Loc) (rt : GoInterfaceOk) (H : IProp GF) (D : schema.AuthData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atl ↦□ (GoInterface.ok rt : GoInterface) ∗
      schema.authReader rt H D ∗ H }}
    (App (Val (atl @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeReadAuthEnabled")) (Val #()))
  {{ (b : Bool), RET #b; H ∗ ⌜b = schema.enabledOf D⌝ }}

end spec

end EtcdGrove
end Perennial
