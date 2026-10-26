/-
`(*authReadTx).UnsafeReadAuthRevision()` (`auth.go`): `unsafeReadAuthRevision` on the transaction's
`tx`. The auth plan's S1 (2026-10-23; `notes/auth-plan.md`; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvAuthBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- An `authReadTx` whose `tx` is the reader `rt` over the auth buckets `D` (its revision 8
bytes) under `H`: returns `revisionOf D`. -/
abbrev schema.authReadTx.UnsafeReadAuthRevision.spec : Prop :=
  ∀ (atx : Loc) (rt : GoInterfaceOk) (H : IProp GF) (D : schema.AuthData), schema.revWf D.auth →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.atxF go!"tx" atx ↦□ (GoInterface.ok rt : GoInterface) ∗ schema.authReader rt H D ∗ H }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authReadTx.ty @!! go!"UnsafeReadAuthRevision")) (Val #()))
  {{ (x : w64), RET #x; H ∗ ⌜x = schema.revisionOf D⌝ }}

end spec

end EtcdGrove
end Perennial
