/-
`(*authBatchTx).Lock()` (`auth.go`): `tx.LockInsideApply()`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBatchTx` whose `tx` is `t`: one call of `t`, `LockInsideApply()`: given its triple from `R`
to `Q`, it goes from `R` to `Q`. -/
abbrev schema.authBatchTx.Lock.spec : Prop :=
  ∀ (atx : Loc) (t : GoInterfaceOk) (R Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atx ↦□ (GoInterface.ok t : GoInterface) ∗ R ∗
      {{ R }} (App (Val #(methods t.ty go!"LockInsideApply" t.v)) (Val #())) {{ RET #(); Q }} }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"Lock")) (Val #()))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
