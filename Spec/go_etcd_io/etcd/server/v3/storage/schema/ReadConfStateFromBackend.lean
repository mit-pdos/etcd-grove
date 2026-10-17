/-
`schema.ReadConfStateFromBackend(lg, tx)` (`server/storage/schema/confstate.go`, added by
etcd-io/etcd#19693; pr-verify, 2026-10-17). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvConfState.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvConfState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `ReadConfStateFromBackend(lg, tx)`: `UnsafeConfStateFromBackend(lg, tx)` between
`tx.RLock()` and `tx.RUnlock()` (a deferred unlock): `nil` or a fresh conf state, owned. -/
abbrev schema.ReadConfStateFromBackend.spec : Prop :=
  ∀ (lg : Loc) (rt : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      csReadTx rt }}
    (App (App (Val (@! schema.ReadConfStateFromBackend)) (Val #lg)) (Val #(GoInterface.ok rt)))
  {{ (cs : Loc), RET #cs; csRead cs }}

end spec

end EtcdGrove
end Perennial
