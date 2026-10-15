/-
`storage.NewBackendHooks(lg, indexer)` (`server/storage/hooks.go`). Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/server/v3/storage/InvHooks.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvHooks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- `NewBackendHooks(lg, indexer)` returns fresh hooks over the indexer and the logger, their
`confState` not dirty. -/
abbrev storage.NewBackendHooks.spec : Prop :=
  ∀ (lg : Loc) (ix : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.NewBackendHooks)) (Val #lg)) (Val #(GoInterface.ok ix)))
  {{ (bh : Loc), RET #bh; isBackendHooks bh ix lg }}

end spec

end EtcdGrove
end Perennial
