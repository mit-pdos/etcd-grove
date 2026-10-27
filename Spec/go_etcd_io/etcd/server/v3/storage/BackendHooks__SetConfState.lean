/-
`(*BackendHooks).SetConfState(confState)` (`server/storage/hooks.go`). Lean-first (no Rocq
counterpart); D43 M5b′ (2026-10-26), for `applyConfChange`; see
`Proof/go_etcd_io/etcd/server/v3/storage/InvHooks.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvHooks
public import Spec.google_golang_org.protobuf.proto.CloneConfState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage backend storage go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- `bh.SetConfState(cs)` of the server's hooks (`isBackendHooks`), with `cs` nil or a read-only
`*pb.ConfState`: it returns (under `confStateLock`, `confState` set to a fresh clone of `cs`, a nil
one for nil, and `confStateDirty` to `true`: what `csInv` guards). -/
abbrev storage.BackendHooks.SetConfState.spec : Prop :=
  ∀ (bh : Loc) (ix : GoInterfaceOk) (lg cs : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      storage.isBackendHooks bh ix lg ∗ (⌜cs = null⌝ ∨ ∃ c, ownCSM cs DFrac.discard c) }}
    (App (Val (bh @!! go.GoType.PointerType BackendHooks.ty @!! go!"SetConfState")) (Val #cs))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
