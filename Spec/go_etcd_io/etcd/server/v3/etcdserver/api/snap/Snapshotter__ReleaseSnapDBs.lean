/-
`(*snap.Snapshotter).ReleaseSnapDBs(snap)` (`server/etcdserver/api/snap/snapshotter.go`), as etcd
PR #22046 changes it: it skips the `.snap.db` files whose index is pending apply. Lean-first (no
Rocq counterpart); branch `pr-verify/etcd-22046` only. See
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `s.ReleaseSnapDBs(snap)`, for a snapshot message `snap` (not `nil`) of index `idx`: it
removes a file `dir/name` only through the caller's hook (`snapRemoveHook γ dir idx`), that is,
only for a name whose parsed index `i` is below `idx` and only after an instant (the
linearization point of its `isPendingDB(i)` check) at which `i` was not in the pending set. It
returns nil or an error; the snapshot is left as it was. (The removal itself comes later,
outside the lock: the hook's right is the caller's to give at that instant.) -/
abbrev snap.Snapshotter.ReleaseSnapDBs.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (dir : GoString) (snap : Loc) (dq : DFrac) (sm : SnapshotM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗
      isSnapshotter s γ dir ∗ ownSnapM snap dq sm ∗ snapRemoveHook γ dir sm.Metadata'.Index' }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty
      @!! go!"ReleaseSnapDBs")) (Val #snap))
  {{ (err : GoInterface), RET #err; ownSnapM snap dq sm ∗ fsResult err iprop(True) iprop(True) }}

end spec

end EtcdGrove
end Perennial
