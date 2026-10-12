/-
`watcherGroup.delete` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchGroup.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchGroup

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `wg.delete(wa)`: the group without `wa`, and whether it was a member (the interval tree's
`Delete` failing, a `panic`, is excluded by the group's invariant: the interval of a non-empty
range set is in the tree). -/
abbrev mvcc.watcherGroup.delete.spec : Prop :=
  ∀ (wg : Loc) (W : GMap Loc mvcc.WatchRange) (wa : Loc) (r : mvcc.WatchRange) (fcs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W ∗ mvcc.watcherFixed wa r fcs }}
    (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"delete")) (Val #wa))
  {{ RET #((W !! wa).isSome); mvcc.ownWatcherGroup wg (GMap.delete wa W) }}

end spec

end EtcdGrove
end Perennial
