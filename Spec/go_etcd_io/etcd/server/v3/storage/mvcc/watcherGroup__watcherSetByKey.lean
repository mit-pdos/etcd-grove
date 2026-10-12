/-
`watcherGroup.watcherSetByKey` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchGroup.lean`.
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

/-- `wg.watcherSetByKey(key)`: the set of the members whose range holds the key, lent: the
group's own key set or range set when the key is in only one of them (by alias, or `nil` when
there is none), else a fresh set; either way the group is back when the set is given back. -/
abbrev mvcc.watcherGroup.watcherSetByKey.spec : Prop :=
  ∀ (wg : Loc) (W : GMap Loc mvcc.WatchRange) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W }}
    (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"watcherSetByKey")) (Val #key))
  {{ (m : GoMap), RET #m; mvcc.ownWatcherSetOpt m (mvcc.membersBy W (·.covers key)) ∗
      (mvcc.ownWatcherSetOpt m (mvcc.membersBy W (·.covers key)) -∗ mvcc.ownWatcherGroup wg W) }}

end spec

end EtcdGrove
end Perennial
