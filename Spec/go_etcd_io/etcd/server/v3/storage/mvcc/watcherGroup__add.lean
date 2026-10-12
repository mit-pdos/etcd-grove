/-
`watcherGroup.add` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchGroup.lean`.
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

/-- `wg.add(wa)` of a watcher not in the group: the group with it (the `panic("add watcher
twice!")` is excluded by the premise). -/
abbrev mvcc.watcherGroup.add.spec : Prop :=
  ∀ (wg : Loc) (W : GMap Loc mvcc.WatchRange) (wa : Loc) (r : mvcc.WatchRange) (fcs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W ∗ mvcc.watcherFixed wa r fcs ∗ ⌜W !! wa = none⌝ }}
    (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"add")) (Val #wa))
  {{ RET #(); mvcc.ownWatcherGroup wg (<[wa := r]> W) }}

end spec

end EtcdGrove
end Perennial
