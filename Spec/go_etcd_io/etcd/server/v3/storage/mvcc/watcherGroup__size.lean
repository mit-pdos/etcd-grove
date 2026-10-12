/-
`watcherGroup.size` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchGroup.lean`.
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

/-- `wg.size()`: the number of members. -/
abbrev mvcc.watcherGroup.size.spec : Prop :=
  ∀ (wg : Loc) (W : GMap Loc mvcc.WatchRange),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W }}
    (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"size")) (Val #()))
  {{ RET #(W64 (GMap.size W)); mvcc.ownWatcherGroup wg W ∗ ⌜GMap.size W < 2 ^ 63⌝ }}

end spec

end EtcdGrove
end Perennial
