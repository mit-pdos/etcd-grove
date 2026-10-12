/-
`newWatcherGroup` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchGroup.lean`.
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

/-- `newWatcherGroup()`: a fresh, empty group, as a `watcherGroup` value (the caller stores it,
in a field of the store or a local); wherever it is stored, the group there is empty. -/
abbrev mvcc.newWatcherGroup.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup)) (Val #()))
  {{ (v : watcherGroup), RET #v; ∀ wg : Loc, wg ↦ v -∗ mvcc.ownWatcherGroup wg ∅ }}

end spec

end EtcdGrove
end Perennial
