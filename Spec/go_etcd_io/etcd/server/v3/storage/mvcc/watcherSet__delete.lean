/-
`watcherSet.delete` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchGroup.lean`.
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

/-- `w.delete(wa)` (a map value receiver) of a member: the set without it (the
`panic("removing missing watcher!")` is excluded by the premise). -/
abbrev mvcc.watcherSet.delete.spec : Prop :=
  ∀ (m : GoMap) (S : GMap Loc Unit) (wa : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherSet m S ∗ ⌜S !! wa = some ()⌝ }}
    (App (Val (m @!! watcherSet.ty @!! go!"delete")) (Val #wa))
  {{ RET #(); mvcc.ownWatcherSet m (GMap.delete wa S) }}

end spec

end EtcdGrove
end Perennial
