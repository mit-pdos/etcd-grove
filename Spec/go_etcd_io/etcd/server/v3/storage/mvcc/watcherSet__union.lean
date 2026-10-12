/-
`watcherSet.union` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchGroup.lean`.
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

/-- `w.union(ws)` (a map value receiver) of a set disjoint from `w` (what its callers
guarantee: a watcher is in one key set or one interval set; the premise keeps `add` from
panicking): `w` holds both. `ws` may be `nil` (`watcherSetByKey`'s `keyWatchers[key]` of a key
with no set), an empty range. -/
abbrev mvcc.watcherSet.union.spec : Prop :=
  ∀ (m : GoMap) (S : GMap Loc Unit) (m' : GoMap) (S' : GMap Loc Unit),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherSet m S ∗ mvcc.ownWatcherSetOpt m' S' ∗ ⌜S ##ₘ S'⌝ }}
    (App (Val (m @!! watcherSet.ty @!! go!"union")) (Val #m'))
  {{ RET #(); mvcc.ownWatcherSet m (S ∪ S') ∗ mvcc.ownWatcherSetOpt m' S' }}

end spec

end EtcdGrove
end Perennial
