/-
`watcherSetByKey.delete` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchGroup.lean`.
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

/-- `w.delete(wa)` (a map value receiver) of a single-key watcher `wa` (a member with its
range `r`, or not a member): the key map of the members without it (its key's set deleted from
the map when it becomes empty), and whether it was a member. -/
abbrev mvcc.watcherSetByKey.delete.spec : Prop :=
  ∀ (km : GoMap) (KM : GMap GoString GoMap) (W : GMap Loc mvcc.WatchRange) (wa : Loc)
    (r : mvcc.WatchRange) (fcs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownKeyMap km KM W ∗ mvcc.watcherFixed wa r fcs ∗
      ⌜r.end? = none ∧ (W !! wa = none ∨ W !! wa = some r)⌝ }}
    (App (Val (km @!! watcherSetByKey.ty @!! go!"delete")) (Val #wa))
  {{ RET #((W !! wa).isSome); ∃ KM', mvcc.ownKeyMap km KM' (GMap.delete wa W) }}

end spec

end EtcdGrove
end Perennial
