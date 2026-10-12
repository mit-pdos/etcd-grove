/-
`watcherSetByKey.add` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchGroup.lean`.
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

/-- `w.add(wa)` (a map value receiver) of a single-key watcher `wa` not among the members `W`:
the key map of the members with it (a fresh set made for its key if the key has none). -/
abbrev mvcc.watcherSetByKey.add.spec : Prop :=
  ∀ (km : GoMap) (KM : GMap GoString GoMap) (W : GMap Loc mvcc.WatchRange) (wa : Loc)
    (r : mvcc.WatchRange) (fcs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownKeyMap km KM W ∗ mvcc.watcherFixed wa r fcs ∗ ⌜W !! wa = none ∧ r.end? = none⌝ }}
    (App (Val (km @!! watcherSetByKey.ty @!! go!"add")) (Val #wa))
  {{ RET #(); ∃ KM', mvcc.ownKeyMap km KM' (<[wa := r]> W) }}

end spec

end EtcdGrove
end Perennial
