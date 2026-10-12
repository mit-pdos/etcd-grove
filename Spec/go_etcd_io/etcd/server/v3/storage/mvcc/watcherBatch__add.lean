/-
`watcherBatch.add` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchBatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchBatch

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

/-- `wb.add(w, ev)` (a map value receiver): the watcher's batch with the event added, a fresh
batch if it had none. -/
abbrev mvcc.watcherBatch.add.spec : Prop :=
  ∀ (wb : GoMap) (Bm : GMap Loc mvcc.EventBatch) (w : Loc) (e : Loc) (ev : mvcc.EvM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherBatch wb Bm ∗ mvcc.evIs e ev }}
    (App (App (Val (wb @!! watcherBatch.ty @!! go!"add")) (Val #w)) (Val #e))
  {{ RET #(); mvcc.ownWatcherBatch wb
      (<[w := mvcc.ebAdd ((Bm !! w).getD mvcc.EventBatch.empty) ev]> Bm) }}

end spec

end EtcdGrove
end Perennial
