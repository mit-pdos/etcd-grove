/-
`eventBatch.add` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchBatch.lean`.
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

/-- `eb.add(ev)`: the batch with the event added (`ebAdd`; the cap is the package's
`watchBatchMaxRevs`). -/
abbrev mvcc.eventBatch.add.spec : Prop :=
  ∀ (eb : Loc) (B : mvcc.EventBatch) (e : Loc) (ev : mvcc.EvM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownEventBatch eb B ∗ mvcc.evIs e ev }}
    (App (Val (eb @!! go.GoType.PointerType eventBatch.ty @!! go!"add")) (Val #e))
  {{ RET #(); mvcc.ownEventBatch eb (mvcc.ebAdd B ev) }}

end spec

end EtcdGrove
end Perennial
