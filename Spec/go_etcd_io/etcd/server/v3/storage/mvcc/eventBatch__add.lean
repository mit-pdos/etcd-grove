/-
`(*eventBatch).add(ev)` (internal): `EBatch.add` (the batch past `watchBatchMaxRevs` revisions takes
nothing; a new revision past the limit sets `moreRev`).

**Proof sketch.** Reads `watchBatchMaxRevs` (`watch_init.spec`), the last event's and the new one's
`Kv.ModRevision`; `append`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def eventBatch.add.spec : Prop :=
  ∀ (eb : Loc) (E : EBatch) (p : Loc) (e : EvM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ ebOwn eb E ∗ evOwn p e }}
    (App (Val (eb @!! go.GoType.PointerType eventBatch.ty @!! go!"add")) (Val #p))
  {{ RET #(); ebOwn eb (E.add e) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
