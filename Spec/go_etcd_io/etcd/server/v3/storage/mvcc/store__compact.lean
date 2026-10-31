/-
`store.compact` (`kvstore.go`): the compaction job scheduled (2026-10-13, unit 5a).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.compact(trace, rev, prev, prevCompactionCompleted)` (`compactJobPre`), with the compaction
jobs' queue at `rev` (`compactQueue`, the compaction right's: the index compactor's token at or
below `rev` once the jobs scheduled before have run; 2026-10-13, unit 5c): the job scheduled,
tracked (`scheduleCompaction` with the token, then the hash stored, `hashStorage.Store`: an axiom
with no effect; on a cancelled context or a failed pass, the barrier; the token handed on at or
below `rev` in every case), the queue back with the job's `Post` last, the channel it closes
returned with the receive right (`compactChan`: a receive gives `compactDone s γ rev`). The
scheduler is read through a share of the fields at the objects `o` (the compaction right's
closer's, `compactRightR`), given back; the job leases its own (`compactJobPre`'s `storeStopR`;
M2, the storage side, item 17). -/
abbrev mvcc.store.compact.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev prev : w64) (pcc : Bool) (te : Bool) (q : Qp)
    (o : mvcc.StoreObjs),
  trace ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.compactJobPre s γ rev ∗
      mvcc.compactQueue γ (sint.Z rev) ∗ traceutil.ownTrace trace te ∗ mvcc.fieldShareAt s γ q o }}
    (App (App (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compact")) (Val #trace))
      (Val #rev)) (Val #prev)) (Val #pcc))
  {{ (ch : GoChan), RET #ch; mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev)) ∗
      mvcc.compactQueue γ (sint.Z rev) ∗ traceutil.ownTrace trace te ∗ mvcc.fieldShareAt s γ q o }}

end spec

end EtcdGrove
end Perennial
