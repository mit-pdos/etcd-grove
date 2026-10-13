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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.compact(trace, rev, prev, prevCompactionCompleted)` (`compactJobPre`): the job scheduled
(`scheduleCompaction`, then the hash stored, `hashStorage.Store`: an axiom with no effect; on a
cancelled context or a failed pass, the barrier), the channel it closes returned with the
receive right (`compactChan`: a receive gives `compactDone s γ rev`). -/
abbrev mvcc.store.compact.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev prev : w64) (pcc : Bool),
  trace ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.compactJobPre s γ rev }}
    (App (App (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compact")) (Val #trace))
      (Val #rev)) (Val #prev)) (Val #pcc))
  {{ (ch : GoChan), RET #ch; mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev)) }}

end spec

end EtcdGrove
end Perennial
