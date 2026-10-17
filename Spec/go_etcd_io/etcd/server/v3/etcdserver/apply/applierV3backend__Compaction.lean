/-
`apply.applierV3backend.Compaction` (backend.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Chain.lean` and mvcc's compaction
(`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/store__Compact.lean`). Written for etcd-io/etcd#22476
(`notes/pr-verify/etcd-22476.md`): the applier's `Compaction` is outside the apply chain's model
(`uberApplier.dispatch`'s premise `dispatchOk`), so this spec stands alone, with what
`store.Compact` needs as its premises.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Compact

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.Compaction(compaction)`** (the request's `Revision` `rev`), by the apply thread, which
holds the store's compaction right at its compaction revision `c` (`store.Compact`'s premises:
the store's backend supporting compaction, `storeStop`, a certificate of a log of which `rev` is a
revision that does not delete a key and put it again, the batch lock's hook and the caller's
critical-section contract `Pre`/`Post`), and a reader slot of the store:
* the compaction scheduled (`c < rev`): no error, the compaction right at `rev` with `Post`, the
  compaction's channel (closed once the store is compacted at `rev`), and a fresh response whose
  `Header.Revision` is the store's current revision when it was read (the last revision of a
  certified log, at least `rev`), with the trace (not nil);
* `store.Compact`'s error (`ErrCompacted` at `rev ≤ c`, `ErrFutureRev`): that error, a `nil`
  response and trace, the right unchanged with `Pre`.
There is no third case: the range read that takes the current revision (`KV.Range` at
`RangeOptions{}`, under `context.TODO()`'s trace context, never canceled) neither fails nor
returns a `nil` result, so the response is never dereferenced as `nil` and the error returned by
etcd-io/etcd#22476's new check of that read is never returned. -/
abbrev apply.applierV3backend.Compaction.spec : Prop :=
  ∀ (E : AEnv GF) (p cr : Loc) (rev : w64) (c : Int) (Pre Q Post : IProp GF) (log : mvcc.Log),
  mvcc.storeCmp E.γ → -1 ≤ c →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendIs E p ∗
      apply.compactionIs cr rev ∗
      mvcc.storeReaderC E.s E.γ ∗ mvcc.storeStop E.s ∗ mvcc.compactRight E.γ c ∗
      mvcc.idxCert E.γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.csContract E.P E.f Pre Q Post }}
    (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"Compaction")) (Val #cr))
  {{ (resp : Loc) (ch : GoChan) (trace : Loc) (err : GoInterface),
      RET (PairV (PairV (PairV #resp #ch) #trace) #err);
      mvcc.storeReaderC E.s E.γ ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev ∧ resp ≠ null ∧ trace ≠ null⌝ ∗
          mvcc.compactRight E.γ (sint.Z rev) ∗ mvcc.crevLb E.γ.idx (sint.Z rev) ∗ Post ∗
          mvcc.compactChan ch (mvcc.compactDone E.s E.γ (sint.Z rev)) ∗
          (∃ te : Bool, traceutil.ownTrace trace te) ∗
          ∃ (h : Loc) (log' : mvcc.Log),
            structFieldRef etcdserverpb.CompactionResponse go!"Header" resp ↦ h ∗
            structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ W64 ((log'.length : Int) - 1) ∗
            mvcc.idxCert E.γ.idx log' ∗ ⌜log' ≠ [] ∧ sint.Z rev < log'.length⌝) ∨
        (⌜resp = null ∧ trace = null ∧ err ≠ GoInterface.nil⌝ ∗
          mvcc.compactRight E.γ c ∗ Pre ∗
          (⌜ch = chan.nil⌝ ∨ mvcc.compactChan ch iprop(True)))) }}

end spec

end EtcdGrove
end Perennial
