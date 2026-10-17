/-
`watcher.send` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

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

/-- `w.send(wr)`: the response `wr` for the watcher `w` (its events `evm`, read-only, those of
the delivery that extends `w`'s delivered events, at or below `wr`'s revision, at or above a
positive start revision: `verify.Verify`'s check), filtered by `w`'s filters, sent on its
channel without blocking (the channel is open: `w` is live), unless all its events were filtered
out (then `true` without sending). On `true` the delivery is recorded (the events delivered
grow by `evm`; `wr`'s events are the channel's for good); on `false` (the channel full) nothing
changed. A progress response (`evm = []`) needs no delivered events. Unit W-M2: the response
carries `w`'s own id, or the channel's progress fact (`progressAll`'s response of id `-1`): the
channel's invariant keeps it for every response of id `-1`. Unit W-K (K1b): the response covers
the watchers `cs` (`covPre`: each delivered past the response's revision, registered on the
channel), which the channel's invariant keeps (`respCov`); `[]` for any but a progress response;
a response without events covers its watcher `w` (so every event-less response sent does).
A response of id `-1` comes with the caller's `CS` (lent) and `complW`: from `CS`, every watcher
registered on the channel is covered or cancelled for its reason (`respCompl`). -/
abbrev mvcc.watcher.send.spec : Prop :=
  ∀ (γ : mvcc.WsNames) (w : Loc) (γw : mvcc.WatcherNames) (r : mvcc.WatchRange) (fcs : GoSlice)
    (ch : GoChan) (qc ql : Qp) (evsw : List mvcc.EvM) (d : Nat) (wr : WatchResponse)
    (es : List Loc) (evm : List mvcc.EvM) (dq : DFrac) (cs : List mvcc.CovArg)
    (CS : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.watcherMeta γ w γw ∗ mvcc.watcherFixed w r fcs ∗ mvcc.filtersOk fcs ∗
      mvcc.watcherChan γ w γw ch ∗
      typedPointsto (structFieldRef watcher go!"ch" w) ch (DFrac.own qc) ∗
      dghostVar γw.live (DFrac.own ql) true ∗
      (if evm = [] then iprop(True) else
        monoListAuthOwn γw.evs (1 : Qp).half evsw ∗ mvcc.evsWf γ r γw.lo (evsw ++ evm) d) ∗
      wr.Events' ↦*{dq} es ∗ ([∗list] x ∈ es.zip evm, mvcc.evIs x.1 x.2) ∗
      mvcc.covPre γ γw.wc wr.Revision' cs ∗ ⌜evm = [] → w ∈ cs.map mvcc.CovArg.w⌝ ∗
      CS ∗ (⌜wr.WatchID' = r.id⌝ ∨ mvcc.complW γw ql CS (cs.map mvcc.CovArg.w) wr.WatchID' wr.Revision' evm) ∗
      ⌜es.length = evm.length ∧ wr.CompactRevision' = W64 0 ∧ (evm ≠ [] → wr.WatchID' = r.id) ∧
        (∀ ev ∈ evm, sint.Z ev.kv.modRev ≤ sint.Z wr.Revision') ∧
        (0 < sint.Z r.startRev → ∀ ev ∈ evm, sint.Z r.startRev ≤ sint.Z ev.kv.modRev)⌝ }}
    (App (Val (w @!! go.GoType.PointerType watcher.ty @!! go!"send")) (Val #wr))
  {{ (b : Bool), RET #b;
      typedPointsto (structFieldRef watcher go!"ch" w) ch (DFrac.own qc) ∗
      dghostVar γw.live (DFrac.own ql) true ∗
      (if b then wr.Events' ↦*□ es else wr.Events' ↦*{dq} es) ∗
      (if evm = [] then iprop(True) else
        monoListAuthOwn γw.evs (1 : Qp).half (if b then evsw ++ evm else evsw)) ∗ CS }}

end spec

end EtcdGrove
end Perennial
