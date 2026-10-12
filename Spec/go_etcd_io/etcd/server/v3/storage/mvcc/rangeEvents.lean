/-
`rangeEvents` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

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

/-- `rangeEvents(lg, b, minRev, maxRev, c)` over the backend `b` of the store's bucket (the
caller's view of it at a fraction, `bucketMap log` of the committed log `log`, which the caller's
certificate makes well formed), for `0 ≤ minRev ≤ maxRev ≤ log.length` (the `minRev < 0` warning
is dead), the group `g` as the `contains` interface: a fresh slice of fresh events, read-only for
good, the events of the revisions `[minRev, maxRev)` of `log` whose key some member of `g` covers,
in revision order. -/
abbrev mvcc.rangeEvents.spec : Prop :=
  ∀ (lg : Loc) (b : GoInterface) (γ : mvcc.StoreNames) (Wr P : IProp GF) (f : val) (q : Qp)
    (log : mvcc.Log) (minRev maxRev : w64) (g : Loc) (W : GMap Loc mvcc.WatchRange),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isKeyBackend b (mvcc.bucketView γ) Wr P f ∗ mvcc.bucketView γ q (mvcc.bucketMap log) ∗
      mvcc.idxCert γ.idx log ∗ mvcc.ownWatcherGroup g W ∗
      ⌜0 ≤ sint.Z minRev ∧ sint.Z minRev ≤ sint.Z maxRev ∧ sint.Z maxRev ≤ log.length⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.rangeEvents)) (Val #lg))
      (Val #b)) (Val #minRev)) (Val #maxRev))
      (Val #(interface.mkOk (go.GoType.PointerType watcherGroup.ty) #g)))
  {{ (evs : GoSlice), RET #evs; mvcc.bucketView γ q (mvcc.bucketMap log) ∗ mvcc.ownWatcherGroup g W ∗
      ∃ ps : List Loc, evs ↦* ps ∗ ownSliceCap Loc evs (DFrac.own 1) ∗
        ⌜ps.length = ((mvcc.logEvents log (sint.nat minRev) (sint.nat maxRev)).filter
          fun ev => mvcc.wgCovers W ev.kv.key).length⌝ ∗
        [∗list] x ∈ ps.zip ((mvcc.logEvents log (sint.nat minRev) (sint.nat maxRev)).filter
          fun ev => mvcc.wgCovers W ev.kv.key), mvcc.evIs x.1 x.2 }}

end spec

end EtcdGrove
end Perennial
