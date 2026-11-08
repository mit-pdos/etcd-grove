/-
`rangeEvents` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactNoDup

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

/-- `rangeEvents(lg, b, minRev, maxRev, c)` over the backend `b` of the store's bucket (the
caller's view of it at a fraction, at a bucket of the committed log `log` (`bucketViewL`: thin of
`bucketMap log` after a restore in compaction mode, M2's item 15), which the caller's certificate
makes well formed), for `0 ≤ minRev`, `0 ≤ maxRev ≤ log.length` (the `minRev < 0` warning
is dead; D22 receiver epochs, S6: `minRev` may be past `maxRev`, after a restore, and the range
is then empty), the group `g` as the `contains` interface: a fresh slice of fresh events, read-only for
good, the events of the revisions `[minRev, maxRev)` of `log` whose key some member of `g` covers,
in revision order. The backend's reader token `RT` is lent (2026-10-13, unit 5). (Watches across
a compaction, 2026-11-01, `notes/watch-compaction-plan.md`: until then the store was not
compacted, `crevFrozen`.) A share of the compaction revision's authority at `c` is lent, with the
scan at or above it. The backend's snapshot is thinned by compaction (`delKey`), so the events are
those of the entries it has (`P`, the kept entries): every entry above `c` (`snapThin_missing_le`),
and every entry of the scanned revisions when revision `c` changes each key once or there is no
compaction (`c = -1`; `snapThin_scan`). Revision `c` changing a key twice loses the earlier change
(`nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md`), which only a watcher reading from `c`
sees (per watcher, 2026-11-05: `notes/mvcc-api-invariants.md` §4.4; until then the premise). -/
abbrev mvcc.rangeEvents.spec : Prop :=
  ∀ (lg : Loc) (b : GoInterface) (γ : mvcc.StoreNames) (Wr P : IProp GF) (HF : val → IProp GF) (q : Qp)
    (log : mvcc.Log) (minRev maxRev : w64) (g : Loc) (W : GMap Loc mvcc.WatchRange)
    (RT WT NC Wi Dep : IProp GF) (Cmp : Prop)
    (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop)
    (Rb : GMap GoString backend.BktData → IProp GF)
    (Bt : GoInterfaceOk → IProp GF) (MW : backend.FkVals → backend.VData → IProp GF) (SR SRh : IProp GF) (qc : Qp) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isKeyBackendG b (mvcc.bucketView γ) RT WT NC PutOk (mvcc.delKey γ) Wr Wi Dep Cmp P HF (Rb := Rb) (Bt := Bt) (SR := SR) (SRh := SRh) (MW := MW) ∗ RT ∗
      mvcc.crevUB γ.idx qc c ∗
      mvcc.bucketViewL γ q log ∗
      mvcc.idxCert γ.idx log ∗ mvcc.ownWatcherGroup g W ∗
      ⌜0 ≤ sint.Z minRev ∧ 0 ≤ sint.Z maxRev ∧ sint.Z maxRev ≤ log.length ∧
        -1 ≤ c ∧ c ≤ sint.Z minRev⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.rangeEvents)) (Val #lg))
      (Val #b)) (Val #minRev)) (Val #maxRev))
      (Val #(interface.mkOk (go.GoType.PointerType watcherGroup.ty) #g)))
  {{ (evs : GoSlice), RET #evs; RT ∗ mvcc.crevUB γ.idx qc c ∗ mvcc.bucketViewL γ q log ∗
      mvcc.ownWatcherGroup g W ∗
      ∃ (P : mvcc.KvEnt → Bool) (ps : List Loc), evs ↦* ps ∗ ownSliceCap Loc evs (DFrac.own 1) ∗
        ⌜(∀ e ∈ mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev), c < sint.Z e.rev.main →
            P e = true) ∧
          ((c = -1 ∨ mvcc.oneChangePerKeyAt log c) →
            ∀ e ∈ mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev), P e = true)⌝ ∗
        ⌜ps.length = (mvcc.entsEvents W
          ((mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev)).filter P)).length⌝ ∗
        [∗list] x ∈ ps.zip (mvcc.entsEvents W
          ((mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev)).filter P)), mvcc.evIs x.1 x.2 }}

end spec

end EtcdGrove
end Perennial
