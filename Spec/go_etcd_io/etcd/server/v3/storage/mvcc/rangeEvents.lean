/-
`rangeEvents(lg, b, minRev, maxRev, c)` (internal): the storage's key-values of the revisions
`[minRev, maxRev)` (`minRev` raised to `0` with a warning) whose key `c` contains, as fresh events in
revision order.

**Proof sketch.** `RevToBytes` of both bounds (3e's); `b.ReadTx()`, `tx.RLock()` (the borrowed
loop slot of `wsReadAt`), `UnsafeRange(Key, min, max, 0)` (3e's storage contract, `ApiStorage.lean`:
`rangeOk` with `KeyData.rtRange` on the shared read transaction, the entries of the visible data in
key (revision) order, their bytes lent, `rangeLent`), `kvsToEvents` (its spec, the bytes given
back), `tx.RUnlock()` after it (the values are copied by the unmarshal). What the entries are: 3e's
`mvccImage_above.spec` (`Internal.lean`): above `h.compacted` exactly the history's events, each
at `revBytes ⟨r, i⟩` encoding `evM` (`kvBytes`), and every entry parses (`revOfBytes`). **At
`h.compacted` itself** (`lo = h.compacted`: `chooseAll` keeps a watcher whose `minRev` equals the
compaction revision) the law says nothing yet: needed of 3e (requested at integration) that an
entry of main revision `h.compacted` is that revision's event at its sub-revision, and that each
event of it that is its key's last change in it is present (the fork keeps a tombstone at the
compaction revision, etcd-io/etcd#19188); under the compaction condition (`exactFrom h lo`: each
key once in it) that is every event of it. Below `h.compacted` nothing is read (the premise:
`syncWatchers`' `minRev` is `chooseAll`'s, at least the compaction revision).

**Changes** (integration): the premise `h.compacted ≤ lo` (without it the post is false: a
compaction removed the earlier revisions' entries).
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

def rangeEvents.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (b : GoInterface) (lg : Loc) (h : KVHist) (minRev maxRev : w64)
    (wg : Loc) (v : watcherGroup) (dq dq' : DFrac) (G : List (Loc × MRange)),
  let lo := (max (sint.Z minRev) 0).toNat
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsReadAt s γ b lg h ∗ wg ↦{dq} v ∗ wgOwn v dq' G ∗ ⌜sint.Z maxRev = h.rev + 1 ∧ h.compacted ≤ lo⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.rangeEvents)) (Val #lg)) (Val #b)) (Val #minRev))
      (Val #maxRev)) (Val #(interface.mkOk (go.GoType.PointerType watcherGroup.ty) #wg)))
  {{ (evs : GoSlice), RET #evs; wsReadAt s γ b lg h ∗ wg ↦{dq} v ∗ wgOwn v dq' G ∗
      ∃ (ps : List Loc) (es : List EvM), evs ↦* ps ∗ ([∗list] p; e ∈ ps; es, evOwn p e) ∗
        ⌜exactFrom h lo →
          es = (((List.range' lo (h.rev + 1 - lo)).flatMap
                  (fun n => (h.eventsAt n).map (fun e => (n, e)))).filter
                (fun x => decide (∃ y ∈ G, y.2.watchMem (evKey x.2)))).map (fun x => evOf x.1 x.2)⌝ }}

end spec

end Mvcc
end EtcdGrove
end Perennial
