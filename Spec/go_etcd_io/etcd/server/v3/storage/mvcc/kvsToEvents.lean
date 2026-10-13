/-
`kvsToEvents` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
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

/-- `kvsToEvents(lg, c, revs, vals)` of the bucket entries `ents` (`revs`/`vals` read-only slices
of their keys and values, in order, readable through `Rd` under the reader's token `Tok`, kept; each value the encoding of a key-value, so `proto.Unmarshal`
returns `nil`: the `lg.Panic` is unreachable), for the group `g` as the `contains` interface: a
fresh slice of fresh events, read-only for good (`evIs`), one per entry whose key some member
covers, in order: a tombstone a `DELETE` with the revision as `ModRevision` (`entsEvents`). -/
abbrev mvcc.kvsToEvents.spec : Prop :=
  ∀ (lg g : Loc) (W : GMap Loc mvcc.WatchRange) (revs vals : GoSlice) (ents : List mvcc.KvEnt)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup g W ∗ mvcc.pairVals Rd revs vals (ents.map mvcc.KvEnt.pair) ∗
      mvcc.rdCap Rd Tok ∗ Tok ∗
      ⌜∀ e ∈ ents, 0 ≤ sint.Z e.rev.main ∧ 0 ≤ sint.Z e.rev.sub⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.kvsToEvents)) (Val #lg))
      (Val #(interface.mkOk (go.GoType.PointerType watcherGroup.ty) #g))) (Val #revs)) (Val #vals))
  {{ (evs : GoSlice), RET #evs; mvcc.ownWatcherGroup g W ∗ Tok ∗
      ∃ ps : List Loc, evs ↦* ps ∗ ownSliceCap Loc evs (DFrac.own 1) ∗
        ⌜ps.length = (mvcc.entsEvents W ents).length⌝ ∗
        [∗list] x ∈ ps.zip (mvcc.entsEvents W ents), mvcc.evIs x.1 x.2 }}

end spec

end EtcdGrove
end Perennial
