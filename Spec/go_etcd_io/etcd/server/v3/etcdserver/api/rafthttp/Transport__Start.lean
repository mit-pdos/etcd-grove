/-
`(*rafthttp.Transport).Start()` (`transport.go`). Lean-first; for `NewServer` since stage N0
(2026-10-16, D13), an axiom from unit N4 (2026-10-17, D14e) to rafthttp stage 6d (2026-10-24),
which restated it over the transport's state (`TransportState.lean`) and proved it over its
callees' specs (`rafthttp.Transport.Start_ok`, `TransportSpecs.lean`; linked in stage 6f).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`t.Start()`** on a transport `t` the caller owns whole (`NewServer`'s literal, its mutex
fresh), its logger and stats set, for member `tv.ID` of the network `γn` (one with peer URLs),
its URLs read-only, its `Raft` the member's (`netRaftOk`: the calls the transport makes into it,
each borrowing an `R`), its snapshotter and the snapshot directory, the network's HTTP side ready
(`netHttpOk`: the streams' registry, the other members' hosts registered with the raft protocol): an
error, or the transport live with no peer or remote yet (`trLive`: `AddPeer` and `AddRemote`
record the ids they add), all its lock's reader tokens (`trTok`), and, once frozen (`trFrozen`,
`trLive_freeze`), the network's transport of its member (`netTransport`: `Send` of the member's
messages with a token, `Stop`, `SendSnapshot`) and its `ActiveSince` (`isTransporter`).

(Until stage 6d it also took the member's slot, `netSlot`, and `netProcSlots` copies of `R`,
and asserted what the transport's goroutines and handlers do; these are now proved: each peer's
goroutines borrow eight `R`s from `AddPeer`, a remote's four from `AddRemote`, each request the
handler serves one from `Serve`, `Handler`'s.) -/
abbrev rafthttp.Transport.Start.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (tv : rafthttp.Transport) (R : IProp GF) (γd : GName)
    (Rm : w64 → IProp GF) (uvs : List net.url.URL),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      t ↦ tv ∗
      ⌜tv.Logger' ≠ null ∧ tv.ServerStats' ≠ null ∧ tv.LeaderStats' ≠ null ∧
        tv.mu' = zero_val _root_.Perennial.sync.RWMutex ∧ γn.dir tv.ID' ≠ []⌝ ∗
      tv.URLs' ↦*□ uvs ∗ □ netRaftOk γn tv.ID' γd R tv.Raft' ∗
      snap.isSnapshotter tv.Snapshotter' ∗
      inv snapDirN (snapDirInv tv.Snapshotter' γd γn.N.img Rm) ∗ netHttpOk γn tv.ID' }}
    (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Start")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗ ∃ c : TrN GF, ⌜c.lid = tv.ID' ∧ c.γd = γd ∧ c.R = R⌝ ∗
        trLive γn t c ([], []) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), trTok γn t c) ∗
        □ (∀ rs : trIds, trFrozen γn t c rs -∗
          netTransport γn c.lid (interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t)
            (trTok γn t c) ∗
          rafthttp.isTransporter (interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t)) }}

end spec

end EtcdGrove
end Perennial
