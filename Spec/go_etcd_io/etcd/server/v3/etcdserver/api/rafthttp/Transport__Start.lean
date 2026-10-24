/-
`(*rafthttp.Transport).Start()` (`transport.go`): names-only. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16, D13: `notes/decisions.md`), for `NewServer`; an
axiom at the trust boundary since unit N4 (2026-10-17, D14e), why it is true of the Go code below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`t.Start()`** on a transport `t` the caller owns whole (`NewServer`'s literal), its logger
and stats set, for member `tv.ID` of the network `γn` (D21 M2, 2026-10-19): given the member's slot
(`netSlot`), its `Raft` (`tv.Raft`: `netRaftOk`, the calls the transport makes into it) and
`netProcSlots` copies of the resource `R` those calls borrow, an error, or the transport live
with no remote yet (`transportLive γn t []`: `AddRemote` adds to the list, `AddPeer` keeps it),
which the caller gives up for `transportStarted γn t` (`Send`, `Stop`, `ActiveSince`) and
`transportRemotes t rs`, the ids `AddRemote` was called for (the partition plan's S1,
2026-10-20: `CutPeer`/`MendPeer` take an id not among them, since a second `CutPeer` of a
remote panics, `issues/nonissues/etcd-rafthttp-cutpeer-twice-remote-panic.md`; `t.remotes` gets a key only
through `AddRemote`, which the exclusive `transportLive` serializes before the transport is given
up, so the list is complete).

What the axiom asserts of the Go code (`transport.go`, `peer.go`, `stream.go`, `pipeline.go`,
`http.go` at the etcd pin), besides `Start`'s own steps (the two round trippers from the TLS info,
an error returned e.g. for an unreadable certificate; the two maps and probers; no goroutine;
the snapshotter `tv.Snapshotter` kept for the snapshot handler):
* the transport's goroutines and handlers call `tv.Raft` only as `netRaftOk` admits: `Process`
  with a fresh copy (unmarshalled: `netRecv`) of a message some member's started transport was
  given by `Send` for `tv.ID` (`Send` routes by `To` to the peer added for it, which posts to that
  peer's URLs, served by the transport holding `To`'s slot: `AddPeer`'s directory premise), with
  that message's bundle; each sent message possibly lost (writers drop on error or a full buffer,
  reporting `ReportUnreachable`), never retried, so delivered at most once if `once`; the reports
  and `IsIDRemoved` at any time; at most `netProcSlots` calls at once, each borrowing an `R`
  (physically: each is a goroutine with its own stack);
* nothing is sent on `ErrorC`: rafthttp reports only `errMemberRemoved` there, on a `403`, which no
  member answers -- none is removed (static membership) and no message reaches the wrong member
  (`issues/etcd-rafthttp-misaddressed-403-member-removed.md`, excluded by the directory).
`Send` after `Stop` finds no peer and returns; `AddPeer` after `Stop` panics, hence the exclusive
`transportLive`, given up for `Stop`; (D22 receiver epochs, S8c, 2026-10-24) and then the exclusive
peers right (`transportPeers`: `netPeers` of the member `tv.ID`, with `netTrIs`, the fact that the
started transport is `tv.ID`'s, given once since `Start` takes the member's `netSlot`), which
`Stop` takes (`netTransport`), so `AddPeer` with it finds the transport not stopped.

**The snapshot stream** (D22 S-i, 2026-10-19; `Net.lean`'s header). The started transport's
`SendSnapshot` (`netTransport`) and the snapshot handler, given the snapshotter `tv.Snapshotter`
(`snap.isSnapshotter`, `bootstrap`'s) and its directory `snapDirInv tv.Snapshotter γd γn.N.img Rm`
(an invariant the receiver allocates, `snapDir_alloc`). What the axiom asserts besides the above:
* `SendSnapshot(m)` (`transport.go:409-418`): under the transport's lock, the peer added for
  `m.GetTo()` takes `m` (`peer.sendSnap` → `snapshotSender.send`, a goroutine) or, none added,
  `m.CloseWithError(errMemberNotFound)`. The sender's goroutine (`snapshot_sender.go:66-140`)
  posts the envelope (the raft message, marshalled) and `m`'s reader's bytes to the peer's
  snapshot URL, once (no retry), then reports `ReportSnapshot(To, Finish|Failure)` to `tv.Raft`
  (the reports at any time, as above) and closes `m` (`CloseWithError`: the reader closed, one
  value on `closeC`, the only send on it). `m`'s raft message is only read (marshalled), `m`'s
  fields only read (`snap.msgIs`), its reader read by this goroutine alone (`readerStreams`).
* the snapshot handler (`http.go:208-330`): it decodes the envelope (a fresh `raftpb.Message`),
  refuses any other type than `MsgSnap`, and saves the rest of the body with
  `Snapshotter.SaveDBFrom(body, m.Snapshot.Metadata.GetIndex())` (`snap/db.go:37-90`): `io.Copy` to
  a temporary file, `Fsync`, and on success either a file of that index already exists (kept, the
  temporary removed) or the temporary is renamed to `snapDBPath ss i` (the directory synced);
  any error answers `500` and calls nothing. Only then does it call `Process` with the message, as
  any other (`netRecv`: a message some started transport was given, here by `SendSnapshot`, for
  `tv.ID`, with its bundle). The saved bytes are a complete stream of the sender's reader: the body
  is chunked and the exact-size reader `NewMessage` wraps errors on a short or long stream, so an
  aborted or truncated body is an `io.Copy` error at the receiver; so the file holds `D`
  (`boltImage bs D` read back: `fileHolds`) with `□ γn.N.img i D` from the sender's bundle. The
  ghost steps it makes on the directory: at the rename (a file created at `i`, so none is there:
  by the closed world of the data directory, `pathOwn`, no `.snap.db` file exists but the ones
  `M` holds or a holder took out of it to rename away, so `i ∉ M`), `i` added to `M` with the file
  and to `E`; nothing at a kept file (then `i ∈ E`: the file is in `M`, or was taken out of it,
  which leaves `E`). So at `Process`, `snapSaved γd i` (`netSnapRecv`). A failed post is
  reported (`ReportUnreachable`, `ReportSnapshot(Failure)`) before the close; the envelope's
  encoding cannot fail (a `bytes.Buffer`, a raft message), so its `Panic` is dead.
* a `MsgSnap` reaches `Process` only that way: `Send` takes none (`netBundle`; through `Send`
  rafthttp would post it to the message handler, `pipeline.go`, with no file saved).
Nothing else in the transport writes the directory: `.snap.db` files are removed only by the
receiver (`OpenSnapshotBackend`'s rename, `ReleaseSnapDBs` from `storage.Release`, which removes
only files *below* the released index, `snap/snapshotter.go:45-70`), each removal its own ghost
step with `Rm i`; the `.snap` files of `SaveSnap` have other names. -/
abbrev rafthttp.Transport.Start.spec : Prop :=
  ∀ (t : Loc) (tv : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport)
    (γn : NetNames GF) (R : IProp GF) (γd : GName) (Rm : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      t ↦ tv ∗
      ⌜tv.Logger' ≠ null ∧ tv.ServerStats' ≠ null ∧ tv.LeaderStats' ≠ null⌝ ∗
      netSlot γn tv.ID' ∗ □ netRaftOk γn tv.ID' γd R tv.Raft' ∗
      -- (D22 S-i) the snapshotter and its directory
      snap.isSnapshotter tv.Snapshotter' ∗
      inv snapDirN (snapDirInv tv.Snapshotter' γd γn.N.img Rm) ∗
      [∗list] _x ∈ List.replicate netProcSlots (), R }}
    (App (Val (t @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"Start")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗ transportLive γn t [] ∗
        (∀ rs : List w64, transportLive γn t rs -∗ transportStarted γn t ∗ transportRemotes t rs ∗
          netPeers γn tv.ID' ∗ netTrIs γn tv.ID' (transportIface t)) }}

end spec

end EtcdGrove
end Perennial
