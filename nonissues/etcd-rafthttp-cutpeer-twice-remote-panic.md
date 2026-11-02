---
upstream: none
checked: 2026-10-23
links:
  - etcd-io/etcd#6140 pr closed: related (2016: the network partition tests CutPeer/MendPeer were added for)
  - etcd-io/etcd#6154 pr merged: related (2016: added Transport.CutPeer/MendPeer, with remote.Pause as g.stop(), which closes the pipeline's stopc)
  - etcd-io/etcd#4427 issue closed: related, not this bug (2016: "close of closed channel" in peer.stop from Transport.Stop after a member removal, before CutPeer existed)
blocks-proof: no
---

# rafthttp: a second `CutPeer` of a remote panics with "close of closed channel"

`Transport.CutPeer(id)` of a remote (a member the transport knows only from its requests, not as a
peer) a second time without a `MendPeer` in between panics with "close of closed channel", and so
does `Transport.Stop` after a cut remote; on a peer both are idempotent. A member gets such a
remote when it joins an existing cluster, or when a removed member or a peer re-dialing during
`applySnapshot`'s peer reset sends it a request.

**Why not an issue:** a precondition of a test hook: `CutPeer`/`MendPeer` (and
`EtcdServer.CutPeer`) are called only by the integration framework's `InjectPartition`/
`RecoverPartition` and `TestTransportCutMend`, through `Pausable` ("a testing interface"), each
cut paired with one mend; no upstream test cuts a remote at all (checked at `3aaab3479b`,
2026-10-23).

## Proof

no: until 2026-11-01 the trust-boundary axioms of `Transport.CutPeer`/`MendPeer`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__CutPeer.lean`) took the id not a
remote (`trNoRemOr`), a premise on a test hook etcd never calls in production. Since then the verified
fork gives `remote` a mutex-guarded `paused` flag that `Pause`/`Resume` set and clear and `send`
checks (`goose-lean-remotepause` `ab3c28d9a`, `etc/goose.py`; `notes/decisions.md`, "A remote pauses
by a flag"), so `CutPeer` and `MendPeer` are idempotent for a remote and `Transport.Stop` after a
`CutPeer` is fine; the premise is gone. A fix the proof could have done without.

## Notes

Test: `TestTransportCutPeerTwiceRemote` in
[`etcd-rafthttp-cutpeer-twice-remote-panic/cutpeer_twice_test.go`](etcd-rafthttp-cutpeer-twice-remote-panic/cutpeer_twice_test.go)
(package `rafthttp`) fails at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-11-01):
`second CutPeer panicked: close of closed channel`. The same hook has a data race by code reading:
`remote.Resume` (`MendPeer`) reassigns `pipeline.msgc` while `remote.send` reads it without a lock.
A guarded `pipeline.stop` (or a `paused` flag in `remote`, as `peer` has, the fork's fix) would be
a harmless hardening for a test that partitions a joined member: this repository's
`TestLeaderAdvanceBeforeApplyConfChangeLosesWrite`
([`etcd-leader-advance-before-applyconfchange`](../issues/etcd-leader-advance-before-applyconfchange.md),
2026-11-02) is one, and has to cut only the old members' side to avoid the panic. The 2026-10-23 review's plan asked
whether this is a bug or a misuse; the 2026-10-23 review answered misuse.
