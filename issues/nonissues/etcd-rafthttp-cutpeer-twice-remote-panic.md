---
upstream: none
checked: 2026-10-23
links:
  - etcd-io/etcd#6140 pr closed: related (2016: the network partition tests CutPeer/MendPeer were added for; the intent: a test hook)
  - etcd-io/etcd#6154 pr merged: related (2016: added Transport.CutPeer/MendPeer, with remote.Pause as g.stop(), which closes the pipeline's stopc); where the bug starts
  - etcd-io/etcd#4427 issue closed: related, not this bug (2016: "close of closed channel" in peer.stop from Transport.Stop after a member removal, before CutPeer existed)
---

> Moved to `issues/nonissues/` on 2026-10-23 (review of `issues/INDEX-reviewed.md`): not an issue: a precondition of a test hook (`Pausable`, "a testing interface"); no test cuts a remote twice (checked at upstream `3aaab3479b`, 2026-10-23), the same pattern as `etcd-bridge-blackhole-twice-panic`.

# server/etcdserver/api/rafthttp: a second `CutPeer` of a remote panics

- **Status**: a test hook's undocumented precondition, not a bug any caller reaches (review of
  2026-10-23 below): `Transport.CutPeer(id)` (and `EtcdServer.CutPeer`, which the
  integration tests' `InjectPartition` calls) is not idempotent for a *remote*: a second call
  without a `MendPeer` in between panics with "close of closed channel". A remote exists only on a
  member that joined an existing cluster (`bootstrapExistingClusterNoWAL` sets
  `bootstrappedCluster.remotes`, and `NewServer` calls `AddRemote` for each), so a new cluster's
  members are not affected; `Transport.Stop` after a `CutPeer` of a remote panics the same way.
  `MendPeer` of a never-cut or already-mended remote starts the pipeline's goroutines again
  (`pipeline.start`), leaking them and the old buffered messages; it does not panic.
- **Where**: the fork `upamanyus/etcd` at `8a24be2a3` (`etc/goose.py`'s etcd pin).
  `Transport.CutPeer` (`server/etcdserver/api/rafthttp/transport.go:234-246`) calls `Pause` on
  the peer and on the remote of `id`; `remote.Pause` (`remote.go:89-91`) is `g.stop()`, which is
  `g.pipeline.stop()` (`remote.go:85-87`); `pipeline.stop` (`pipeline.go:81-83`) does
  `close(p.stopc)` unconditionally. `peer.Pause` (`peer.go:297-303`) only sets a flag, so a peer
  may be cut any number of times. `EtcdServer.CutPeer` (`server/etcdserver/server.go:2166-2171`)
  forwards to the transport.
- **What happens**: the second `CutPeer` panics. Reproduction (a test in package `rafthttp`,
  `go test -run TestTransportCutPeerTwiceRemote ./server/etcdserver/api/rafthttp/`; it passes,
  i.e. confirms the panic, at the pin):

  ```go
  func TestTransportCutPeerTwiceRemote(t *testing.T) {
  	tr := &Transport{
  		Logger:      zap.NewNop(),
  		ID:          types.ID(1),
  		ServerStats: stats.NewServerStats("", ""),
  		LeaderStats: stats.NewLeaderStats(zap.NewNop(), ""),
  		peers:       map[types.ID]Peer{},
  		remotes:     map[types.ID]*remote{},
  	}
  	tr.AddRemote(types.ID(2), []string{"http://127.0.0.1:0"})
  	tr.CutPeer(types.ID(2))
  	defer func() {
  		if r := recover(); r != nil {
  			t.Logf("second CutPeer panicked: %v", r) // close of closed channel
  			return
  		}
  		t.Fatal("second CutPeer did not panic")
  	}()
  	tr.CutPeer(types.ID(2))
  }
  ```
- **Expected**: `CutPeer`'s documentation ("drops messages to the specified peer") and
  `MendPeer`'s ("recovers the message dropping behavior") describe a state, not a one-shot
  operation; `Pause`/`Resume` on a peer are idempotent, and the integration tests
  (`tests/framework/integration/cluster.go`, `InjectPartition`/`RecoverPartition`) treat them so.
- **How the proof handles it**: the transport's ghost state records the ids `AddRemote` was
  called with (`transportLive γn t rs`, `transportRemotes t rs`,
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvBoot.lean`), and the axioms of
  `Transport.CutPeer`/`MendPeer` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/`) take
  `id ∉ rs`. `bootstrap`'s contract records that a new cluster's bootstrap has no remotes
  (`bootOk`'s `Hrms0`: the contract already describes only that case, its storage fresh and raft
  started by `StartNode`), so `srvNetMember` carries `transportRemotes t []` and the server's
  `CutPeer`/`MendPeer` (`Spec/.../etcdserver/EtcdServer__CutPeer.lean`) are proved for a new
  cluster's member only.
- **Possible fixes**: make `remote.Pause`/`Resume` idempotent (a `paused` flag under a mutex, as
  `peer` has, or a guarded `pipeline.stop`), or have `remote.Pause` pause rather than stop the
  pipeline (drop in `send` while paused, as `peer.send` does).
- **A data race in the same hook** (by code reading, 2026-10-22, the rafthttp plan's inventory,
  `notes/rafthttp-plan.md`): `remote.Resume` (`MendPeer`) is `pipeline.start()`, which assigns
  `p.msgc` and `p.stopc` (`pipeline.go:64-66`), while `remote.send` reads `g.pipeline.msgc` with
  no lock (`remote.go:54-55`); `Transport.Send` holds `t.mu.RLock` for it, but `MendPeer` releases
  that lock before calling `Resume` (`transport.go:249-262`). A `Send` to a remote concurrent with
  `MendPeer` of it is a data race (the race detector would report it); test hook only, as above.
- **Found**: 2026-10-20, stating the axiom of `Transport.CutPeer` for the partition example
  (`notes/partition-plan.md`, stage S1).

## Review, 2026-10-23: misuse of a test hook, not a bug

Question: is this a bug, or is calling `CutPeer` twice a misuse? Checked at etcd upstream `main`
`3aaab3479b` (2026-10-22).

- **The API is a test hook.** `CutPeer`/`MendPeer`
  (`server/etcdserver/api/rafthttp/transport.go:233-260`) are documented only as "drops messages
  to the specified peer" / "recovers the message dropping behavior", and they call through
  `Pausable` (`transport.go:420`: "Pausable is a testing interface for pausing transport
  traffic"). `EtcdServer.CutPeer`/`MendPeer` (`server/etcdserver/server.go:2165-2179`) forward to
  them. Their only callers are the integration framework's `Member.InjectPartition`/
  `RecoverPartition` (`tests/framework/integration/cluster.go:1355-1370`) and the unit test
  `TestTransportCutMend` (`server/etcdserver/api/rafthttp/transport_test.go:72-99`, fake peers
  only, one cut then one mend). No non-test caller: etcd never cuts a peer in production.
- **Intent.** Added by `937ae658d` (etcd-io/etcd#6154, 2016-08-10, "From #6140", the network
  partition tests); `remote.Pause` was written as `g.stop()` and `Resume` as
  `g.pipeline.start()` in that commit, with no thought of repeated calls. The commit and the tests
  pair each cut with one mend.
- **No upstream test reaches it.** A remote exists only on a member started with
  `ClusterStateExisting` and no WAL (`bootstrapExistingClusterNoWAL`,
  `server/etcdserver/bootstrap.go:343-372`; `NewServer` adds them, `server.go:431-435`). The
  partition tests (`tests/integration/network_partition_test.go`, `revision_test.go`,
  `clientv3/ordering_util_test.go`, `clientv3/watch/v3_watch_restore_test.go`,
  `clientv3/connectivity/{dial,network_partition}_test.go`) partition members of a new cluster
  only, so they never cut a remote; each pair is cut once per partition (no overlapping
  `InjectPartition`s). Some never recover (`connectivity/dial_test.go:156`,
  `connectivity/network_partition_test.go:134`), so `Transport.Stop` after a cut remote would
  panic there too, but again only with a joined member.
- **The asymmetry is real but confined to the hook.** `peer.Pause`/`Resume` (`peer.go:297-312`)
  are idempotent flag writes; `remote.Pause` (`remote.go:89-91`) closes `pipeline.stopc`
  unconditionally (`pipeline.go:81-83`), and `Resume` restarts goroutines (`pipeline.go:64-70`).
  That argues the remote side was not designed for repeated calls, not that a caller relies on
  them. The same pattern as `nonissues/etcd-bridge-blackhole-twice-panic.md` (a non-idempotent
  test helper whose callers pair each call).
- **Upstream search** (`repo:etcd-io/etcd CutPeer`): only #6140 and #6154.

Verdict: a precondition of a test hook (cut a remote at most once between mends, mend before
stopping), not reached by any upstream test or production path. Move to `issues/nonissues/`. A
guarded `pipeline.stop` (or a `paused` flag in `remote`) would be a harmless hardening if a test
that partitions a joined member is ever written. The proof's premise (`id ∉ rs`, a new cluster's
member) stays as it is.
