---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/etcd#6154 pr merged: related (2016: added Transport.CutPeer/MendPeer, with remote.Pause as g.stop(), which closes the pipeline's stopc); where the bug starts
  - etcd-io/etcd#4427 issue closed: related, not this bug (2016: "close of closed channel" in peer.stop from Transport.Stop after a member removal, before CutPeer existed)
---

# server/etcdserver/api/rafthttp: a second `CutPeer` of a remote panics

- **Status**: a bug in a test hook: `Transport.CutPeer(id)` (and `EtcdServer.CutPeer`, which the
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
- **Found**: 2026-10-20, stating the axiom of `Transport.CutPeer` for the partition example
  (`notes/partition-plan.md`, stage S1).
