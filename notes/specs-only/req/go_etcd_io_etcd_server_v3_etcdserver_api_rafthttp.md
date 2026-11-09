# Requirements on `go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp` (2f)

## from 2d

Answers to 2f's items in `req/go_etcd_io_etcd_server_v3_etcdserver.md` ("from 2f"), and 2d's needs:

1. (2f's 3) `EtcdServer.Process.spec` takes the thread token and returns it with `Rafthttp.procErr
   err` (`procErr_forbidden` for the 403s); `IsIDRemoved.spec` takes and returns a token;
   `ReportUnreachable`/`ReportSnapshot` need only `srvNode`. The message's `recvd` gives raft's
   `msgSent`/`msgCredit` (`Process` checks `To` itself). Callable from `NewServer` on.
2. (2f's 4) `processMessages` returns `sendable γ out msgs` (`ApiApply.lean`: each message with
   `msgPts` at `readyDq`, `msgSent`, `msgCredit`; no `MsgSnap`): 2f's `outMsg` per message, given
   `Send`'s member id (2d's realization ties `γ.raft` to `ν.γ`).
3. (2f's 6) `run` stops the scheduler (every apply done: no `AddPeer` after) before `s.r.stop()`,
   whose `onStop` stops the transport: no conf change or snapshot is applied after `Stop`.
4. (2f's 7) `mergedSnap mg γ m` (`createMergedSnapshotMessage.spec`) is 2f's `outSnap ν mg` (the
   reader's complete streams `snapImg` images of the snapshot's index: 2d's `snapImage`).
5. **2d needs**: `Transport.Send(msgs)` with `sendable`; `SendSnapshot(mg)` with `mergedSnap`;
   `AddPeer`/`RemovePeer`/`UpdatePeer`/`RemoveAllPeers` with a share of `trRunning` (the apply
   thread's, while running); `Stop` with the whole. The received `MsgSnap`'s `dbSaved ss i bs ∗ snapImg
   ν i bs` must reach the apply thread's `applySnapshot` for the snapshot of index `i` (the server's
   invariant keeps it from `Process` to the batch's install): with `snapImg ν i bs` meaning "an image
   of the state machine at `histAt γ k` for some `k ≥ i`, with stored index `k`" (2d's `snapImage`).

## from 2e

1. **The raft handler** (2f's review F1): `EtcdServer.RaftHandler.spec` gives `raftHandler h γ id`
   (provisional in `ApiBoot`), which the programs serve at the root of the member's peer listener
   (`go http.Serve(l, s.RaftHandler())`: `etcdstart.NewMember`, `restart.startMember`) or mount at `/`
   in a mux. `Transport.Handler.spec`'s post must be usable there (`handlerOk h P "/"` for every
   protocol compatible with the transport's).
2. **Re-serving a peer address after a restart** (F2): `restart.startMember` listens and serves the
   restarted member's handler on the stopped member's peer address. The serving right must be
   persistent per address and protocol (the restarted transport has the member's id and network).
   Used by the snippet `ReqRestart`, `EtcdServer.HardStop.spec`'s users.
3. **The received snapshot's database** (F3): 2e's `Snapshotter.SaveDBFrom.spec` is logically atomic
   over `Snap.snapDbs sd F` (to `Snap.saveAt F id img`, the update given back on an error), with a
   reader `Snap.dbReader r img` (provisional: please export your reader contract, one predicate for
   2d's `dbReader`, 2e's and your `outSnap`). `trCfg` should take the client's update (the server's
   invariant holds `snapDbs`), not mint a persistent `dbSaved`.
   ```go
   n, err := h.snapshotter.SaveDBFrom(r.Body, m.Snapshot.Metadata.GetIndex()) // http.go:275
   ```
4. **`Transport.Start` at `NewServer` time** (F4): the server supplies `raftOk` from what it holds
   after `bootstrap` (`srvMember`, and 2d's entry points stated over it), before `Start`.
5. **The slots**: `rafthttpBootCfg cfg` (a provisional `Prop` slot of `NewServer.spec`): replace by your
   slot, of the kind you need (a resource is fine: the hub names it once). `transporterOk tp`
   (provisional, `util.go`'s helpers, `adjustTicks`): export it as the `Transporter` bundle of the
   transport's interface value.

## from 2d (round 1)

6. `EtcdServer.Process.spec` now takes `srvNet γ ν ∗ Rafthttp.recvd ν m` (your round-1 `recvd`, with
   `ν.dbIn i` for a `MsgSnap`); the server chooses `ν.img := imgAt γ`, `ν.dbIn` its record over its
   `snapDbs` (`req/go_etcd_io_etcd_server_v3_etcdserver.md`, from 2d (round 1), item 9).
7. `srvNode_errorc` gives your `errChanOk` of `s.errorc`; `run` returns on a receive.

## from 2e, round 1

1. 2e uses your `Net`, `raftProto`, `raftCompat`, `peerAddr_reserve`, `Http.addrFree`/`protoAt`:
   `cluster_alloc` and `urls_reserve` reserve the members' peer hosts for the cluster's network
   (`srvNet γ ν`), `EtcdServer.RaftHandler.spec` gives your `Transport.Handler` post at that network.
2. The URL hosts are your provisional `urlsHosts` (1c's): keep it or tell 2e.
3. `transporterOk` (provisional in `ApiBoot`) is the `Transporter` bundle with token-taking
   `ActiveSince`/`ActivePeers`: please export it.
