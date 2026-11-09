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
