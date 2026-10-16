---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#17223 issue closed: same crash (a Snapshot RPC committing on the closed backend during shutdown); closed as fixed by grpc-go's GracefulStop waiting for handlers, which does not cover the two cases below
  - etcd-io/etcd#17790 pr closed: graceful stop under cmux/TLS, one of the two cases; not merged
  - etcd-io/etcd#17757 pr merged: related, not this bug (a panic during defrag made fatal)
  - etcd-io/bbolt#715 issue closed: the same crash seen in the robustness tests
---

# etcdserver: shutdown closes the backend while gRPC handlers may still use it

- **Status**: bug (a nil-dereference panic during shutdown); not reproduced at the pin, from code
  reading and the upstream report.
- **Where**: `server/embed/etcd.go:413-480` (`Etcd.Close`) and `:487-522` (`stopServers`);
  `server/etcdserver/server.go:827` (`run`'s shutdown calls `Cleanup`) and `:942-957`
  (`Cleanup` closes the backend); `server/storage/backend/backend.go:481-487` (`Close`),
  `batch_tx.go:381-406` (`unsafeCommit(stop=true)`), `read_tx.go:133-138` (`reset`: `tx = nil`), at
  the pinned `107edf7e4`.
- **What happens**: `Etcd.Close` stops the gRPC servers, then `e.Server.Stop()`, which ends
  `run`; `run`'s shutdown calls `Cleanup`, which closes the backend (the last commit resets the
  read transaction to `nil` and begins no new batch transaction; then bbolt's `db.Close`).
  `stopServers` waits for in-flight handlers only through `grpc.Server.GracefulStop`. It calls
  `grpc.Server.Stop()` instead (1) when the gRPC server runs under the HTTP server with TLS
  (`ss.secure && ss.http != nil`) and (2) when `GracefulStop` takes longer than the request
  timeout (a long `Snapshot` or `Watch` stream). `Stop` returns without waiting for method
  handlers unless the server was built with `grpc.WaitForHandlers(true)` (grpc-go v1.84
  `server.go:645-654`), which etcd does not set. A handler still running then reads or commits on
  the closed backend: `maintenanceServer.Snapshot` → `backend.Snapshot` → `batchTx.Commit` → the
  consistent-index hook → `batchTx.UnsafeRange` on a closed transaction (the trace in
  etcd-io/etcd#17223), or a serializable `Range` → `ConcurrentReadTx` with `tx == nil`.
- **Expected**: no panic on a client request during shutdown: the backend closed only after
  every handler that may use it has returned, or such handlers get an error.
- **How the proof handles it**: the backend's verified specs exclude it: `batchTxBuffered.Commit`
  and the readers hold a share `bOpen γ q` of the backend being open, and `backend.Close` needs
  all of it (`bOpen γ 1`, `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Close.lean`).
  The server's proof lets it through by the names-only axiom `EtcdServer.Cleanup.wp_proof`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Cleanup.lean:24`), whose precondition
  has no backend token: a postulate stronger than the code, since the store's reader slots keep
  shares of `bOpen` (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/InvStore.lean`, `kbRT`)
  that `Cleanup` invalidates. `notes/bug-triage/etcd-17223.md` has the argument and the proposed
  restatement.
- **Possible fixes**: build the gRPC servers with `grpc.WaitForHandlers(true)` so that `Stop`
  waits for handlers too, and use a graceful stop under TLS (PR #17790's approach); or count the
  backend's users and make `Close` wait for them (fuweid's `txRef` sketch in #17223).
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#17223.
