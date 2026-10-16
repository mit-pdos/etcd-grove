---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22440 issue open: this bug
  - etcd-io/etcd#22441 pr open: answers 400 to a MsgSnap without a Snapshot (the fix)
  - etcd-io/etcd#22561 pr open: the same check, a second proposed fix
---

# rafthttp: `snapshotHandler` panics on a `MsgSnap` without a `Snapshot`

- **Status**: a bug (a reachable nil pointer dereference from one malformed peer message; a
  regression of raft v3.7's protobuf-go `raftpb`, where `Message.Snapshot` became a `*Snapshot`,
  on etcd `main` since `4715a5474`, 2026-05-27, an ancestor of the pin). `net/http` recovers a
  handler's panic and aborts the request, so the member likely survives; the request gets no
  answer instead of a 400.
- **Where** (etcd pin `107edf7e4`): `server/etcdserver/api/rafthttp/http.go:208`
  (`snapshotHandler.ServeHTTP`). After decoding the message it checks only `m.GetType() !=
  raftpb.MsgSnap` (`:251`), then reads `m.Snapshot.Metadata.GetIndex()` at `:272`, `:279`, `:286`
  and `:301` with no check that `m.Snapshot` is non-nil. Reaching the handler takes the peer TLS
  (if configured) and the `X-Etcd-Cluster-ID` header check (`checkClusterCompatibilityFromHeader`).
- **What happens**: a POST to `/raft/snapshot` whose body is a well-formed `Message{Type: MsgSnap}`
  without field 9 decodes with `m.Snapshot == nil`, and the handler panics at `:272`. Reproduction:
  `issues/etcd-rafthttp-snapshot-handler-nil-snapshot/snapshot_handler_nil_snapshot_test.go`
  (dropped into `server/etcdserver/api/rafthttp/`; `go test ./etcdserver/api/rafthttp/ -run
  TestSnapshotHandlerMsgSnapWithoutSnapshot -v` from `server/`). It fails at the pin: `snapshotHandler
  panicked on a MsgSnap without a Snapshot: runtime error: invalid memory address or nil pointer
  dereference`. It passes once the handler answers 400.
- **Expected**: a malformed message is rejected with `400 Bad Request`, as the handler does for a
  decoding error or a wrong message type.
- **How the proof handles it**: outside the verified code. `rafthttp` is translated names-only
  (`Code/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp.lean`: `snapshotHandler` is an axiomatized
  type, no bodies), so no spec covers the handler. Raft is not affected:
  `raft.handleSnapshot` (raft pin `509271dac`, `raft.go:1832-1837`) reads through `m.GetSnapshot()`
  and `pb.EnsureSnapshot`, and `MsgSnap` is outside `RawNode.Step`'s specified network types
  (`netStepTypes`, `Proof/go_etcd_io/raft/v3/InvRawnode.lean:465`). Translating the handler
  with even `{{ True }} h.ServeHTTP(w, r) {{ True }}` would catch it, since Goose makes a nil
  dereference a stuck program (`notes/bug-triage/etcd-22440.md`, proposal
  `verify-rafthttp-handlers`).
- **Possible fixes**: after the type check, reject `m.GetSnapshot() == nil` with 400 (#22441,
  #22561), and read the index through the getters (`m.GetSnapshot().GetMetadata().GetIndex()`).
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#22440 (`notes/bug-triage/etcd-22440.md`).
