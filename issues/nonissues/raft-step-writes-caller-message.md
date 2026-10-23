---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/raft#418 pr merged: related, flagged: added the 'treat m as immutable' comment on Step (etcd-io/raft@c1cf9fb); a reviewer found no in-repo path mutating m after Step, which this finding contradicts
  - etcd-io/raft#441 pr merged: related, not this bug: EnsureSnapshot/EnsureSnapshotMetadata no longer reassign non-nil fields, after a race found in etcd-io/etcd#21778 (ApplySnapshot writing its argument); EnsureConfState still writes AutoLeave
---

> Moved to `issues/nonissues/` on 2026-10-23 (review of `issues/INDEX-reviewed.md`): not an issue: at most a documentation change.

# raft v3.7: `Step` writes into the caller's message and keeps it; `MemoryStorage.ApplySnapshot` writes into its argument

- **Status**: open (documentation the code contradicts; not reported). Introduced with the move of
  raftpb to protobuf-go v2 (messages passed as pointers): at `40f8be7` and earlier, `Step` took a
  `pb.Message` value and these writes went to its copy.
- **Where** (etcd-io/raft v3.7.0, `b867cf13`; the same in the fork commit `509271dac` that
  `etc/goose.py`'s project `raft37` pins):
  - `raft.go:1085-1088` (`raft.Step`'s documentation): "Callers must treat m as immutable after
    passing it to Step. Mutating it concurrently can lead to unexpected behavior." Nothing says
    that raft itself writes `m` or keeps it.
  - `raft.go:1720`, `1739`, `1761` (`stepFollower`, `MsgProp`/`MsgTransferLeader`/`MsgReadIndex`):
    `m.To = new(r.lead)` then `r.send(m)` on the stepped message; `send` (`raft.go:515-517`,
    `543`) sets `m.From` when unset and `m.Term` (for `MsgTransferLeader`) on it, and queues the
    object itself (`raft.go:592`, `598`), which `Ready.Messages` hands back to the application.
    `node.run` sets `m.From` on the proposer's message (`node.go:388`).
  - Kept after `Step` returns: `pendingReadIndexMessages` (`raft.go:1366`), `readOnly`'s requests
    (`read_only.go:61`), the forwarded messages above, responses that share the stepped message's
    `From`/`Term`/`Entries`/`Context` cells (`responseToReadIndexReq`, `raft.go:2066-2080`,
    `handleHeartbeat`), and a follower's log entries (the `*pb.Entry` objects of `m.Entries`,
    appended as they are, `log.go:127`).
  - `storage.go:216-222` (`MemoryStorage.ApplySnapshot`, "overwrites the contents of this Storage
    object with those of the given snapshot"): `pb.EnsureSnapshot(snap)` fills the caller's
    snapshot's nil `Metadata`, `Metadata.Index`/`Term` and `ConfState.AutoLeave` in place
    (`raftpb/util.go:20-67`); `raft.handleSnapshot` does the same to a received `MsgSnap`'s
    snapshot (`raft.go:1836`).
  - `storage.go:62-66` (`Storage.Entries`) refers to "comments in Ready struct" forbidding a
    handler to mutate entries; the `Ready` struct (`node.go:52-115`) has no such comment.
- **What happens**: an application that steps a message it still holds (reuses a decode buffer,
  logs it after `Step`, or steps the same object on two nodes in a test) sees raft's writes, and
  raft's queued message changes with the application's later writes. Reproduction (in package
  `raft`, passes on v3.7.0):

      func TestStepWritesAndKeepsCallerMessage(t *testing.T) {
      	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
      	r.becomeFollower(1, 2)
      	m := &pb.Message{From: new(uint64(3)), To: new(uint64(1)), Type: pb.MsgProp.Enum(),
      		Entries: []*pb.Entry{{Data: []byte("x")}}}
      	if err := r.Step(m); err != nil {
      		t.Fatal(err)
      	}
      	if m.GetTo() != 2 {
      		t.Fatalf("m.To = %d, want unchanged 1", m.GetTo())
      	}
      	msgs := r.readMessages()
      	if len(msgs) != 1 || msgs[0] != m {
      		t.Fatalf("queued %v", msgs)
      	}
      	// the caller's message was written (To 1 -> 2) and is the queued message itself
      }

  etcd's server steps messages freshly decoded by rafthttp, so no misbehaviour of etcd is known.
- **Expected**: either raft does not write or keep the caller's message (copy what it forwards or
  keeps), or `Step` documents that it takes ownership of `m` (and of `m.Entries`'s entries and
  `m.Snapshot`), as `ApplySnapshot` should for its argument.
- **How the proof handles it**: not yet (raft v3.7 is being retargeted, stage R0). The design
  (`notes/raft-retarget-plan.md`, "Design") states it as ownership: `Step` takes the message's
  cells (and the entries' read-only facts) and does not give them back.
- **Possible fixes**: document the transfer of ownership on `Step`/`RawNode.Step`/`Node.Step` and
  `ApplySnapshot`; or `proto.Clone` the message in `stepFollower`'s forwarding branches and in
  `pendingReadIndexMessages`, and clone the snapshot in `ApplySnapshot` before `EnsureSnapshot`.
- **Found**: 2026-10-15, the raft v3.7 retarget's inventory (stage R0, the message lifecycle).
