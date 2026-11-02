---
upstream: none
checked: 2026-11-02
links:
  - etcd-io/raft#551 issue open: related, not this bug: with AsyncStorageWrites, a candidate's MsgVote is sent before its term and vote are durable
blocks-proof: no
---
# raft: `doc.go` lets a follower send its acknowledgement before the entries it acknowledges are durable

[doc.go's step 2](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/doc.go#L79-L86)
says "Messages may be sent while entries from the same batch are being persisted", for any node,
while [`Ready.Messages`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/node.go#L98-L101)
says that without async storage writes "these messages must be sent AFTER Entries are appended to
stable storage". Read literally, doc.go lets a follower send its `MsgAppResp` for entry `i` (or a
vote) while `i` is still being written: if it crashes before the write is durable, the leader may
have committed `i` on that acknowledgement, and a later leader elected without it can overwrite it.

**Why not an issue:** documentation only, found by code reading, no test; the parenthesis is safe
for the leader (its own acknowledgement of its new entries is stepped at `Advance`, after the
application persisted them), and etcd sends before saving only as leader
(`raftNode.start`,
[server/etcdserver/raft.go](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/raft.go#L239-L256)).

## Proof

no: the current proof has no crash model (`notes/STATUS.md`, "Out of scope for now"); the
durability plan makes every message of a `Ready` conditional on the batch being persisted, which
is `node.go`'s contract (`notes/raft-durability-plan.md`, §4.2).

## Notes

A doc fix: reword the parenthesis to "(the leader may send its messages while the entries from the
same batch are being persisted, see below)", or keep only the §10.2.1 sentence, scoped to the
leader. Found 2026-10-28 reading raft's durability contract while planning the durability proof.
Upstream searched 2026-11-02 (`Messages persisted batch`, `Ready Messages before persist`): only
#551, on the async mode.
