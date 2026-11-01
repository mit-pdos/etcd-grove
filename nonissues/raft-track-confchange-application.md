---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/etcd#4203 issue closed: related, flagged: asked in 2016 whether a Ready's conf change must be applied before Advance (maintainer: 'probably fair'); closed by etcd-io/etcd#4049, whose Advance comment allows Advance while applying without that exception; the safety consequence was not raised
  - etcd-io/raft#80 issue open: related, not this bug: the pendingConfIndex > applied proposal check gives false positives; proposes tracking the configuration explicitly
  - etcd-io/raft#234 issue closed: related, not this bug: split brain with a stalled apply; closed citing hasUnappliedConfChanges (assumes conf changes applied before the applied index moves)
blocks-proof: no
---
# raft: track which conf changes have been applied, so that `Advance` before `ApplyConfChange` is safe

A proposal, not a bug: raft's guards against overlapping configuration changes
(`hasUnappliedConfChanges`, `pendingConfIndex > applied`, auto-leave) read the applied index, which
`Advance` moves, while the configuration changes only in `ApplyConfChange`. raft would record the
index of every conf change entry it hands out and match each `ApplyConfChange` call with the
oldest, so that the guards follow the conf changes actually applied (opt-in,
`Config.TrackConfChangeApplication`; prototype `raft-conf-lag-model/guard-fix.patch`, against
`40f8be7`).

**Why not an issue:** a design proposal, not a bug (INDEX-reviewed.md's Plan: "Nonissue"); the
bug it addresses is [`raft-advance-before-applyconfchange`](../issues/raft-advance-before-applyconfchange.md),
whose candidate takes the documentation fix instead.

## Proof

no: the proposal changes no code the proof covers.

## Notes

Not filed (2026-10-21): default-on tracking needs one `ApplyConfChange` call per handed-out conf
entry, which `Node.ApplyConfChange`'s own comment (do not pass a rejected change) and etcd's
restart path (it skips replayed conf entries below its consistent index) break, leaving nodes
unable to campaign; opt-in, it fixes nothing for existing applications (etcd-io/raft#80's
direction). The prototype also fixes `raft-snapshot-during-apply-stale-confchange`.
