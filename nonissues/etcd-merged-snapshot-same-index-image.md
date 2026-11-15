---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: yes
---
# etcdserver: two merged snapshots of one index can leave a follower's backend and raft configuration apart

A follower's snapshot database is saved as `<index>.snap.db` by rafthttp before the message is
stepped into raft, so a second `MsgSnap` of the same index overwrites the file even when raft
rejects the second snapshot. Two leaders (or one leader twice) can send merged snapshots of one
index `i` whose databases are at different consistent indices: a leader still replaying after a
restart merges at its applied index `i` with its backend (and `ConfState`) at `c > i`; another at the
same applied index with its backend at `c' ≠ c`. If a conf change lies between `c` and `c'`, the
follower installs raft's snapshot with one configuration (`ConfState` of the accepted message) and
opens the other message's database: the entries between the two points are then replayed for the
membership only (below the backend's consistent index), so raft's tracker misses a committed conf
change, or applies one twice.

**Why not an issue:** found by code reading, no test; it needs two merged snapshots of one index
from members at different consistent indices with a conf change between them, both arriving before
the follower opens the file, which a restart's replay window and a leader change must line up for.

## Proof

yes: 2d's `snapImage` (the image installed with a snapshot is at that snapshot's point) is a scope
restriction for this case: a member never saves two merged snapshots of one index with different
points before installing one (batch 2d, round 1, provability F4; an open question for the user).

## Notes

A fix: name the database file by index and term (or by a digest the snapshot's metadata carries),
or have `applySnapshot` read the configuration from the opened database and hand it to raft.
