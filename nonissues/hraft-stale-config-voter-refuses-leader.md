---
upstream: none
checked: 2026-11-28
links:
  - hashicorp/raft#727 issue open: related, not this bug: a leadership transfer to a non-voter
blocks-proof: no
---
# raft: a voter whose log lags behind a membership change refuses the only candidates that can be elected, and the cluster stops for good

`requestVote` (and the pre-vote) refuse a candidate that is not a voter in the receiving server's
latest configuration. When the newest configuration's voters are a server that holds it and a
server whose log is behind it (whose own latest configuration still lists the first as a
non-voter), neither can be elected once the leader that appended it is gone: the lagging voter
refuses the up-to-date one, and the up-to-date one refuses the lagging one (its log is behind).
Seen in the hraft kit's crash deployment (`examples/dsverify/hraftrobust`'s `TestRobustCrash`,
2026-11-28, frequent crashes): the configuration at index 185 had voters {4, 1}, server 1's log
ended at 177 with voters {2}; no term advanced for nine minutes, over about 1400 restarts.

**Why not an issue:** liveness only (no safety property fails, and the kit's theorems are safety);
no deterministic test yet.

## Proof

no: liveness. It makes some of the crash deployment's runs stop making progress (the robust
harness's deadline), which the non-vacuity runs must count.
