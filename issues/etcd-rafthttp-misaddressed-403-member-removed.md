---
upstream: none
checked: 2026-10-20
links:
  - etcd-io/etcd#17078 pr merged: introduced the `403` "cannot process message to mismatch member" in Process (2023, backported to 3.5 and 3.4) that the sender reads as errMemberRemoved; the review did not discuss the sender's reaction
  - etcd-io/etcd#20356 issue closed: related (mismatch-member rejections in a 3.5.11 cluster that became unavailable; maintainer suspected members of different clusters); no member reported stopping as removed; converted to a discussion without a root cause
---

# rafthttp: a message delivered to the wrong member makes the healthy sender stop as "removed"

- **Status**: a wrong result (a healthy member shuts itself down) under a misaddressed peer URL;
  found while scoping the multi-member generalization (D21, `notes/decisions.md`). Medium
  confidence on reachability, high on the code path. Not reproduced by a test yet.
- **Where** (etcd fork at the pin `8a24be2a3`, `etc/goose.py`):
  - `server/etcdserver/server.go:699-721` `EtcdServer.Process`: a message whose `To` is not the
    local member is rejected with `httptypes.NewHTTPError(http.StatusForbidden, "cannot process
    message to mismatch member")` -- the same status as a message from a removed member
    (`server.go:701-708`).
  - `server/etcdserver/api/rafthttp/http.go:102-169` `pipelineHandler.ServeHTTP`: checks the
    cluster id (`checkClusterCompatibilityFromHeader`) but not the `X-Raft-To` header (the stream
    handler does, `http.go:437`), then writes `Process`'s HTTP error back.
  - `server/etcdserver/api/rafthttp/util.go` `checkPostResponse`: every `403` becomes
    `errMemberRemoved`; `pipeline.go:165-171` and `snapshot_sender.go:110-114` then
    `reportCriticalError(err, errorc)`.
  - `server/etcdserver/server.go:844-847` `run`: on `errorc` it logs "data-dir used by this member
    must be removed" and returns, stopping the server.
- **What happens**: if member A's pipeline (or snapshot sender) for peer B posts to a URL that is
  served by another member C of the same cluster (a stale peer URL after `UpdateMember`, a member
  re-created on a reused address, a misconfigured `--initial-cluster`), C's `Process` answers
  `403` because `m.To = B ≠ C`. A reads that as "I was removed from the cluster" and stops, although
  nobody removed it. The `403` for a misaddressed message is indistinguishable from the `403` for
  a removed sender.
- **Expected**: only a peer that knows the sender was removed should make it stop; a misaddressed
  message should get a status the sender does not treat as fatal (e.g. the `412`/`X-Raft-To`
  check the stream handler uses), or `checkPostResponse` should tell the two `403` bodies apart.
- **For the proofs**: the server's named premise `transportEffectsOk` reads "no well-behaved member
  reports `errMemberRemoved` of a member never removed" (D19m); with several members this needs the
  peer URLs to address the members they name (a deployment premise), or the fix above.
