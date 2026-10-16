---
upstream: none
checked: 2026-10-16
links:
  - etcd-io/etcd#21138 pr closed: introduced `buildConfStateFromV3store` (commit 25a5bb287, in v3.7.0); the source of the hazard, not a report of it
  - etcd-io/etcd#20967 issue closed: zombie members in the members bucket after upgrading to 3.6 (related: the precondition of this hazard)
  - etcd-io/etcd#20995 pr merged: release-3.5 only (v3.5.26), cleans zombies from the v3 store; nothing on release-3.6 or main
  - etcd-io/etcd#13196 issue closed: earlier zombie members (related)
  - etcd-io/etcd#21867 pr open: removes stale members from the backend on --force-new-cluster (related, a different path)
---

# bootstrap: zombie members in the members bucket become raft voters at every restart

- **Status**: possible bug (unconfirmed). The mechanism is shown at the pin by a unit test; that a
  real upgrade reaches it, and its effect on a running cluster, are reasoned from the code, not
  reproduced.
- **Where** (etcd pin `107edf7e4`): `server/etcdserver/bootstrap.go:108-118` and `:132-149`. On
  every start with a WAL, `bootstrap` replaces the WAL snapshot's `ConfState` with
  `buildConfStateFromV3store(cfg.Logger, backend.be)`, which reads bbolt's `members` bucket
  (`schema.NewMembershipBackend(...).MustReadMembersFromBackend()`) and makes every member a voter
  unless `IsLearner`. That snapshot is what raft restarts from (`bootstrapRaft`). Introduced by
  etcd-io/etcd#21138 (`25a5bb287`, 2026-01-15), released in v3.7.0; not in 3.6.
- **What happens**: shown: with the members bucket holding members 1, 2, 3 and a zombie (a member
  under a new ID with member 1's peer URL, in neither `members_removed` nor raft's configuration, as
  in #20967), `buildConfStateFromV3store` returns voters `[1 2 3 beb11f483a7b51c5]`:
  `issues/etcd-bootstrap-confstate-zombie-voters/confstate_zombie_member_test.go` (dropped into
  `server/etcdserver/`; `go test ./etcdserver/ -run TestBuildConfStateFromV3storeZombieMember -v`
  from `server/`; passes at the pin, the zombie among the voters).
  Not shown:
  1. That a real upgrade reaches that state. #20967 shows zombies in the bucket of a member upgraded
     from 3.5.25 to 3.6.6 (3.5 used the v2 membership store, so they were invisible there; 3.6 reads
     the bucket and keeps them; #20995's cleanup is on release-3.5 only, v3.5.26). The next step,
     3.6 → 3.7 (or the pin), would then restart that member with the zombies as voters. Neither the
     3.5.25 → 3.6 → pin upgrade nor #20995's e2e data was run here.
  2. The cluster-level effect, reasoned from the code: the restarted member's raft configuration
     differs from the one the cluster committed. Zombies never vote or acknowledge: no member runs
     under their IDs, and a message to one goes to a real member's peer URL, whose stream handler
     rejects it (`X-Raft-To`, `rafthttp/http.go:437`) and whose raft answers, if at all, under its
     own ID. So that member needs a larger quorum: with 5 real members and 3 zombies, 5
     of 8, i.e. every real member. If every member has the same zombies (data from one restore),
     the whole cluster stops making progress after any single failure. If only some do, members
     disagree on the configuration at the same index. `etcdctl member remove <zombie>` should
     remove a zombie from both the bucket and raft's configuration, while all real members are up.
- **Expected**: a restart reproduces the raft configuration the log committed. Either the bucket
  equals the applied configuration (zombies cleaned on the way to 3.7, as #20995 does on 3.5), or
  bootstrap does not trust the bucket over the WAL snapshot's `ConfState` and the replayed conf
  changes.
- **How the proof handles it**: outside the verified results. `bootstrap` and
  `buildConfStateFromV3store` are translated names-only (`Code/go_etcd_io/etcd/server/v3/etcdserver.lean:420`),
  and none of etcd's restart paths is verified (`notes/STATUS.md`, raft v3.7 retarget stage R8a,
  D11). raft's `RestartNode.spec` (`Spec/go_etcd_io/raft/v3/RestartNode.lean:65-76`) covers only an
  empty log and ties the ghost configuration to the storage's conf state by premise
  (`γ.reCfg = GMap.listToSet csm.Voters'`, `:76`): a restart from a bucket that differs from the
  committed configuration violates that premise. Discharging it for etcd's restart is the
  bucket-equals-configuration invariant of the triage's proposal `membership-state-model`
  (`notes/bug-triage/etcd-20967.md`, "A residual hazard at the pin").
- **Possible fixes**: on `main`/3.7, clean the members bucket of members that are not in raft's
  configuration (as #20995 does from the v2 store on 3.5; on 3.7, against the WAL snapshot's
  `ConfState` plus the replayed conf changes); or document that clusters must pass through 3.5.26+
  (or clean zombies with `member remove`) before 3.7; or have `buildConfStateFromV3store` compare
  with the WAL snapshot's `ConfState` and refuse to start on a mismatch.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#20967 (`notes/bug-triage/etcd-20967.md`).
