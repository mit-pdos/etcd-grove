---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#11051 issue closed: same bug (Campaign returns nil after the prior keys go though its own key was deleted); closed by the stale bot, never fixed
  - etcd-io/etcd#11777 issue closed: same bug (own key deleted before waitDeletes, Campaign still returns nil); closed by the stale bot, never fixed
  - etcd-io/etcd#21165 pr open: Campaign resigns on any waitDeletes error; same lines, not this bug (textual conflict)
blocks-proof: no
---
# concurrency: Election.Campaign returns nil after its key was deleted while it waited

`Election.Campaign` (`client/v3/concurrency`) returns nil once every key created before its own is
gone, without checking that its own key still exists. If the key is deleted while it waits (its
session's lease is revoked or expires, or another `Election` on the same session and prefix
resigns), `Campaign` returns nil while another campaigner leads; `Leader()` names the other key and
`Proclaim` fails with `election: not leader`.

**Why not an issue:** not a guarantee etcd makes: `Campaign` returning nil never meant the caller
still leads (its session can expire right after it returns, which this is equivalent to), and the
guarantee callers must use, fencing on the key's create revision (`Proclaim`, `Leader()`), fails
correctly here; the user's decision of 2026-10-21, confirmed by the 2026-10-23 review ("Move to
non-issue").

## Proof

no: the proved spec of `Campaign` has the outcome `campaignLost` (nil with its key gone,
`Proof/go_etcd_io/etcd/client/v3/concurrency/Election__Campaign.lean`); election exclusion and
"only the leader proclaims" are proved on the fenced operations and hold.

## Notes

- `TestElectionCampaignKeyDeleted` in
  [`nonissues/election-campaign-key-check/election_campaign_test.go`](election-campaign-key-check/election_campaign_test.go)
  (revoke the waiting campaigner's lease, then resign the leader) fails at
  etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef, go1.27.3:
  `Error: An error is expected but got nil. Messages: e2 elected after its key was deleted`.
- A fix exists if this is revived: branch `fix/election-campaign-key-check` in
  `~/etcd-fixes/election-campaign-key-check` (upamanyus/etcd, pushed; 91d51234f test, a9699489e fix,
  off 22cc5d9ac): after `waitDeletes`, `Campaign` gets its key as `Mutex.Lock` does since b14c7cd44,
  returns `ErrElectionNotLeader` if it is gone, and waits again if it was recreated. It also keeps
  `TestElectionWithAuthEnabled`'s second campaigners' sessions alive (that test relied on the bug).
- Also noticed: `ResumeElection` uses `pfx` without appending `/` (unlike `NewElection`); after a
  failed `Proclaim`, `leaderKey` is `""` while `leaderSession` stays set.
