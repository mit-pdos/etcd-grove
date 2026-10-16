# election-campaign-key-check

- **Finding**: `issues/election-campaign-key-check.md`
- **Target**: etcd-io/etcd, `main` (`client/v3/concurrency`)
- **Branch**: `election-campaign-key-check` in `~/etcd-fixes/election-campaign-key-check` (commit
  fd83e72569415d691445ab88ac9c86fdbe93cf89), not pushed. `origin` (upamanyus/etcd) already has an older
  `election-campaign-key-check` (bb50d33b8, off f061acd09: a loop that re-waits on a recreated key, returning
  `ErrElectionNotLeader`, and a 313-line test file), which this branch replaces, so the push is
  `git -C ~/etcd-fixes/election-campaign-key-check push --force-with-lease=election-campaign-key-check:bb50d33b8ce7a31961be5b498f0e6e1e375338f5 origin election-campaign-key-check`.
  `issue.md` links the test at `https://github.com/upamanyus/etcd/blob/election-campaign-key-check/...`, which shows
  this branch's test only after that push.
- **Base**: upstream `main` b25719d10cdc41fb707b0d9f819c2529dec5d590 (2026-10-16); `Election.Campaign` unchanged
  in substance since f061acd09, where the finding was made
- **State**: draft
- **Upstream issue**: —
- **PR**: —

Independent of the sibling candidate `mutex-lock-recreated` (same fix for `Mutex.Lock`); both branch off the same
base and touch different files.

## Security

Not a security report: the bug is in the client library's election recipe. It needs the waiting campaigner's own
lease to be revoked or to expire (or a sibling `Election` on the same session to resign); it does not crash or hang
a member, lose acknowledged data, or bypass auth. Its impact is on the application's mutual exclusion (two
`Campaign` calls returning nil at once).

## Duplicates checked (2026-10-16)

Searches (2 of 3 allowed): `Campaign election` (PRs), `Campaign deleted key`; plus direct reads of #11051, #11777,
#12334 and PR #21165's diff.

- #11051 (issue, closed by the stale bot 2020-04-28, labels `type/question`, `stale`): same bug (Campaign returns
  nil after waiting although its own key was deleted). Never fixed.
- #11777 (issue, closed by the stale bot 2020-07-31): same bug (own key deleted, Campaign still returns nil). Never
  fixed.
- Alternative for the user: reopen (or comment on) #11051 or #11777 instead of filing a new issue; the issue text
  says in one sentence that both were closed as stale.
- #21165 (PR, open, for #21128): `Campaign` resigns on any `waitDeletes` error. Same lines, not this bug; the two
  PRs will conflict textually in the `if err != nil` block (trivial to rebase).
- #22124 (PR, open): `Resign` keeps leadership state on failure; #22560 (PR, open): auth token renewal in
  concurrency calls; #12334 (issue, closed): a question about lease expiry while campaigning; #17623 (issue,
  open): token expiry while campaigning. None fixes this bug.
- No open PR fixes it; `Campaign` at the base has no check of its key after `waitDeletes`.

## Verification

`TestElectionCampaignKeyDeleted` (`tests/integration/clientv3/concurrency/election_test.go`) is the issue's example
(two sessions; `e2` waits behind `e1`; `s2`'s lease is revoked; `e1` resigns). At the base (fix reverted):
`cd tests && go test ./integration/clientv3/concurrency/ -run TestElectionCampaignKeyDeleted -count=1` fails at
line 137, "Expected error with "mutex: session is expired" in chain but got nil".

With the fix, all pass:

- `cd tests && go test ./integration/clientv3/concurrency/ -run TestElectionCampaignKeyDeleted -count=5`, and
  `-race -count=20`
- `cd tests && go test -race ./integration/clientv3/concurrency/ -count=1` (the package)
- `cd client/v3 && go test ./concurrency/ -count=1`
- `cd tests && go test ./integration/ -run 'TestElection|TestV3Election' -count=1` (all of `v3_election_test.go`
  and the v3election gRPC service's tests), and `-run 'TestV3Election|TestElectionWithAuthEnabled' -count=3`
- `go vet` of `client/v3/concurrency`, `tests/integration/clientv3/concurrency`, `tests/integration`; `gofmt -l` of
  the changed files: clean

`TestElectionWithAuthEnabled` fails with the fix and the test unchanged ("[Campaign] client1 first campaign: mutex:
session is expired"): every session is orphaned with TTL 10, so the waiting campaigner's key expires with the
leader's and its `Campaign` returned nil only because of this bug. The branch orphans only the first campaign of
each user and closes the other sessions when their `Campaign` returns (taken from the old draft); the changed test
also passes at the base.

Other runs at the base (scratch tests, not committed):

- The issue's output, each call logged. With the fix the same run gives `e2.Campaign: mutex: session is expired`.
- The two-leader claim in "Anything else": with `e3` on a third session campaigning after the revoke and before
  `e1.Resign`, at the base `e3.Campaign: <nil>`, `e2.Campaign: <nil>`, and `e2.Leader()` returns `e3`'s value.

Not run: the shared-session schedule (a sibling `Election` on the same session and prefix resigning; the old draft's
test reproduced it at f061acd09), the recreated-key case the `CreateRevision` comparison covers (no test on the
branch), the v3election gRPC service variant, `tests/e2e` (`v3_curl_election_test.go`), `make verify`,
`golangci-lint`.

## If a reviewer asks

- Why `ErrSessionExpired`, whose message is "mutex: session is expired": it is what `Mutex.Lock` returns when its
  key is gone after the same wait, and what the sibling `Mutex.Lock` PR returns for a recreated key; the session's
  lease being gone is the usual cause. Alternatives: `ErrElectionNotLeader` (what `Proclaim` returns when the leader
  key is gone; the old draft used it), or a new error, at the cost of a new exported name. Easy to switch.
- Why compare the create revision, not only existence: a sibling `Election` on the same session and prefix can
  delete the shared key (`Resign`, a canceled `Campaign`) and create it again with a later revision, after another
  session's key; finding a key then does not mean this campaign is first. Matches the sibling `Mutex.Lock` fix.
- Why an error and not keep waiting (the old draft looped, adopting a recreated key's revision): the smaller change,
  and the same behavior as `Mutex.Lock`; a recreated key belongs to the sibling `Election` that recreated it.
- Cleanup on the new error: it goes through the existing `waitDeletes` error path (`leaderSession = nil`, or
  `Resign` if the context is done; `Resign`'s compare on the create revision does not touch a recreated key).
- `e.hdr` stays the header of the campaign's transaction, as before; `Mutex.Lock` uses its `Get`'s header instead.
- Cost: one more `Get` per successful `Campaign`.
- Backports: `release-3.6` and `release-3.5` have the same code after `waitDeletes` (read, not run; in
  `release-3.5` `waitDeletes` also returns a header).

## check.py (2026-10-16)

No FAIL. WARNs kept: the fix's comment says why the `Get` is there (the key can go during the wait), which the code
does not; the issue names `Campaign`, the API the user calls.
