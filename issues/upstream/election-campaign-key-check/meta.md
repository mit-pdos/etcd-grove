# election-campaign-key-check

- **Finding**: `issues/election-campaign-key-check.md`
- **Target**: etcd-io/etcd, `main` (`client/v3/concurrency`)
- **Branch**: `fix/election-campaign-key-check` in `~/etcd-fixes/election-campaign-key-check`, rebuilt 2026-10-18 on the
  base below as two commits: 91d51234f (`client/v3: test Election.Campaign whose key is deleted while it waits`, the
  tests, which fail there) and a9699489e (`client/v3: fail Election.Campaign when its key was deleted while waiting`,
  the fix). Not pushed: the fork's `upamanyus/etcd:fix/election-campaign-key-check` still has the old single commit
  fd83e7256 (off b25719d10) until the user approves the force-push
  `git -C ~/etcd-fixes/election-campaign-key-check push --force-with-lease=fix/election-campaign-key-check:fd83e7256 origin fix/election-campaign-key-check`.
  The issue's link (lines 107-139 of `tests/integration/clientv3/concurrency/election_test.go`, the test's doc
  comment to its closing brace) holds only after that push; check it on GitHub then. The fork's older draft branch
  `election-campaign-key-check` (bb50d33b8) is left as it was.
- **Base**: upstream `main` 22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4 (2026-10-18); `client/v3/concurrency` and the
  changed tests are the same as at b25719d10, the previous base, and `Election.Campaign` is unchanged in substance
  since f061acd09, where the finding was made
- **State**: draft (revised 2026-10-18 to the skill's current standard)
- **Upstream issue**: —
- **PR**: —

Independent of the sibling candidate `mutex-lock-recreated` (the corresponding fix for `Mutex.Lock`); both branch off
`main` and touch different files.

## Security

Not a security report: the bug is in the client library's election recipe. It needs the waiting campaigner's own
lease to be revoked or to expire (or a sibling `Election` on the same session to resign); it does not crash or hang
a member, lose acknowledged data, or bypass auth. Its impact is on the application's mutual exclusion (two
`Campaign` calls returning nil at once).

## Duplicates checked (2026-10-16)

Searches (2 of 3 allowed then): `Campaign election` (PRs), `Campaign deleted key`; plus direct reads of #11051,
#11777, #12334 and PR #21165's diff.

- #11051 (issue, closed by the stale bot 2020-04-28, labels `type/question`, `stale`): same bug (Campaign returns
  nil after waiting although its own key was deleted). Never fixed.
- #11777 (issue, closed by the stale bot 2020-07-31): same bug (own key deleted, Campaign still returns nil). Never
  fixed.
- For the user: reopen (or comment on) #11051 or #11777 instead of filing a new issue. The issue text no longer
  mentions them (the skill keeps other issues out of the issue); if filing a new issue, a comment linking them after
  filing, or a "Related: #11051, #11777" line in the PR, are the options.
- #21165 (PR, open, for #21128): `Campaign` resigns on any `waitDeletes` error. Same lines, not this bug; the two
  PRs will conflict textually in the `if err != nil` block (trivial to rebase).
- #22124 (PR, open): `Resign` keeps leadership state on failure; #22560 (PR, open): auth token renewal in
  concurrency calls; #12334 (issue, closed): a question about lease expiry while campaigning; #17623 (issue,
  open): token expiry while campaigning. None fixes this bug.
- No open PR fixes it; `Campaign` at the base has no check of its key after `waitDeletes`.

## Why the fix works, and why the test shows the bug

At the base, `Campaign` creates `keyPrefix/<lease>` with the session's lease (its create revision is `leaderRev`),
then `waitDeletes` loops: get the newest key under the prefix created before `leaderRev`, watch it until deleted,
repeat; when none is left it returns nil, and so does `Campaign`. `waitDeletes` never looks at the campaign's own
key, so a key deleted during the wait (lease revoked or expired, a sibling `Election` on the same session and prefix
resigning) goes unnoticed. The fix gets the key after the wait; if it is gone, or was recreated (a different create
revision, so keys of other sessions created between the two revisions were never waited for), `Campaign` returns
`ErrSessionExpired` through the existing cleanup path.

The test (`TestElectionCampaignKeyDeleted`, next to `TestResumeElection`, through the package's lazy integration
cluster) uses the API as documented: two sessions, `e1` leads, `e2` campaigns and waits (the setup check waits only
until `e2`'s key exists, so that the revocation happens during the wait), `s2`'s lease is revoked from the client
(standing in for a lease that expires: the session's keepalive cannot prevent either), and `e1` resigns. It asserts
only the guarantee: `e2.Campaign` returns an error (not which one).

`TestElectionWithAuthEnabled` (in `tests/integration/v3_election_test.go`) relied on the bug: it orphans every
session (TTL 10), so each user's second campaign, which waits for the first campaign's lease to expire, loses its own
key at about the same time (its lease was granted milliseconds later) and was elected anyway. With the fix and that
test unchanged, it failed 3 runs of 3 (`[Campaign] client1 first campaign: mutex: session is expired`, or `client1
second campaign`: the two campaigns of a user race to be first). The tests commit orphans only the first campaign listed
for each user (`orphan: true`) and closes the other sessions when their `Campaign` returns, which deletes their keys;
whichever of a user's two campaigns is elected first, the other then finds its own key alive. That change goes in the tests commit, not the fix: the changed test passes on `main` (run
below) and with the fix, so the tests commit holds every test change, fails only in the new test, and the fix
commit changes only `election.go`. Either placement keeps "the tests commit fails, the fix commit passes" true; this
one also shows that the changed test is valid on `main`, i.e. that it does not depend on the fix.

## Verification (go1.27.2 linux/amd64)

- At the tests commit 91d51234f: `cd tests && go test ./integration/clientv3/concurrency/ -run
  'TestElectionCampaignKeyDeleted$' -count=1` fails at line 138, `An error is expected but got nil.` (`e2 elected
  after its key was deleted`), the output in `issue.md`. `go test ./integration/ -run 'TestElectionWithAuthEnabled$'
  -count=1` (the changed test) passes.
- At the fix commit a9699489e, all pass:
  - `cd tests && go test ./integration/clientv3/concurrency/ -run 'TestElectionCampaignKeyDeleted$' -count=5`, and
    `-race -count=20`;
  - `cd tests && go test -race ./integration/clientv3/concurrency/ -count=1` (the package);
  - `cd tests && go test ./integration/ -run 'TestElectionWithAuthEnabled$|TestElection|TestV3Election' -count=1`
    (all of `v3_election_test.go` and the v3election gRPC service's tests);
  - `cd client/v3 && go test ./concurrency/ -count=1`;
  - `go vet` of `client/v3/concurrency`, `tests/integration/clientv3/concurrency`, `tests/integration`; `gofmt -l`
    of the changed directories: clean.
- The fix with `TestElectionWithAuthEnabled` as on `main` (`go test -overlay`): fails, 3 runs of 3 (above).
- Scratch test (not committed; `go test -overlay` adding it, and at the base also `election.go` from `main`), each
  call logged; the issue's step 4 and "Anything else" come from it:
  - at the base: `e2.Campaign: <nil>`, `e2.Proclaim: election: not leader`, `e2.Leader: election: no leader`; with
    `e3` on a third session campaigning after the revocation and before `e1.Resign`: `e3.Campaign: <nil>`,
    `e2.Campaign: <nil>`, `e2.Leader` returns `"e3"`;
  - with the fix: `e2.Campaign: mutex: session is expired` in both runs.

Not run: the shared-session schedule (a sibling `Election` on the same session and prefix resigning; the old draft's
test reproduced it at f061acd09), the recreated-key case the create-revision comparison covers (no test on the
branch), the v3election gRPC service and grpc-proxy variants, `etcdctl elect`, `tests/e2e`
(`v3_curl_election_test.go`), `make verify`, `golangci-lint`. Lease expiry (rather than revocation) is shown at the
base only through `TestElectionWithAuthEnabled` (above).

## If a reviewer asks

- Why `ErrSessionExpired`, whose message is "mutex: session is expired": it is what `Mutex.Lock` returns when its
  key is gone after the same wait, and what the sibling `Mutex.Lock` PR returns for a recreated key; the session's
  lease being gone is the usual cause. The message reaches users of the v3election gRPC service and `etcdctl elect`
  as is. Alternatives: `ErrElectionNotLeader` ("election: not leader", what `Proclaim` returns when the leader key is
  gone; the finding and the old draft used it), or a new error, at the cost of a new exported name. Easy to switch;
  the test asserts only that an error is returned.
- Why compare the create revision, not only existence: a sibling `Election` on the same session and prefix can
  delete the shared key (`Resign`, a canceled `Campaign`) and create it again with a later revision, after another
  session's key; finding a key then does not mean this campaign is first. Matches the sibling `Mutex.Lock` fix.
- Why an error and not keep waiting (the finding proposed looping, adopting a recreated key's revision): the smaller
  change, and the same behavior as `Mutex.Lock`; a recreated key belongs to the sibling `Election` that recreated it.
- Why not the shape of `Mutex.Lock` (a separate `Get` and error handling after the wait): the `Get` and its error go
  through the existing cleanup (`leaderSession = nil`, or `Resign` if the context is done; `Resign`'s compare on the
  create revision does not touch a recreated key), instead of duplicating it.
- After the new error with a live context, `Key()` and `Rev()` still return the lost key, as after a `waitDeletes`
  error at the base; `Proclaim` and `Resign` return `ErrElectionNotLeader`/nil since `leaderSession` is nil. Not
  changed.
- `e.hdr` stays the header of the campaign's transaction, as before; `Mutex.Lock` uses its `Get`'s header instead
  (the revision at which the key was confirmed). Easy to switch if a reviewer prefers it.
- `Campaign`'s doc comment is not changed: it does not say that `Campaign` returns nil only as leader, nor list its
  errors.
- Cost: one more `Get` per successful `Campaign`.
- Backports: `release-3.6` and `release-3.5` have the same code after `waitDeletes` (read, not run; in
  `release-3.5` `waitDeletes` also returns a header).

## check.py (2026-10-18)

No FAIL. WARNs kept: the fix's comment says why the `Get` is there (the key can go during the wait), which the code
does not; the issue names `Campaign`, the API the user calls; the PR has 117 words (the approved raft example
has about as many), the extra sentence explaining the change to `TestElectionWithAuthEnabled`, which a reviewer
needs.
