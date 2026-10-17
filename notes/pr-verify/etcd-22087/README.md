# etcd-io/etcd#22087: files the report relies on

The report is `notes/pr-verify/etcd-22087.md`. Revisions:

- the PR head: etcd-io/etcd 41ee0c1e249826fa58896281de6af5256e8d6962 (upstream base
  12caed621b38312cc1084113415bf135c59e6457);
- the fork pin 09669450f (`etc/goose.py`'s etcd pin);
- the verified fork code, PR alone: `mit-pdos/etcd-grove` branch `pr-etcd-22087-goose-lean`, commit
  2428ff1f6 (the pin plus the PR, with the PR's test file);
- the fork code with etcd-io/etcd#22291 on top: `mit-pdos/etcd-grove` branch
  `pr-etcd-22087-with-22291-goose-lean`, commit dc69a2d15 (2428ff1f6 plus #22291's head 71d57990b,
  with its test file).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `lease_requireleader_pairing_internal_test.go` | (copied verbatim from `pr-verify/etcd-22291`) etcd#22081: after one leader loss, a plain subscriber's channel is paired with the require-leader subscriber's context, and a second leader loss closes it. Fails on the pin and the upstream base; passes on the PR head, on the PR alone and on the PR with #22291. | all five revisions above | `cp lease_requireleader_pairing_internal_test.go <checkout>/client/v3/ && cd <checkout>/client/v3 && go test -count=1 -run TestLessorCloseRequireLeader -v .` |
| `lease_requireleader_internal_test.go` | (#22291's own test, from its head 71d57990b) etcd#22094: an entry all of whose subscriptions required a leader must leave `l.keepAlives`. Fails on the pin, the upstream base, the PR head and the PR alone (so #22087 does not fix the orphan); passes with #22291 on top. | all five | as above (on the combined branch the file is already there) |
| `tests.log` | the output of both tests (and of the PR's own `TestLessorCloseRequireLeaderKeepsSurvivorsPairedWithOwnContext`, present on the last three revisions) on the five revisions | | the loop above, `GOTOOLCHAIN=go1.27.1` |
| `lease_requireleader_ctxcloser_review_internal_test.go` (the reviewer's) | `TestReviewCtxCloserAfterCloseRequireLeader`: after a leader loss, cancelling the require-leader subscriber's context closes the plain subscriber's channel (fails at the upstream base 12caed621, passes at the PR head, the PR alone and the PR with #22291). `TestReviewOrphanReapedOnlyByCtxCloser`: an emptied entry is removed only when a former subscriber's cancelable context ends (`keepAliveCtxCloser`'s `len(ka.chs) == 0`), and stays otherwise (fails on all but the PR with #22291). | 12caed621, 41ee0c1e2, 2428ff1f6, dc69a2d15 (the PR's test file copied in at the base) | `cp lease_requireleader_ctxcloser_review_internal_test.go <checkout>/client/v3/ && cd <checkout>/client/v3 && go test -count=1 -v -run 'TestLessorCloseRequireLeaderKeepsSurvivorsPairedWithOwnContext\|TestReview' .` |
| `review-tests.log` | that file's output on the four revisions | | as above |
| `with-22291/` | the spec, proof and invariant of `closeRequireLeader` proved of the code of #22087 with #22291 on top (this branch's commit dc2bb0753, where they are the files `Spec/go_etcd_io/etcd/client/v3/lessor__closeRequireLeader.lean`, `Proof/.../lessor__closeRequireLeader.lean`, `Proof/.../InvLease.lean` and build with that commit's translation). Kept here because the branch's tip translates #22087 alone; not built at the tip. | | `git checkout dc2bb0753 && lake build Proof.go_etcd_io.etcd.client.v3.Results` |
