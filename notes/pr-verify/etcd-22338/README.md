# Files of the etcd#22338 verification

Every test is a `.go` file named as it would be in etcd (`server/auth/`). To run one, copy it into a
checkout of the stated revision and run `go test` there:

```
cp server/auth/<file> <checkout>/server/auth/ && cd <checkout>/server/auth && \
  GOTOOLCHAIN=go1.27.1 go test -race -run '<Name>' -v .
```

| File | What it shows | Revision | Command |
|---|---|---|---|
| `server/auth/simple_token_gauge_test.go` | `TestSimpleTokenGaugeTracksCount`: the gauge follows the number of tokens through assign, `invalidateUser`, expiry and `disable`. `TestSimpleTokenGaugeSharedAcrossProviders`: with two providers in one process, the gauge alternates between their counts. `TestSimpleTokenWarnAtEveryCrossing`: the warning repeats each time the count comes back to 10000 (6 warnings after 5 delete/add cycles). All pass, under `-race`. | PR head `6b04e70c3` | `-run 'Gauge\|WarnAt'`; log `gauge-tests.log` |
| `server/auth/simple_token_review_test.go` (reviewer's) | `TestReviewWithRootCountsTokens`: 50 `WithRoot` calls (health checks, lease revokes) add 50 tokens. `TestReviewRecoverDisabledKeepsTokens`: the Recover finding, with the gauge. Both pass; they log rather than assert. | PR head `6b04e70c3` | `-run TestReview`; log `review-tests.log` |
| `server/auth/recover_disabled_tokens_test.go` | `TestRecoverAuthDisabledKeepsSimpleTokens`: after `Recover` from a backend with auth disabled and a later `AuthEnable`, a token issued before the disable is valid again (`issues/etcd-auth-recover-disabled-keeps-tokens.md`). It **fails** (shows the bug). | fork pin `09669450f` (same code on upstream `main` `b25719d10`) | `-run TestRecoverAuthDisabledKeepsSimpleTokens`; log `recover-disabled-tokens.log` |
