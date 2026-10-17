# Files of the etcd-io/etcd#21714 verification

Every test is a `_test.go` file of package `clientv3` (`client/v3`). To run one:
`cp <file> <checkout>/client/v3/ && cd <checkout>/client/v3 && go test -run <Name> -v .`
(`GOTOOLCHAIN=go1.27.1`). "base" is upstream `5ef5d3c26` (the PR's merge base), "head" the PR head
`73e843991`; the fork branch `pr-etcd-21714-goose-lean` (mit-pdos/etcd-grove) behaves as head.

| File | What it shows | Revision | Command |
|---|---|---|---|
| `client_error_wrap_test.go` | what a caller of `New` sees of the dial error, the token error (wrong password, unreachable endpoint with credentials) and `ErrMutuallyExclusiveCfg`: message, `errors.Is`/`As`, `==`, type assertion, `status.Code`, `rpctypes.ErrorDesc`; that an unreachable endpoint without credentials gives no `New` error at all | base and head (`PR21714_HEAD=1` at head selects the head's assertions) | `go test -run TestPR21714 -v .` |
| `probe-base.log`, `probe-head.log` | its output at base and head (passes at both) | | |
| `client_new_cancel_leak_test.go` | `issues/etcd-client-new-context-leak.md`: the size-check and logger-error returns of `newClient` leave the context registered with its parent (100 of 100) | base and head (fails at both) | `go test -run CancelsContext -v .` |
| `leak-base.log`, `leak-head.log` | its output | | |
| `review_postulates_test.go`, `.log` | the reviewer's: the first versions of the names-only postulates (dial, `SetEndpoints`, `resolver.Close`, `Close`, `autoSync`, `checkVersion`) promised no panic for clients with nil fields; all 8 cases panic. Fixed: `clientFixed` and the postulates now require non-nil mutex/resolver, a context of the model and its cancel function, non-empty endpoints | head | `go test -run TestReviewPostulatesPanic -v .` |
| `review_dialopts_race_test.go`, `.log` | the reviewer's: a caller writing `Config.DialOptions` while `New` runs races with the dial (`-race`). Fixed: `New`/`newClient` now require the dial options read-only | head | `go test -race -run TestReviewNewDialOptionsRace -v .` |
| `review_errorf_test.go`, `.log` | the reviewer's: `fmt.Errorf`'s `%w` calls the operand's `Format` if it has one (the `ErrorfWrap` axiom now states the no-`Formatter` assumption, as `Spec/fmt/Errorf.lean` does); the result is a `*fmt.wrapError` whose `Unwrap` returns the operand | head | `go test -run TestReviewErrorfWrapCallsFormat -v .` |
| `review_dial_race_test.go`, `.log` | the reviewer's: `issues/etcd-client-dial-endpoints-race.md`, `Client.Dial` reads `c.endpoints[0]` without `epMu` while `SetEndpoints` writes it (`-race`) | head (the code is the same at the pin) | `go test -race -run TestReviewDialSetEndpointsRace -v .` |
