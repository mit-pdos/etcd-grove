# The `ETCD_VERIFY` family (sweep plan review's new target)

Reviewed 2026-11-07 by the `axiom` skill (sweep phase 1, Go first), on `lean` at `ad87892323`,
branch `axiom/etcd-verify`.

**Axioms.** All four in `Proof/go_etcd_io/etcd/server/v3/storage/backend/`, with their triples in
`Spec/go_etcd_io/etcd/server/v3/storage/backend/`:
- `backend.ValidateCalledInsideApply.wp_proof`;
- `backend.ValidateCalledOutSideApply.wp_proof`;
- `backend.ValidateCalledInsideUnittest.wp_proof`: for each of these three,
  `∀ lg, {{ isPkgInit backend }} f lg {{ RET #(); True }}`;
- `backend.VerifyBackendConsistency.wp_proof`:
  `∀ b lg skip bs, {{ isPkgInit backend }} … {{ RET #(); True }}`.

**Verdict: refuted on the Go side, all four. The Lean proof is not yet built** (phase 2).

The docstrings call this "a deployment assumption (`ETCD_VERIFY` unset)". But the triples have no
premise that states the assumption. No closed theorem shows it either (the audit row,
`notes/audit.md:272`, marks it "ok (assumption)").

## The Go code (pin `673da07c8fab`, `server/storage/backend/verify.go`)

- `ValidateCalledInsideApply` (`:31-38`): `if !verifyLockEnabled() { return }`. If
  `.applyEntries` is not in `debug.Stack()`, it calls `lg.Panic`.
- `ValidateCalledOutSideApply` (`:40-47`): the converse. If `.applyEntries` is on the stack, it
  calls `lg.Panic`.
- `ValidateCalledInsideUnittest` (`:49-56`): `lg.Fatal` unless the stack has `_test.go` and no
  `tests/`.
- `VerifyBackendConsistency` (`:72-95`): `verify.Verify` runs only under `ETCD_VERIFY` `assert` or
  `all`. It calls `b.BatchTx().LockOutsideApply()`, then compares the buckets and panics on a
  mismatch (`verify.verifier`).

The environment is read at every call, not at package init: `verify.IsVerificationEnabled` calls
`os.Getenv("ETCD_VERIFY")` (`client/pkg/verify/verify.go`). So a `t.Setenv` before the call works.

Which paths panic:
- **`lg.Panic`** panics with a real logger too. zap's Panic level runs `WriteThenPanic` even under
  `zap.NewNop()`. With a nil `lg` it is a nil dereference in `(*Logger).check`.
- **`lg.Fatal`** with a real logger is `os.Exit(1)`, which is not a counterexample. With a nil `lg`
  (the spec admits any `lg : Loc`), `(*Logger).check` dereferences nil and panics (`zap@v1.28.0
  logger.go:339`).
- **`VerifyBackendConsistency`** panics on a real mismatch. It also panics through `b`'s own
  methods: the spec takes any interface value `b`.

## The program

`examples/axiomcx/etcd-verify/etcdverify.go`:
- `InsideApply()` calls `backend.ValidateCalledInsideApply(nil)`; `InsideApplyNop()` does the same
  with `zap.NewNop()`.
- `OutSideApply()` calls `applyEntries(nil)`, a local function whose name puts `.applyEntries` on
  the stack, and which calls `ValidateCalledOutSideApply`. `OutSideApplyNop()` does the same with
  `zap.NewNop()`.
- `InsideUnittest()` calls `ValidateCalledInsideUnittest(nil)` on a goroutine started in a non-test
  file, then waits on a channel. The goroutine is needed because, called directly from a test, the
  stack has `_test.go`.
- `Consistency()` calls `backend.VerifyBackendConsistency(badBackend{}, nil, false)`, where
  `type badBackend struct{ backend.Backend }` has a nil embedded interface.

Test output (`go test ./axiomcx/etcd-verify/ -run . -count=1 -v`, go1.27.3):

```
=== RUN   TestUnset                       (ETCD_VERIFY="": all four return)
--- PASS: TestUnset (0.00s)
=== RUN   TestInsideApply                 (ETCD_VERIFY=all)
    etcd-verify_test.go:16: panicked: runtime error: invalid memory address or nil pointer dereference
    etcd-verify_test.go:16: panicked: Called outside of APPLY!
--- PASS: TestInsideApply (0.00s)
=== RUN   TestOutSideApply                (ETCD_VERIFY=lock)
    etcd-verify_test.go:16: panicked: runtime error: invalid memory address or nil pointer dereference
    etcd-verify_test.go:16: panicked: Called inside of APPLY!
--- PASS: TestOutSideApply (0.00s)
=== RUN   TestConsistency                 (ETCD_VERIFY=all)
    etcd-verify_test.go:16: panicked: runtime error: invalid memory address or nil pointer dereference
--- PASS: TestConsistency (0.00s)
=== RUN   TestInsideUnittest              (child process, ETCD_VERIFY=all)
    etcd-verify_test.go:56: child: err=exit status 2
        panic: runtime error: invalid memory address or nil pointer dereference
        go.uber.org/zap.(*Logger).check(0x0, 0x5, ...)   zap@v1.28.0/logger.go:339
        go.uber.org/zap.(*Logger).Fatal(...)             zap@v1.28.0/logger.go:295
        go.etcd.io/etcd/server/v3/storage/backend.ValidateCalledInsideUnittest(0x0)  verify.go:54
        .../axiomcx/etcd-verify.InsideUnittest.func1()   etcdverify.go:47
--- PASS: TestInsideUnittest (0.01s)
```

Every run is deterministic. The `TestX` wrappers recover the panic and pass. The panic itself is
the evidence.

## The Lean proofs (sketch; not yet built)

For each function F, `{{ isPkgInit pkg_id.etcdverify }} @! etcdverify.F #() {{ RET #(); True }}`.
- **The premise.** `isPkgInit backend` comes from the package's own `isPkgInit`, through its imports.
- **The environment** is not in the model. Nothing in the triple can exclude `ETCD_VERIFY`.
- **`InsideApply`, `OutSideApply`:** one `wp_apply` of the axiom at `lg := null`.
  `applyEntries` is an ordinary function call. These are the cleanest: no other axiom.
- **The `Nop` variants** add the `zap.NewNop` axiom (`notes/axiom-review/lease-ttl-*`). Prefer the
  nil forms.
- **`InsideUnittest`:** `wp_fork` of a thread that runs the axiom, plus Perennial's channel specs
  for `make`, `close` and receive. An alternative is to prove the goroutine body as a named function.
- **`Consistency`:** the axiom at `b := interface.ok badBackend{nil}`. Risk: Goose's translation of
  a struct that embeds an interface (the promoted methods are not called by the proof; the value is
  only converted to `Backend`). If Goose does not support it, use another non-nil `Backend` value.

## What rests on them

- `batchTx.Lock`, `LockInsideApply` and `LockOutsideApply` (`batch_tx.go:103,119,125`).
- `EtcdServer.applyAll` (`server.go:987`), `ApplyAllSnap(On)` and the corruption monitor
  (`:2294`).
- The plan review's reach: 17 of 23 closed theorems each for `OutSideApply` and
  `VerifyBackendConsistency`.
- No etcd bug: `applyAll` calls `VerifyBackendConsistency` after `applyEntries` returns, so the
  stack check passes in etcd's own use.

## Proposed restatement (not applied)

1. Add a persistent startup fact `envVerifyOff`, meaning `ETCD_VERIFY` is unset, or neither
   `lock`/`assert`/`all` (case-insensitive). The adequacy theorems take it as a premise, as they
   take `walDirsAbsent`, so the assumption appears in the closed statements.
2. Each of the four specs requires `envVerifyOff`.
3. Perennial has no `os.Setenv` spec, so the program cannot change the environment in the model. A
   future `os.Setenv`/`Unsetenv` spec must consume or exclude the fact. Otherwise the restatement
   becomes false again.
4. The alternative keeps the checks on: specs that panic-free-ly require "called inside or outside
   apply" and a non-nil `lg`. That needs a model of the call stack, so it is not practical.

Not done in phase 1: the audit row (`notes/audit.md:272`) and the index row in `README.md`.
