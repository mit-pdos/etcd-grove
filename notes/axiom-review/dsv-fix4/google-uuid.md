# Axiom review: `google/uuid`'s `New` and `UUID.ID` (`New.wp_proof`, `UUID.ID.wp_proof`)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` (branch `dsv-fix4`, head `5c6274f9e0` plus the uncommitted files that
add these axioms); Perennial `fce59af75` (`lake-manifest.json`); Go `github.com/google/uuid` v1.3.1
(`~/go/pkg/mod/github.com/google/uuid@v1.3.1`) at the pinned toolchain go1.27.3
(`src/crypto/rand/rand.go`, `src/crypto/internal/rand/rand.go`, `src/crypto/internal/sysrand/rand.go`).

## The axioms

Both replace a former premise of swiftpaxos's statement (`SwiftOsRandom`, and `SwiftHyps.uuid_ID`,
`Dsverify/Proof/github_com/imdea_software/swiftpaxos/Hyps.lean`). They discharge those classes in
`Dsverify/Proof/github_com/imdea_software/swiftpaxos/HypsHoldLinked.lean`
(`swiftOsRandom_holds`, `swiftHyps_holds`). The specs are in
`Dsverify/Proof/github_com/imdea_software/swiftpaxos/lib/LibSpecs.lean:53-63`:

    -- Dsverify/Proof/github_com/google/uuid/New.lean
    axiom github_com.google.uuid.New.wp_proof : github_com.google.uuid.New.spec
    New.spec := {{ isPkgInit pkg_id.github_com.google.uuid }}
                  @! uuid.New #()
                {{ (u : UUID), RET #u; True }}

    -- Dsverify/Proof/github_com/google/uuid/UUID__ID.lean
    axiom github_com.google.uuid.UUID.ID.wp_proof [uuid.Assumptions] : UUID.ID.spec
    UUID.ID.spec := ∀ u : UUID, {{ True }} u.ID() {{ (x : w32), RET #x; True }}

`UUID` is `GoArray w8 16` (`Dsverify/Code/github_com/google/uuid.lean:330`). The package is translated
names and types only (`Dsverify/Code/github_com/google/uuid.toml`: `translate = ["!*"]`), so both
calls go through the context's opaque function table. `isPkgInit uuid` is `True`, written by hand
(`Dsverify/Proof/github_com/google/uuid/Init.lean`; its own init axiom was reviewed in
`notes/axiom-review/dsv-inits/github-com-google-uuid.md`).

The claims, in plain words:
1. `uuid.New()` returns, without panicking, in **every** state once the package is initialized. The
   precondition carries nothing about the package's state (`rander`, `poolEnabled`).
2. `u.ID()` returns some `uint32` for every 16-byte value `u`.
3. Nothing else: no claim about the bytes (version, variant, randomness, uniqueness), and no state or
   resource is consumed or produced.

`(UUID).Time` has no spec and no axiom.

## Users

- `examples/dsverify/swiftpaxos/client/client.go:56`, `ClientId: int32(uuid.New().ID())`. Proved in
  `Dsverify/Proof/github_com/imdea_software/swiftpaxos/client/NewClientLog.lean:37-38`
  (`wp_apply wp_New`, `wp_apply wp_ID`, both results discarded as arbitrary).
- `examples/dsverify/swiftpaxos/client/buffer.go:206`, `uuid.New().Time()` in `genGetKey`. It is called
  only from `BufferClient.Loop` (`buffer.go:103`), which no proof reaches (`grep genGetKey Dsverify/Proof`:
  nothing). Out of scope. `Time` cannot panic either way (`time.go:112-117`: fixed slices of a `[16]byte`).

## The Go code

- `New` is `Must(NewRandom())` (`version4.go:13-15`). `Must` panics on a non-nil error (`uuid.go:178`).
- `NewRandom` (`version4.go:39-44`) calls `NewRandomFromReader(rander)` when the pool is off. With the
  pool on, it calls `newRandomFromPool`, which does `io.ReadFull(rander, pool[:])` under `poolMu`. Either
  way, an error from `rander` becomes a panic in `New`.
- `rander` is a package variable initialized to `crypto/rand.Reader` **at uuid's init** (`uuid.go:40`).
  `SetRand(r)` overwrites it (`uuid.go:262-268`; `nil` restores `rand.Reader`). The documentation says:
  "If r.Read returns an error ... a panic will be issued."
- go1.27.3: `crypto/rand.Reader` is `crypto/internal/rand.Reader = reader{}`. Its `Read`
  (`crypto/internal/rand/rand.go:22-30`) calls `drbg.Read`, which calls `sysrand.Read` (getrandom(2)).
  On an error, `sysrand.Read` calls `runtime.fatal` (`sysrand/rand.go:44-52`): the process ends, and
  `Read` never returns an error. **Exception:** under `GOEXPERIMENT=boringcrypto`, `reader.Read` calls
  `panic("crypto/rand: boring RandReader failed: ...")` when BoringSSL's RNG fails (`rand.go:23-26`). That
  is an ordinary panic, which propagates out of `uuid.New`.
- `ID` is `binary.BigEndian.Uint32(uuid[0:4])` on a `[16]byte` value (`dce.go`). It has no failure path.

## Verdict

- **`UUID.ID.wp_proof`: survives**, with no conditions beyond the generic context condition (attack 9).
- **`New.wp_proof`: survives with conditions.** No counterexample can be built in the current tree.
  However, the triple is not true of the library in every Go program. Its precondition is `True`, yet Go's
  `New` panics in a state that a legal Go program reaches through the package's public API
  (`SetRand(failingReader)`). The axiom is sound only because no spec of `SetRand` exists, and none can
  be added beside it. The conditions are listed below.

## Attacks tried

1. **`SetRand` to a failing reader** (missing premise). Go: `uuid.SetRand(failReader{}); uuid.New()`
   panics with `boom` (test below, `TestSetRandPanics`). The same happens with `EnableRandPool()`
   (`TestPoolSetRandPanics`). Lean: blocked only because `SetRand` has no body and no spec in the
   translation, so a program that calls it has no provable WP. This is not a property of `New.spec`.
   Any spec of `SetRand`, even the true `{{ True }} uuid.SetRand r {{ RET #(); True }}`, combined with
   `New.wp_proof` gives a no-panic proof of a program that panics. **Condition N1:** no part of the
   deployed program calls `uuid.SetRand` with a reader that can fail. Swiftpaxos does not call
   `SetRand` (`grep -rn SetRand examples/dsverify/swiftpaxos`: nothing). **Rule for the tree:** never
   add a spec of `SetRand` while this axiom stands.
2. **Racing `SetRand` against `New`.** A torn interface read of `rander` could crash the program. This
   attack needs `SetRand`, so it falls under N1.
3. **`EnableRandPool`/`DisableRandPool`** (also unspecified). With the default reader the pool path
   cannot fail: `poolPos` stays a multiple of 16 that is at most `randPoolSize = 256`, it is checked
   against 256 before the copy, and it is changed only under `poolMu`. `DisableRandPool` resets it under
   the lock. A data race on `poolEnabled` only picks one of two paths, and neither panics. This does not
   weaken the axiom.
4. **Replacing `crypto/rand.Reader` before uuid's initialization.** `rander` captures the value at init,
   so a package initialized before `github.com/google/uuid` that assigns `rand.Reader = bad` would make
   `New` panic. Lean: blocked, because Perennial's `crypto/rand` init fact gives
   `globalAddr Reader ↦□ rdr` (persistent: `Perennial/Proof/crypto/rand/Base.lean:32`), so no proof can
   store to it. Assigning it after uuid's init has no effect on `rander`. **Condition N2:** the program
   does not assign `crypto/rand.Reader` (Go's own docs discourage it). The model already enforces this.
5. **OS randomness failing** (the docstring's environment claim). I ran a child process that installs a
   seccomp filter (TSYNC) making `getrandom` return `EPERM` and then calls `uuid.New()`. Result: `fatal
   error: crypto/rand: failed to read random data (see https://go.dev/issue/66821): operation not
   permitted`, exit status 2. That is a runtime fatal, not a panic: no `recover`, no `PanicV`. On a
   kernel older than 3.17 (`ENOSYS`), the fallback to `/dev/urandom` also ends in `fatal` if the open
   fails. A blocked `getrandom` (no entropy at boot) blocks, which is non-termination. None of these is
   a panic, so none is a counterexample. In the model, `New` returns where the real process dies. The
   real behavior is a prefix of a modelled run, so no safety (no-panic) conclusion is affected, the same
   way an exit counts as a safe run. **The environment claim is therefore not needed for soundness of the
   no-panic results.** It only matters if a conclusion ever depends on the process continuing past
   `New` (liveness), which `Robust` does not state.
6. **`GOEXPERIMENT=boringcrypto` builds.** `crypto/internal/rand.reader.Read` panics on a BoringSSL RNG
   error, and that panic escapes `uuid.New`. I did not try to make BoringSSL's RNG fail. **Condition
   N3:** the program is not built with `boringcrypto`. Default builds (the pinned toolchain, no
   `GOEXPERIMENT`) take the `drbg`/`sysrand` path of attack 5. FIPS mode (`GODEBUG=fips140=on`) also ends
   in `sysrand.Read`, which is fatal, not a panic.
7. **`testing/cryptotest.SetGlobalRandom`** (`crypto/internal/rand.SetTestingReader`, reached by
   linkname). This is test-only and not reachable from a deployed program or from Goose. Out of scope.
8. **`ID`/`Time` on boundary values.** The zero UUID and the all-`0xff` UUID give
   `ID = 0`/`4294967295` and `Time = 1152921504606846975` (test). There is no panic path, and any `w32`
   is allowed.
9. **Inconsistency / the context.** Both triples are about opaque function-table entries. No lemma
   fixes those entries, so no `⊢ False` follows. Like every names-only trust-boundary axiom, they are
   stated for every `GoGlobalContext`/`go.Semantics`, and would be false in a context where `New`
   resolves to a panicking body. This is generic (`notes/axiom-review/dsv-inits/os-signal.md`,
   attack 8).
10. **Cross-world entailment.** Neither post holds a pure equation about an opaque function of a
    pointer (`True`, an existential value). Not applicable.
11. **Claiming too much about the value.** The posts say nothing about the bytes, so nothing about
    uniqueness of `ClientId` (`int32` of 32 random bits, which collide between clients with birthday
    probability) can be derived from them. The proof (`NewClientLog.lean`) treats the id as arbitrary.

Go check (scratch module `/shared/tmp/uuidrev`, deleted; go1.27.3, uuid v1.3.1):

    TestDefault           PASS  (100000 × New().ID()/Time(); max ID=4294967295 Time=1152921504606846975)
    TestSetRandPanics     PASS  recovered: boom
    TestPoolSetRandPanics PASS  pool recovered: boom
    TestSeccomp           PASS  child err=exit status 2:
                                fatal error: crypto/rand: failed to read random data
                                (see https://go.dev/issue/66821): operation not permitted

## Conditions under which `New.wp_proof` holds

- **N1:** no `uuid.SetRand` with a reader that can fail anywhere in the program. In the tree, this
  means no spec of `SetRand` may coexist with this axiom.
- **N2:** `crypto/rand.Reader` is not reassigned before uuid's initialization. Perennial's `↦□`
  enforces this.
- **N3:** a default (non-`boringcrypto`) build.
- **Environment:** none needed for the no-panic claim. An OS randomness failure is a runtime fatal
  (process exit), not a panic. The docstring's wording ("else the process dies, which no `Robust`
  execution covers") is accurate as a description. It could say plainly that a fatal is not a panic,
  so that the claim is not an assumption that the results need.

## Proposed restatement (not applied)

Make the dependence on `rander` explicit, so that a later `SetRand` spec cannot coexist with it.
`isPkgInit uuid` would give a persistent fact that `rander` holds the default reader, for example
`globalAddr uuid.rander ↦□ (crypto/rand's reader)` (opaque initializer:
`notes/axiom-review/dsv-inits/github-com-google-uuid.md`). A sound spec of `SetRand` would then need
full ownership of `rander`, which no one has after init, so `SetRand` stays unprovable by
construction instead of by omission. Alternatively, add to `New.wp_proof`'s docstring the rule
"no spec of `uuid.SetRand` may be added while this axiom stands". That is cheaper but is checked by
no one.

No counterexample program was built: no gap can be reached from a provable program in the current
tree. No bug found in the Go code. uuid's documentation states the `SetRand` panic, and swiftpaxos
uses the default reader.
