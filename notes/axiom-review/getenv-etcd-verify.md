# `os.Getenv` and `strings.ToLower`: strengthened to retire the `ETCD_VERIFY` checks (etcdstorage, 2026-11-20)

Branch `prove-etcdstorage/2026-11-20`. Not an `axiom`-skill review: a check, against the Go sources and
by measurement, of two strengthened trust-boundary axioms, which replace five axioms
(`verify.Verify`, `backend.ValidateCalledInsideApply`, `ValidateCalledOutSideApply`,
`ValidateCalledInsideUnittest`, `VerifyBackendConsistency`; `verify.IsVerificationEnabled`, which they
call, is proved too, never having been an axiom). See `notes/axiom-review/etcd-verify.md` for why the checks took
`envVerifyOff` (sweep repairs 1, B4).

## What changed

Before, the world assumption `verifyEnvOff e` (`Proof/go_etcd_io/etcd/client/pkg/v3/verify/Env.lean`:
`ETCD_VERIFY` is unset at start, or its lower-cased value is none of `all`, `assert`, `lock`, and no
code of `e` sets it) reached the logic as the token `envVerifyOff`, which each check's axiom took as
a premise. Now one axiom reads it: `os.Getenv`'s post (`Spec/os/Getenv.lean`)

    envVerifyOff -∗ ⌜key = "ETCD_VERIFY" → etcdVerifyOffValue v⌝

with `etcdVerifyOffValue v` = `lowersTo v w = false` for `w` each of `all`, `assert`, `lock`; and
`strings.ToLower`'s post (`Spec/strings/ToLower.lean`) says, for every ASCII word `w` without an
upper-case letter (`lowerWord`), `r = w ↔ lowersTo s w` (`Proof/strings/Lower.lean`). The checks are
then proved from the translated code (`IsVerificationEnabled`, `Verify`, `verifyLockEnabled` and the
three lock checks, `VerifyBackendConsistency`), none of whose branches that read the stack, call the
closure or panic is reached.

Both posts are strengthenings (the old posts were `True`); every existing caller drops them (`-`).

## `os.Getenv` (Go 1.27.3, the pinned toolchain)

`os.Getenv(key)` is `testlog.Getenv(key); v, _ := syscall.Getenv(key); return v` (`os/env.go`).
`syscall.Getenv` (`syscall/env_unix.go`) reads `env`, the map built once from `envs` (the process's
initial environment, `runtime_envs`) by `copyenv` under `envOnce`, under `envLock`; only
`syscall.Setenv`, `Unsetenv` and `Clearenv` (behind `os.Setenv`, `os.Unsetenv`, `os.Clearenv`) change
it. No cgo is linked into etcd's programs here, so no C `setenv` changes the process environment
behind Go's copy (and Go's copy would not see it anyway). Hence: in a run where `ETCD_VERIFY` is off
at start and no code sets it (`verifyEnvOff`), every `os.Getenv("ETCD_VERIFY")` returns the start
value (or `""` if unset), whose lower-case form is none of the three. (With `ETCD_VERIFY` twice in the
initial environment, `copyenv` keeps the first and clears the others: "the value" is the first.) That is the new post, given
the token, which program start hands out only under `verifyEnvOff e` (`goose_adequacy_start`).

The token's satisfiability argument (`Start.lean`, `Env.lean`'s header) still holds: `os.Getenv` is
names-only, so a model in which it returns `""` satisfies its spec whatever the token is, and
`lowersTo "" w = false` for a non-empty `w`.

## `strings.ToLower` (Go 1.27.3)

`strings.ToLower(s)` (`strings/strings.go`): if `s` is ASCII, it lower-cases `A`-`Z` byte by byte
(returning `s` itself if it has none); otherwise it is `Map(unicode.ToLower, s)`. `Map` ranges over `s`
by rune (an invalid byte is `utf8.RuneError`, U+FFFD, and is written as its 3-byte encoding
`EF BF BD`), and writes `unicode.ToLower(r)` for each rune `r` (never negative, so no rune is dropped).
`unicode.ToLower` maps a rune to one rune. So `ToLower(s)` equals an ASCII word `w` iff `s` is the
concatenation, byte `b` of `w` by byte, of the encoding of a rune `r` with `unicode.ToLower(r) = b`
(an invalid byte, giving `EF BF BD`, never matches an ASCII byte; a valid encoding decodes to its rune
and only to it).

Which runes `unicode.ToLower` maps to an ASCII byte other than themselves, outside `A`-`Z`: measured
by enumerating every rune, `GOTOOLCHAIN=go1.27.3 go run .` of

```go
for r := rune(0); r <= unicode.MaxRune; r++ {
	l := unicode.ToLower(r)
	if l < utf8.RuneSelf && l != r && !(r >= 'A' && r <= 'Z') {
		fmt.Printf("rune U+%04X -> %q\n", r, l)
	}
}
```

which prints exactly `U+0130 -> 'i'` (LATIN CAPITAL LETTER I WITH DOT ABOVE, `C4 B0`) and
`U+212A -> 'k'` (KELVIN SIGN, `E2 84 AA`); `strings.ToLower("LOCK") == "lock"` is `true`. That is
`lowerAlts` (`Proof/strings/Lower.lean`): `b`, its upper-case letter, and those two.

The Kelvin sign matters: excluding only ASCII spellings of `lock` would have been false
(`ETCD_VERIFY=LOCK` enables the lock checks). `verifyEnvOff`'s docstring speaks of the
lower-cased value, which `lowersTo` now states exactly, so the world assumption is unchanged.

## Verdict

Both strengthened posts are true of the pinned Go (by the source for `Getenv`, by the source and an
exhaustive measurement for `ToLower`). Net: five axioms out, none in; two axioms' posts
strengthened.

## 2026-11-25: restated over the run's value (the owner's decision)

`os.Getenv`'s post is now `⌜key = "ETCD_VERIFY" → v = etcdVerifyEnv⌝`, with `etcdVerifyEnv` an opaque
`GoString` (the run's value, `""` when unset) and the closed theorems' premise `EtcdVerifyOff :=
etcdVerifyOffValue etcdVerifyEnv`; the token `envVerifyOff` and the axiomatized `verifyEnvOff` are gone
(`notes/decisions.md`, "`ETCD_VERIFY` as an environment premise over its value"). Checked against the
same source reading as above: every `os.Getenv("ETCD_VERIFY")` of a run returns the first value of the
initial environment (or `""`) as long as nothing calls `Setenv`/`Unsetenv`/`Clearenv`, which no verified
code can (no spec). So one constant per run is faithful; the post is stronger than before only in naming
the value, which is what that argument shows. A deployment whose unverified code set the variable would
falsify it; the docstring says so. The constant is one for all machines of a deployment, a restriction
of the model (as `GODEBUG`'s `godebugFips140`), not a claim about Go: the theorems are about
deployments in which every machine's value enables no check.

## Review of the value-naming post (2026-11-25, the `axiom` skill): refuted across processes; weakened

The draft post `key = "ETCD_VERIFY" → v = etcdVerifyEnv` holds within one process (no spec for
`os.Setenv`/`Unsetenv`/`Clearenv`/`syscall.Setenv`; Go reads the copy taken at start) but is false across
processes: one opaque constant for every machine and every boot lets a proof show that two processes read
equal values. Go: process A with `ETCD_VERIFY` unset writes its value to durable storage, process B with
`ETCD_VERIFY=0` reads its own and the stored one and panics if they differ: 5/5 panics (both values are
off). Lean: the payload invariant `m = etcdVerifyEnv` from A's read and B's read discharge B's panic branch,
with no environment premise (sketch, not built). **Fix:** the post gives only offness,
`key = "ETCD_VERIFY" → EtcdVerifyOff → etcdVerifyOffValue v`; no proof can relate two processes' values. The
proofs used only offness (`IsVerificationEnabled`; `bbolt`'s `Verify` ignores the post). `goose_adequacy_start`
without the environment premise survives (its conclusion is about the operational semantics, which has no
environment; the satisfiability argument never used `hEnv`).
