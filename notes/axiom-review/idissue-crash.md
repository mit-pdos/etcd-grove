# The issue record after a crash: `idutil.Generator.Next`'s trusted model (etcd-dist D4b)

Reviewed 2026-11-24 by the `axiom` skill, on branch `etcd-safe-d4b/2026-11-24` (not `axiom/<slug>`: the
review is part of the D4b packet and its counterexample is Go only).

**Under review.** `TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`'s `Generator.Next.impl` (Go's body,
then `assume` of the record's `"Issue"` of `(id, g)`) over the record as changed by D4b
(`GooseLang/Ext/IdIssue/Impl.lean`): `IdIssueState := GMap w64 (Option Loc)`; `"Issue"` succeeds iff the
entry is absent or `some g`; a crash maps every entry to `none` (`idIssueCrash`). The crash interpretation
(`IdIssue/Crash.lean`) is untrusted (proved).

## Claims, in plain words

1. Two generators of one machine never return one id, within a run (unchanged by D4b).
2. (new) A generator started after a crash of the machine never returns an id any generator of that
   machine returned before the crash, whatever its address.
3. Nothing is claimed across machines (the record is local); distinct prefixes are proved, from the
   deployment's distinct 16 low bits of member ids.

## Go facts (fork pin, `pkg/idutil/id.go`)

`NewGenerator(m, now)`: prefix `uint64(m) << 48`, suffix `lowbit(unixMilli, 40) << 8`; `Next`: atomic
add 1 to the suffix, `prefix | lowbit(suffix, 48)`. Two generators of one prefix return one id iff their
suffix ranges overlap: the earlier (start t0) issued more than `256·(t1 − t0)` ids, or `t1 < t0` (clock
back), or the 40-bit millisecond field wrapped (2^40 ms, 34.8 years, apart). Go never checks.

## Attacks

| # | program | Go | model | verdict |
|---|---|---|---|---|
| A1 | `Twice`: two generators of prefix 7 started at one millisecond in one process, `panic` if their first ids are equal | panics (`TestTwicePanics`) | provable: the second `"Issue"` is refused, `assume` does not return, so the `panic` is unreachable (`idIssueFrag_agree`, the generators' distinct addresses) | **holds as documented**: a *program* restriction (one generator per prefix per start, starts spaced by the rate) that the trusted model's docstring states and etcd meets (`NewServer` makes one). Not new with D4b |
| A2 | `Restart`: first run writes its first id to a file; after a crash the next run, clock reading the same millisecond, panics if its first id equals the file's | panics (`TestRestartPanicsWhenClockSame`); not with the clock forward (`TestRestartFineWhenClockForward`) | provable after D4b: the old entry is `none`, the new `"Issue"` refused; the proof gets the old id's `idIssuePast` from the crash rest (`idIssueFrag_crash_past`) against the new `idIssueFrag` (`idIssueFrag_past`). Before D4b the model admitted the reissue when the new generator sat at the old address, so this was *not* provable | **holds as an environment assumption**, new with D4b: the wall clock does not step back across a machine's restart (RTC, NTP), and the earlier generators' rate. This is exactly `nonissues/etcd-request-id-restart-reuse.md`, which D4b turns from "not reachable in the model" into an assumption of the model |
| A3 | a crash between `Next`'s atomic add and its `"Issue"` | the id was never returned, so nothing holds it | not recorded; the restarted generator may issue it | no gap |
| A4 | no successor crash state (would silently exclude crashes) | n/a | `idIssueCrash` is a total function: every crash has its record | no gap |
| A5 | an initial record that refuses ids from the start | n/a | `initLocal` is the default: a theorem quantifies over every record, the empty one included | no gap |
| A6 | two machines with equal low 16 bits | collide (`examples/idissue/semantics/per_machine_test.go`) | the local record does not exclude it; the proof needs the deployment premise | no gap (proved, not assumed) |
| A7 | 2^40 ms wrap | would reissue across 34.8 years | excluded forever (the record is never cleared) | over-exclusion, disclosed (Go's own comment: "before 35 years") |

## Verdict

**Survives, with its assumptions disclosed**: no program found that panics under etcd's use (one
generator per start) while the clock never steps back across restarts. The counterexamples A1/A2 are
real Go panics that the model proves away; both are the documented restrictions (A1 a program
restriction, A2 the environment assumption D4b adds for real crashes). The Lean proofs of A1/A2 were
**not built** (no Goose project added: argued from `wp_IdIssue`, `idIssueFrag_agree`,
`idIssueFrag_past`, `idIssueCrashStart_past`), so the "provable" column is an argument, not a theorem.

The owner's decision is whether to accept A2's assumption ("a machine's clock does not step back across
its restart, and a member issues at most 256 ids per ms since its previous start") as an environment
assumption of `etcd_safe` with crashes. The alternative that needs none is a fix to etcd (seed the
generator from the WAL's highest own id, or `max(now, persisted)`), recorded in the nonissue.

Go: `examples/axiomcx/idissuecrash/` (go1.27.3, `GOTOOLCHAIN=local go test`, all three pass).
