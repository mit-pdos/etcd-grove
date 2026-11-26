# `NewServer_dist`'s axiom-tok finding (rule 2b, `threadTok`), F7 against M1

2026-11-26, F7 session 9 (branch `etcd-safe-f7`). For the lead: whether `NewServer_dist.wp_proof` gets an allow entry
(and a `trunc` line) in `etc/axiom-tok-allow.txt`. **No entry is added here.**

## The finding

`etc/AxiomTokCheck.lean` walks `Perennial.EtcdGrove.etcd_dist.NewServer_dist.wp_proof` (statement
`NewServer.specG_dist`, `Spec/.../etcd/dist/NewServerDist.lean`) at the gate's default depth (14). The walk is
**capped** (`PRUNEAT` 64 undominated scenarios, merged) and **truncated** (`depth:` `ownMap`, `backend.bbAt`,
`bbolt.isBolt`, ... 41 notes). Rule 2 fails at the generic level point `*` in every scenario kept (8 of 208, all
the same counts, so not an artefact of merging capped scenarios):

| | `threadTok` (`tok:T`) |
|---|---|
| consumed | 3, of which 2 handed back by callbacks (`ret:T 2`) |
| produced | 3, of which 2 handed to callbacks (`cb:T 2`) |
| supplied directly | 1 (`Htok`) |

Rule 2b: what the axiom hands a callback the user supplies is paid only by what the user supplies directly (a
callback may never return); `cb 2 > direct 1` fails.

## Which callbacks: a provenance walk

The walker keeps no provenance, so a copy of it was run that prints, for every token under a callback
(`cbDepth ≥ 1`), the chain of definitions unfolded to reach it (`/shared/tmp/f7prov/AxiomTokCheckProv.lean`: the
gate's file plus a `path` stack pushed at each unfold and an `IO.eprintln` in `walkTok`; script
`/shared/tmp/f7prov/f7prov.sh`, run on fk-lean2 at `etcd-safe-f7` `adaea37e3a`; not committed: the gate is
unchanged). It finds exactly four tokens under a callback, all in one premise:

```
cb  threadTok :: NewServer.specG_dist > lease.bootCfg > srvRevokeOpen > EtcdServer.revokeExpiredLeases.spec
ret threadTok :: NewServer.specG_dist > lease.bootCfg > srvRevokeOpen > EtcdServer.revokeExpiredLeases.spec
cb  threadTok :: ... > EtcdServer.revokeExpiredLeases.spec > srvFieldsAt > lessorOk
ret threadTok :: ... > EtcdServer.revokeExpiredLeases.spec > srvFieldsAt > lessorOk
```

The callback is **`srvRevokeOpen`**, `lease.bootCfg`'s revocable conjunct
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseApi.lean:69`: `m = .revocable → srvRevokeLevels ∧ srvRevokeOpen`),
which is `EtcdServer.revokeExpiredLeases.spec` (`LeaseRun.lean:50`): a Hoare triple the caller proves and the axiom
uses (the revocable cluster's open case of `run`'s expiry arm). Its two token pairs:

1. **`revokeExpiredLeases`'s own token** (`Spec/.../etcdserver/EtcdServer__revokeExpiredLeases.lean:54-56`): its
   precondition takes `threadTok` (the axiom hands one to the callback: `cb`) and its postcondition returns it
   (`ret`). This is the `-∗` premise that takes a `threadTok` and returns one.
2. **`Promote`'s token, inside that triple's precondition**: `srvFieldsAt` holds `lessorOk`
   (`InvApplier.lean:614`), whose `□ ∀ d, {{ threadTok }} Promote d {{ RET #(); threadTok }}` the axiom supplies to
   the callback. Seen from the axiom: the callback hands it a token when it calls `Promote` (`ret`), and gets it
   back in `Promote`'s postcondition (`cb`).

No other premise or post of the statement hands a token to a callback: `bootstrapContract`'s triple, `Hpeers`'s
wand, `Hlslot`, `Hγa` and the post's offered specs contribute none (`Htok` and the post's `threadTok`, both arms,
are the only tokens outside a callback), as far as the walk reaches (it truncates at depth 14: a token below a
truncated definition is not seen).

## Reading

Neither pair is the axiom handing out a token it does not own:
- pair 2 is a borrow: `Promote`'s postcondition gives back the token its precondition took, within one call the
  callback makes; the walker does not pair a nested spec's pre and post, so the `cb` counts against the direct
  supply although it is paid by the `ret` of the same call;
- pair 1 is the revocable mode's open case: `NewServer` does not call `revokeExpiredLeases`; it keeps the premise
  for `run`'s expiry arm, which `Start`'s goroutine runs on a token of its own. Within `NewServer_dist`'s triple
  the callback is never run, so nothing is handed; the walker cannot see that the premise is only stored.

So the finding is the walker's over-approximation of a stored callback with a borrowing method, not a token the
statement manufactures. An allow entry would name the key `*:handed 2/direct 1` (rule 2b) with this note, and the
`trunc` line the walk's 41 `depth:` notes. Outside the revocable mode (`m ≠ .revocable`, every deployment but
`leaseExpiry`'s) the conjunct is vacuous, but the walk is per statement, not per mode.

## M1

M1's `NewServer_dist` (head `e2d102d97b`, merge of `etcd-safe-m1` into `etcd-safe-m1-top/2026-11-25`): **the same finding.** Built in a worktree of its own on fk-lean2 (`~/eg/wt/m1-e2d`, `NewServerDist` at `e2d102d97b`,
BUILD 0), the gate's walk gives `etcd_dist.NewServer_dist.wp_proof`: 200 findings, capped (208 scenarios, 8 kept,
all `cb:T 2`, `ret:T 2`, `tok:T` 3 consumed and 3 produced), `TOKEN: level *: handed to a callback 2, supplied
directly 1`, truncated with the same 41 notes; the provenance walk finds the same four tokens on the same paths
(`lease.bootCfg > srvRevokeOpen > EtcdServer.revokeExpiredLeases.spec`, and `> srvFieldsAt > lessorOk` inside it).
So the finding predates F7: it comes with `lease.bootCfg`'s revocable conjunct (the lease-expiry plan's X5,
2026-11-04), not with F7's new premises (`Hlslot`, `Hγa`) or the auth-on posts, which add no token. M1's allow file
has no entry for the axiom either, so M1's full gate fails on it the same way (the `etc/axiom-tok-check.py` run at
M1: `FAILED: 1 unknown (scenario cap), 1 unknown (truncated)`, plus 51 stale entries of axioms outside that one-axiom
json, an artefact of the single-axiom run).

## Reproducing

- the gate's walk: `~/eg/logs/f7atok-m1e.sh` on fk-lean2 (copy `/shared/tmp/f7atok-m1e.sh`) for M1 in its own
  worktree `~/eg/wt/m1-e2d` (seeded from `etcd-safe-m1`'s `.lake/build`, `NewServerDist` built first under the lock
  and `MemoryMax=55G`); the F7 walk is Session 8's (`/shared/tmp/f7atok.raw`);
- the provenance walk: `~/eg/logs/f7prov.sh WORKTREE TAG` (copy `/shared/tmp/f7prov/f7prov.sh`), summaries
  `~/eg/logs/f7prov-{f7,m1}.sum`.
