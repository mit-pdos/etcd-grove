# `NewServer_dist`'s axiom-tok entry: the capped walk, traced (M1, 2026-11-26)

This note records the reasoning behind `etc/axiom-tok-allow.txt`'s entry for
`etcd_dist.NewServer_dist.wp_proof`. It is a trace, not an `axiom`-skill review. The axiom's soundness reviews are
in `notes/etcd-dist-plan.md` §17.3.

**Corrected after an independent triage** (`newserver-dist-axiom-tok-triage.md`, verdict "justified with
corrections", no key changed). Its three corrections are applied below:

- the source of the rule-2b token key (§Rule 2);
- why `3:Dep` differs from the proved walks;
- the subset argument, restated as a textual argument (§Rules 3 and 7).

This trace's first instrumented run recorded only `walkI`'s unfolds, not `walkProp`'s. So it read two tokens of a
`Prop`-level premise as the post's.

## The walk is capped, and the cap is global

The scenario cap is `MAXSCEN = 1024`, a constant of the checker (`etc/AxiomTokCheck.lean:163`). It applies to every
axiom, and the allow file cannot set it per axiom.

- **What a scenario is.** One choice among the statement's `∨`, `∧` and `if` branches. The number of members a
  deployment has does not bound the number of scenarios.
- **What the walk did.** One of `NewServer_dist`'s sub-walks passed the cap. The checker collapsed that sub-walk's
  scenarios into one worst scenario, taking the pointwise maximum of what is produced and the minimum of what is
  consumed. Its final set has 208 scenarios, and those that come from the collapsed part are marked `<capped>`.
- **What the collapse costs.** The rule-3 counts it reports are not reliable. It reported 200 findings.
- **Uncapped runs.** A diagnostic copy of the checker with the cap raised to 8192, 65536 and 2^20 was run on the VM.
  None finished: each was stopped after 6 to 25 minutes, against 12 s for the capped walk.
- **The decision.** The cap was not changed (the M1 lead's decision: a tool change is out of scope). The entry covers
  the capped walk's keys, and each class of key is traced below.

## Rule 2 (tokens)

**Plain rule 2 passes on every scenario of the final set, the collapsed ones included, so it passes on every scenario
of the uncollapsed walk.** The collapsed scenario produces at least what each scenario it replaces produces, and
consumes at most what each consumes. Every later step of the walk is monotone in that order (the checker's header,
"Scenario sets"). A scenario that produced more tokens than it consumed would therefore fail rule 2 after the collapse
as well. No token is produced beyond what is consumed.

**`2:*:handedtoacallback2/supplieddirectly1`** (rule 2b) is not a mint. The triage traced it with an unfold stack
that both `walkI` and `walkProp` push (its run2):

```
TOK threadTok pol=neg cb=0 flips=1 stack=[named, specG_dist]                        -- the pre's Htok (direct)
TOK threadTok pol=pos cb=0 flips=2 stack=[specG_dist]  (x2)                          -- the post's threadTok, both arms
TOK threadTok pol=pos cb=1 flips=2 stack=[spec, srvRevokeOpen, bootCfg, specG_dist]  -- cb
TOK threadTok pol=neg cb=1 flips=3 stack=[spec, srvRevokeOpen, bootCfg, specG_dist]  -- ret
TOK threadTok pol=pos cb=1 flips=4 stack=[lessorOk, srvFieldsAt, spec, srvRevokeOpen, bootCfg, specG_dist] -- cb
TOK threadTok pol=neg cb=1 flips=3 stack=[lessorOk, srvFieldsAt, spec, srvRevokeOpen, bootCfg, specG_dist] -- ret
```

**The post's `threadTok` is not under a callback (`cb=0`).** Every token that is under a callback sits inside the
caller-supplied premise `lease.bootCfg` (`LeaseApi.lean:69`). Its revocable conjunct is `srvRevokeOpen`
(`LeaseRun.lean:50`), and `srvRevokeOpen` is `EtcdServer.revokeExpiredLeases.spec`, a triple the caller proves and
the axiom may use. It accounts for the two pairs:

1. **`revokeExpiredLeases`'s own token.** Its pre takes a `threadTok`, which the axiom hands to the callback (`cb`).
   Its post returns the token (`ret`). This pair is paid by the pre's `Htok`, which is supplied directly: if the
   callback never returns, the axiom loses that token, and it gains none.
2. **`Promote`'s token.** The callback's pre holds `srvFieldsAt`, which holds `lessorOk`
   (`InvApplier.lean:614-617`), with `□ ∀ d, {{ threadTok }} Promote d {{ RET #(); threadTok }}`. When the callback
   calls `Promote`, it gives a token, which the walker counts as handed back (`ret`). The axiom returns it in
   `Promote`'s post, which the walker counts as handed to a callback (`cb`). This is a borrow within one call: the
   walker does not pair a nested method's pre and post.

So 2b counts 2 tokens handed to callbacks against 1 supplied directly. Plain rule 2 passes: 3 tokens produced, 3
consumed. The proved theorems carry the identical premise (`specG`'s text) and the identical four tokens, which is
why they have the same 2b key. The triage notes that 2b is not monotone under the collapse; that does not matter here,
because the provenance enumerates every token occurrence, and the worst uncollapsed scenario is exactly 2 against 1.
The same reading is in the F7 team's independent walk (`origin/etcd-safe-f7` `625dda2fae`,
`notes/axiom-review/f7-newserver-atok.md`).

## Rules 3 and 7: compared with the proved `wp_NewServer`

The dist axiom's post has the text of `NewServer.specG`'s post (`etc/dist-axiom-diff.py`). The only differences are
`γn`, now an `∃` with its two pure facts. The linked theorem `wp_NewServer : NewServer.spec` proves that post (at
auth off; `Proof/go_etcd_io/etcd/server/v3/etcdserver/Link.lean`).

The dist axiom and the proved theorems were walked by the same checker, with the same cap, in the same run
(`axiom-tok-check.py --lean-only --names`, a diagnostic list of the three; the auth-on theorem was added because the dist axiom quantifies over the auth mode).

The walks were run in one go on the head after the merge of lean `009822ac30`: `NewServer_dist.wp_proof`,
`wp_NewServer : NewServer.spec` (auth off, every `cmp`) and `server_new_auth_on : NewServer.specM true` (auth on,
`cmp = false`). Between them, the last two cover every mode the dist axiom quantifies over; `specG`'s premise
`cmp = true → on = false` excludes the rest. All three walks are capped.

| walk | scenarios | findings | distinct keys (rules 2, 3, 7) |
|---|---|---|---|
| `NewServer_dist.wp_proof` | 208 | 200 | 45 |
| `wp_NewServer` | 416 | 91 | 41 |
| `server_new_auth_on` | 136 | 164 | 43 |

- **The two theorems together have 44 of the dist axiom's 45 keys.** This includes the token key
  `2:*:handedtoacallback2/supplieddirectly1`, which both proved theorems have.
- **No key of the theorems is missing from the dist axiom.**
- **The one extra key, `3:Dep:produced1/consumed0`, comes from the depth cutoff, not the collapse.**
  - Its `∃ Dep` binder is in `storeTxnWriteIs` and is used at `batchTxSpecG`, on the path `srvBuiltG > srvReadBuiltNK >
    isApplyLessor > revokeClause > mvccDeleter > mvccTxn > mvccTxnI > isTxnWriteT > storeTxnWriteIs > batchTxSpecG`,
    14 unfolds deep. This is CP3's attribution for `EtcdServer.leaseTimeToLive`'s same key.
  - The proved statements are one `Prop` unfold deeper (`NewServer.spec`/`specM` → `specG`), so their walks stop above
    `batchTxSpecG` at `--depth` 14. They have the matching transfer `7:Dep:IPropGF`.
  - The triage confirmed this both ways. At `--depth=15` both proved theorems report the same key. At `--depth=13`
    the dist axiom loses it and keeps every other rule-2 and rule-3 key.

**Why the shared keys are enough: the textual argument.** Key equality across capped walks is weak evidence on its
own: each collapse happens at a different point, and a key is a binder name plus counts. The argument that holds is
textual:
- Every finding is of a binder inside text the proved statements share verbatim: the post, and every premise but the
  deviations `etc/dist-axiom-diff.py` lists.
- A rule-3 or rule-7 verdict for a binder depends only on the subterm under it (`bindVar`/`closeAtom`).
- So every such finding is a finding of the text that the proved `wp_NewServer`/`server_new_auth_on` establish in
  process. This covers the 44 shared keys and `3:Dep`, whatever their counts.

**The moved `γn`.**
- The top-level `∃ γn` is neutral: the walk never finds it naked.
- The `7:γn:NetNamesGF` key belongs to `srvApplyAllBuilt`'s inner binder, which is shared text.
- The post's `γn.N = srvNet γ` fixes the one `IProp`-carrying field of `γn`.
- The deviations' premises, `Hpeers` and `noProxyEnv`, are consumed. A consumed premise only adds to what the axiom
  consumes, and the run reports no rule-6 holder that could credit one. (Triage §3.)

The keys are in `etc/axiom-tok-allow.txt`'s entry, one per finding class; the walk's raw output is not kept.

## Truncations

The walk truncates in the post's backend, lease and bbolt definitions (`bbAt`, `isBolt`, `lessorPin*`, `ownMap`,
...). These are the definitions whose truncations other entries already accept: `storage.OpenBackend`,
`bootstrap.wp_proofOne`, and the server-handle axioms. The same post is the post of the proved `wp_NewServer`.
