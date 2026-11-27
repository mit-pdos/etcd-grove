# Triage of `NewServer_dist`'s axiom-tok entry (independent, 2026-11-26)

The entry under triage is `etc/axiom-tok-allow.txt`'s `entry` and `trunc` lines for
`Perennial.EtcdGrove.etcd_dist.NewServer_dist.wp_proof` and the paragraph above them. They were added in commit
`026edd807f`, and the trace behind them is `notes/axiom-review/newserver-dist-axiom-tok.md`. This triage was done at
`c997c37fd8` (origin/etcd-safe-m1-top/2026-11-25). Nothing is committed.

**Verdict: justified with corrections.** NewServer_dist mints nothing the gate's rules are meant to catch, so the
entry's keys can stay as they are. Two of its three explanations are wrong in their detail, though, and one argument
is weaker than the entry presents it:

- The rule-2b token key does not come from the post's continuation. It comes from a caller-supplied premise.
- The extra `3:Dep` key comes from the walk's depth cutoff, not from a different collapse.
- The subset-of-keys argument needs the textual argument stated below to be sound under a capped walk.

## What was run

All runs were on the VM, at the gate's default depth 14 unless a depth is given. Raw output is in
`/home/ubuntu/.claude-E/jobs/b20ef685/tmp/tri-scratch/run*.{jsonl,err}`, which is not kept in the repository.

- **run1.** The gate's `etc/AxiomTokCheck.lean` walked the three statements in one run: `NewServer_dist.wp_proof`,
  `wp_NewServer` and `server_new_auth_on`. It reproduces the trace's table exactly:

  | walk | scenarios | findings | distinct keys |
  |---|---|---|---|
  | `NewServer_dist.wp_proof` | 208 | 200 | 45 |
  | `wp_NewServer` | 416 | 91 | 41 |
  | `server_new_auth_on` | 136 | 164 | 43 |

  All three walks are capped, and none is a mint candidate. Taking both theorems together, `dist − (theorems) =
  {3:Dep:produced1/consumed0}`, and `(theorems) − dist = ∅`. The entry's keys equal the dist walk's keys exactly.
- **run2, run6.** An instrumented copy of the checker, untracked and deleted afterwards. It adds an unfold stack that
  `walkI` and `walkProp` push at each definition, and prints one line per token, per `Dep` atom use, per callback
  entry, per `∃ γn : NetNames` binder and per naked use of one.
- **run3.** The same instrumented copy, run on the two proved theorems.
- **run4, run5.** The gate's checker at depth 15 on the two theorems (run4), and at depth 13 on the dist axiom (run5).

The commands were `vmlake env lean --run etc/AxiomTokCheck.lean --axioms=FILE <the gate's --part flags> MODULE…`,
with modules `Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewServerDist` and
`Proof.go_etcd_io.etcd.server.v3.etcdserver.Results`, after a `vmlake build` of both.

## (1) The rule-2b key `2:*:handedtoacallback2/supplieddirectly1`: not a mint, but the entry names the wrong source

These are the tokens of the dist walk (run2):

```
TOK threadTok pol=neg cb=0 flips=1 stack=[named, specG_dist]                        -- the pre's Htok (direct)
TOK threadTok pol=pos cb=0 flips=2 stack=[specG_dist]  (x2)                          -- the post's threadTok, both arms
TOK threadTok pol=pos cb=1 flips=2 stack=[spec, srvRevokeOpen, bootCfg, specG_dist]  -- cb
TOK threadTok pol=neg cb=1 flips=3 stack=[spec, srvRevokeOpen, bootCfg, specG_dist]  -- ret
TOK threadTok pol=pos cb=1 flips=4 stack=[lessorOk, srvFieldsAt, spec, srvRevokeOpen, bootCfg, specG_dist] -- cb
TOK threadTok pol=neg cb=1 flips=3 stack=[lessorOk, srvFieldsAt, spec, srvRevokeOpen, bootCfg, specG_dist] -- ret
(+ balanced cb=0 pairs in the post: lessorOk under srvFieldsBuiltNA, authRecoverOk under srvSnapRO)
```

**The post's `threadTok` is not under a callback (`cb=0`).** The top-level triple is `∀ Φ, P -∗ ▷ (Q -∗ Φ) -∗ WP`.
The walker enters a callback only at a negative `∀ Φ : _ → IProp` or a negative WP, and the continuation's `∀ srv
err` binds values, not `Φ`. All four tokens under a callback sit inside the premise `lease.bootCfg`
(`LeaseApi.lean:69`). Its revocable conjunct is `srvRevokeOpen` (`LeaseRun.lean:50`), and `srvRevokeOpen` is
`EtcdServer.revokeExpiredLeases.spec` (`Spec/.../EtcdServer__revokeExpiredLeases.lean:46-56`). That is a triple the
caller proves and the axiom may use (`run`'s expiry arm). It accounts for the two pairs:

- **`revokeExpiredLeases`'s own token.** Its pre takes a `threadTok`, which the axiom hands to the callback (`cb`).
  Its post returns the token (`ret`).
- **`Promote`'s token.** The callback's pre `srvFieldsAt` holds `lessorOk` (`InvApplier.lean:614-617`), which
  contains `□ ∀ d, {{ threadTok }} Promote d {{ RET #(); threadTok }}`. The axiom supplies that method to the
  callback. Seen from the axiom, the callback gives a token when it calls `Promote` (`ret`, by the walker's
  convention), and the axiom gives it back in `Promote`'s post (`cb`).

In the success arm this makes 2 tokens handed to a callback against 1 supplied directly (`Htok`), and 2b fails.
Plain rule 2 passes: 3 tokens produced, 3 consumed. Neither pair is a mint:

- **The first pair is paid by `Htok`.** If the callback never returns, the axiom loses that token. It gains none.
- **The second pair is a borrow within one call.** `Promote` returns the token only after it receives one. 2b's
  premise, "the callback may never return", does not apply, because the walker does not pair a nested method's pre
  and post.

The proved theorems carry the identical premise (`specG`'s text) and the identical four tokens. run3 shows them with
the stack `[…, srvRevokeOpen, bootCfg, specG, spec|specM]`. That is why they have the same 2b key.

**Why the trace got this wrong.** It reports `CBTOK … flips=2 stack=[]` and `RETTOK … flips=3 stack=[]`. Its stack
recorded only `walkI` unfolds, and `bootCfg`, `srvRevokeOpen` and `spec` are `Prop` definitions that `walkProp`
unfolds, so the trace read a flips-2 token with an empty stack as the post's.

**This agrees with the F7 team's independent provenance walk** (origin/etcd-safe-f7 `625dda2fae`,
`notes/axiom-review/f7-newserver-atok.md`). It found the same four tokens in
`specG_dist > lease.bootCfg > srvRevokeOpen > EtcdServer.revokeExpiredLeases.spec`, with the same reading.

**The rule-2 argument under the cap is valid.** The collapse (`Res.cap`) takes the pointwise max of productions and
the min of consumptions, and every later step is monotone for plain rule 2. A plain rule-2 pass on the collapsed
scenario therefore implies a pass on every scenario it replaced. 2b is not monotone under the collapse, because the
`ret:` min can only raise `direct`. That does not matter here: the provenance enumerates every token occurrence in
the walk, and the worst uncollapsed scenario is exactly 2 against 1, the key itself.

**Correction to the entry text.** Replace "tokens traced (the continuation's and `Promote`'s returned token: no
mint)" and the paragraph's 2b bullet with this:

> the tokens handed to a callback are those of the caller-supplied premise `lease.bootCfg` ⊇ `srvRevokeOpen` =
> `EtcdServer.revokeExpiredLeases.spec` (its pre's token, returned by its post), and `Promote`'s, borrowed and
> returned inside that triple's pre (`srvFieldsAt` ⊇ `lessorOk`); the post's `threadTok` is not under a callback;
> the proved theorems have the same premise and the same four tokens.

The same fix applies to `notes/axiom-review/newserver-dist-axiom-tok.md`, §Rule 2, items 1-2.

## (2) The subset argument under a capped walk: the conclusion holds, the argument needs restating

**Key equality across three capped walks is weak evidence on its own.**

- Each walk collapses at different points.
- A key is a binder name plus counts. Two binders with the same name, or counts inflated by a collapse, can coincide
  or differ by accident.

**The sound form of the argument is textual.**

- **The post's binders.** The dist post is `specG`'s post verbatim, apart from `γn` (`etc/dist-axiom-diff.py`, and
  re-diffed here). A rule-3 or rule-7 verdict for a binder inside the post depends only on the subterm under that
  binder (`bindVar`/`closeAtom`). So every such finding is a finding of the same text, which the proved theorems
  establish as a post in-process. That text is therefore satisfiable by the real `NewServer` and is not a shape that
  mints.
- **The premises.** The same argument covers every premise, which is identical text apart from the deviations in
  (3).
- **What this argument covers.** It covers all 44 shared keys and `3:Dep`, whatever their counts.

**`3:Dep:produced1/consumed0` comes from the depth cutoff, not the collapse.**

- **The dist walk.** run2 shows `Dep` used once, at `batchTxSpecG` (`InvStore.lean:1694`, `LockOutsideApply`'s pre).
  Its `∃ Dep` binder is in `storeTxnWriteIs` (`InvStore.lean:5864`), reached by
  `srvBuiltG > named > srvReadBuiltNK > isApplyLessor > revokeClause > mvccDeleter > mvccTxn > mvccTxnI >
  isTxnWriteT > storeTxnWriteIs > named > batchTxSpecG`, 14 unfolds deep.
- **The proved walks.** run3 shows no `Dep` use at all in either proved walk. Their statements are one `Prop`
  unfold deeper (`NewServer.spec`/`specM` → `specG`), so the walk cuts the same path at depth 14 before
  `batchTxSpecG`.
- **The trace's explanation.** The trace says "their walks collapse at other points". That is not the reason.
- **The depth runs.** run4 confirms the depth explanation. At `--depth=15`, both proved theorems report
  `atom:Dep: produced 1, consumed 0`, the dist axiom's exact key, alongside the same 2b key and the other rule-3 keys:
  - `wp_NewServer`: 480 scenarios, capped;
  - `server_new_auth_on`: 208 scenarios, capped.

  run5 confirms it in the other direction. At `--depth=13`, the dist axiom loses `3:Dep` (272 scenarios, capped)
  and keeps every other rule-2 and rule-3 key.

  With that, the dist axiom's 45 keys are all keys of the proved statements walked at the same effective depth.
- **Attribution.** CP3's attribution of `leaseTimeToLive`'s `3:Dep` names the same binder through the same chain
  (`isApplyLessor > revokeClause > … > batchTxSpecG`), so attributing the key to that pattern is right. The
  difference: there the handle is consumed, and here it is produced. The textual argument above covers that.

**Corrections.**

- Replace the trace's "Their walks collapse at other points, so the rule-3 count of `Dep` differs" with this: the
  proved statements are one definition deeper, so their walks stop above `batchTxSpecG` at `--depth` 14.
- In the entry, replace "every key a key of the proved … (same post text)" with this: every finding is of a binder
  inside text the proved statements share verbatim (the post and all premises but the deviations of (3)); 44 of the
  45 keys recur in their walks, and `3:Dep` sits one definition below their depth cutoff.

## (3) The deviations: none mints a token or resource the proved specs do not

**`γn` moved to the post's `∃`.** run6 shows four `∃ γn : NetNames GF` binders in the dist walk:

| binder | where | rule 7 |
|---|---|---|
| ex 19 | the top-level `∃ γn` | neutral, never naked |
| ex 54 | `srvApplyAllBuilt` | naked |
| ex 116, ex 164 | `ccMembRes` | neutral |

- **The one naked binder is inner, shared text.** Ex 54's naked uses are `consumed: γn.N.P st / γn.N.O st / γn.N.img
  …` under `netTransport`'s bundles. The proved walks have exactly this binder and these uses.
- **The `7:γn:NetNamesGF` key is that inner binder's.** It is not the moved `γn`'s, so the moved binder adds no
  finding.
- **Its fields are fixed or carry no resource.** Its only `IProp`-carrying field is `N : NetPayload`
  (`rafthttp/Net.lean:105`), and the post's own pure fact `γn.N = srvNet γ` fixes it to the in-process payload. The
  walker does not read that fact; the proved spec's `%Hγn` is the same fact. Its other fields, `slots`, `reg` and
  `dir` (`dir` also fixed), are names.
- **The resources at those names are ghost state, not tokens.** The ghost state at those names in the post
  (`srvNetMember`, `srvTrTok`, `srvServeRes`) is no longer paid by a consumed `netHttpOk γn id`, so in the dist it is
  ghost state at axiom-picked names: in effect a fresh allocation, as `Net.lean:542`'s allocation lemma does. It is
  not a token (`threadTok`/`levelTok`, …), and the rules do not count it. Plain rule 2 still passes on every
  scenario. Whether such ghost state is honest across machines is the axiom's soundness question (plan §17.3), not
  this gate's.
- **The extra neutral binders are a depth effect.** The two extra `ccMembRes` binders appear because the dist walk is
  one level shallower.

**`Hpeers` in place of `netHttpOk γn id` / `%Hγn`.**

- **`Hpeers`.** It is consumed (in the pre), persistent, and binds only `pid : w64` and `a : GoString`, which carry
  no `IProp`. It is pure-guarded and unfolds to `addrProto a (httpPeerSvc γ.cl pid)…`.
- **Why consumed premises cannot mint.** A consumed premise only adds to what the axiom consumes, which makes rule 2
  harder to pass, never easier.
- **The rule-6 credit check.** The one way a consumed opaque could help the axiom is a rule-6 holder credit. No
  holder was reported in these runs. A credit would only be possible if some axiom produced `addrProto`/`osEnvIs`
  while consuming tokens, and `http_addr_set` is a theorem.

**`noProxyEnv`.** It is consumed and persistent: a big separating conjunction of `osEnvIs k ""`. It has no binders
and no token, so the same reasoning applies.

**`etcdURLsFit U.peer`, `etcdURLsFit U.client`.** These are not a deviation from today's `specG`. The diff against
`specG` shows only the comment changed; `specG` took the premise earlier and the dist copy restored it. They are pure
Lean-level premises, so the walk flips them to supplied, and they hold no resource.

**`[π : NetProtoGS]`.** It is an instance binder, which the walk skips.

**Truncations.** The dist's 41 truncation notes are the post's and premises' backend, bbolt, lease and context
definitions (`ownMap`, `bbAt`, `isBolt`, `lessorPin*`, `isMutex`, `isClosedchanInit`, …). The proved walks have the
same kinds of notes. No note is in the deviations' text. As in every walk of this post, a token below a truncated
definition is unseen.

## Summary of corrections

1. **Token key.** The entry's 2b explanation names the wrong source. The source is the caller-supplied premise
   `lease.bootCfg` ⊇ `srvRevokeOpen` (`revokeExpiredLeases.spec`'s pre/post token, plus `Promote`'s borrow inside
   its `srvFieldsAt`). It is not the post's continuation, and not the post's `srvFieldsAt`. The trace note's §Rule 2
   needs the same fix.
2. **`3:Dep`.** It is a depth-cutoff difference (the proved statements are one `Prop` unfold deeper), not a collapse
   difference.
3. **The subset argument.** Restate it as the textual argument: every binder of a finding lies in text shared
   verbatim with the proved specs. Add one sentence on the moved `γn`: its walk is neutral, the `7:γn` key is
   `srvApplyAllBuilt`'s inner binder, and `γn.N = srvNet γ` fixes its one `IProp` field.

No key needs to change. The entry's key list matches the walk exactly.
