# `NewServer_dist`'s axiom-tok entry: the capped walk, traced (M1, 2026-11-26)

This note records the reasoning behind `etc/axiom-tok-allow.txt`'s entry for
`etcd_dist.NewServer_dist.wp_proof`. It is a trace, not an `axiom`-skill review. The axiom's soundness reviews are
in `notes/etcd-dist-plan.md` §17.3.

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

**`2:*:handedtoacallback2/supplieddirectly1`** (rule 2b) is not a mint. It was traced with a diagnostic copy of the
checker that prints the stack of unfolded definitions at each token it tags as handed to a user-supplied callback
(`cb:`) or handed back by one (`ret:`):

```
RETTOK threadTok fl=1 flips=3 stack=[lessorOk, srvFieldsAt]
CBTOK  threadTok fl=1 flips=4 stack=[lessorOk, srvFieldsAt]
CBTOK  threadTok fl=1 flips=2 stack=[]
RETTOK threadTok fl=1 flips=3 stack=[]
```

The two tokens counted as handed to a callback are these:

1. **The post's `threadTok`** (`flips=2`, at the top level). The axiom hands it to the triple's continuation (the
   user's `Φ`), as every triple that takes a token and gives it back does. It is paid for by the pre's `threadTok`,
   which is supplied directly.
2. **The post of `lessorOk`'s `□ ({{ threadTok }} Promote d {{ RET #(); threadTok }})`.** This is the lessor's
   `Promote` contract (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvApplier.lean:614-617`, reached through
   `srvFieldsAt` in the post's server fields).
   - The contract sits inside the post, so it is under the continuation (`fl=1`).
   - The checker therefore counts the token its pre takes as "handed back by a callback" (`ret:`, subtracted from
     what is supplied directly).
   - It counts the token its post gives back as "handed to a callback".
   - The method takes one token from its caller and returns it: nothing is minted.

So `2b` sums the continuation's token and `Promote`'s returned token (2), against one token supplied directly. In-process,
the proved `NewServer.specG` has the same `lessorOk` in the same post.

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
- **The one extra key, `3:Dep:produced1/consumed0`, was traced.** A diagnostic copy of the checker prints the
  unfold stack at each `Dep` atom. The atom is produced once, six flips and three callbacks deep, at
  `srvBuiltG > srvReadBuiltNK > isApplyLessor > revokeClause > mvccDeleter > mvccTxn > mvccTxnI > isTxnWriteT >
  storeTxnWriteIs > batchTxSpecG`. That is CP3's attribution for `EtcdServer.leaseTimeToLive`'s same key: the
  revoke's backend batch-transaction callbacks, inside the server's read handle. The proved theorems have the
  matching transfer `7:Dep:IPropGF`. Their walks collapse at other points, so the rule-3 count of `Dep` differs
  between the three capped walks.

The keys are in `etc/axiom-tok-allow.txt`'s entry, one per finding class; the walk's raw output is not kept.

## Truncations

The walk truncates in the post's backend, lease and bbolt definitions (`bbAt`, `isBolt`, `lessorPin*`, `ownMap`,
...). These are the definitions whose truncations other entries already accept: `storage.OpenBackend`,
`bootstrap.wp_proofOne`, and the server-handle axioms. The same post is the post of the proved `wp_NewServer`.
