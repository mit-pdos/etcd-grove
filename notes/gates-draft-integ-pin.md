# Gates draft for `etcd-safe-integ-pin/2026-11-27` (@ `21403763b3`): entries for the lead's trust review

Branch `etcd-safe-integ-pin-gates/2026-11-27`, worktree `/shared/etcd-grove-pingates`. The build state is copied from
`/shared/etcd-grove-integpin` (`.lake/build/lib` only, `cp -a`: `lake build --no-build` reports all 29753 jobs up to
date without `ir/`), along with `.lake/tcb.json` and `.lake/model-param.jsonl`. Perennial `/shared/perennial-01f1c6ee1`,
manifest `/shared/tmp/integpin-manifest.json`. No Lean change. Everything below is a DRAFT: the lead decides.

## 1. `mode` (466 against the baseline's 457): drafted, the gate passes

The 9 findings are three literals in each of three statements. In every statement they are `kvInvM false` (the
`#Hkvinv` premise), `srvErM false` (the post's `srvBuiltR` argument) and `lease.srvInvAt false` (the post's lease part),
next to `E.authOn = false` and `ρ.rd.kv.ch0 = alarmChain false …`. These are the same three rows, at the same three
places, as in `NewServer.specR`. The existing entry `etc/mode-allow.txt` `lit-mode unmoved … NewServerR\.lean::NewServer\.specR::  # 3`
classifies specR's three as "the restart constructor spec scoped to auth off (srvStop.scope); an auth-on restart stage
moves it". I read each statement:

- `NewServer.specC` (`Spec/.../etcdserver/NewServerCrash.lean`): its header says the post is "specR's word for word"
  at the crash image, so it has the same auth-off scope.
- `NewServer.specRAt` (`Proof/.../etcdserver/NewServerRAt.lean`): specR at one image's bootstrap contract
  (`specR_of_RAt` derives specR from it), with the same three literals.
- `NewServer.specC_dist` (`Spec/.../examples/etcd/dist/NewServerCDist.lean`): specC's distributed copy. Its header says
  "specC is auth off" and lists the changes from specC (network only), which `dist-axiom-diff` checks.

Entries: three `lit-mode unmoved` lines, each scoped to `FILE::DECL::` exactly as specR's, placed after specR's
entries. Baseline (`etc/mode-baseline.txt`): etcdserver 276 -> 282 and a new row `examples/etcd/dist` 0 -> 3, each with
a comment. The precedent for raising the baseline together with a classification is `cee6468281` (S4's
`serve_member_lease`, baseline 456).

## 2. `model-param` (36): drafted, the gate passes (`--reuse` on integpin's run: ok, 502 findings accepted by 488 pairs)

**Cause.** The handoff called this a "binder path differs" problem, but the binder path is the same. On this line,
every one of the 28 client axioms also *receives* `grpcStreamerOk/{Req,Rep}`. The source is the line's §25 watcher
refactor (`05325ced29`). It keeps each stream under
`wgsGuard V G callSl := □ (watchSrvFacts V -∗ isWGS V G callSl)` (reached through `isNewClient` > `isClientWatcherCore` >
`watcherMu`), and `watchSrvFacts` > `watchConnFacts` > `etcdWatchConn` > `etcdConnStream` > `streamIcOk` sits left of
that wand. So the stream contract occurs at both polarities: each axiom supplies and receives both `streamIcOk/{Req,Rep}`
and `grpcStreamerOk/{Req,Rep}` (all keyed). `judge_pairs` accepts the atom only when every `recv` line is paired.
Lean's 8 pairs therefore matched their lines but "accepted nothing", because the atom as a whole failed.

**Entries.** Each of the 28 axioms gets 4 pairs, `streamIcOk/{Req,Rep}` and `grpcStreamerOk/{Req,Rep}`, with the axiom
itself as the depositor (its `supp` lines). Lean's 8 stay as they are, so 104 lines are new, appended under a section
header at the end of `etc/model-param-allow.txt`. The 72 `streamIcOk` pairs are lean's S3.4 entry repeated
mechanically. The 32 `grpcStreamerOk` pairs are a new key: see the judgment item (a) below.

## 3. `axiom-tok`: drafted (GD-2, `1332aaad20`), the gate passes (`ok (360 Prop axioms walked: 299 pass, 61 by an entry or pair)`)

The 24 direct findings were the line's client axioms walked after S3.4. Each existing entry line got the extra keys
the raw walk lists for it (read by a script from `/shared/tmp/pingates/atok.jsonl` with the checker's own
`finding_key`, not copied from a sibling). A comment block before the F7 S13 header explains them. The ~39 rule-5
cascade findings and the two scenario-cap unknowns (`NewServer_dist`, `Serve_dist`) cleared without entries:
0 tainted predicates, 0 need an entry, 0 unknown. `--selftest --reuse-raw`: 0 failures (real-pass
`EtcdServer.leaseTimeToLive` ok). The groups:

- **A, 12 axioms, KV_Put_dist's S3.4 keys exactly** (`KV_Compact_dist`, `Auth_{AuthEnable,RoleAdd,RoleGrantPermission,UserAdd,UserGrantRole}_dist`,
  the six `view.*` lease axioms): rule 2 `8 + len(vs)×2k / 1` for k = 1..4 (one `len(vs)+len(vs)` per connection's
  stream contract: the call options' `backoffOkT` `levelTok 0`, lent by the backoff's caller), and rule 7 `Dn`, `cd'`.
  Precedent: lean's S3.4 `KV_Put_dist` line and NewStream's decision-1b entry.
- **B, 3 axioms, the same with `supplieddirectly0`** (`Watch_dist`, `RequestProgress_dist`, `WatchOn_dist`): the
  8/0 shape of their existing entries (no token in the pre). Precedent: the same.
- **C, 8 gated auth-on axioms** (`KV_{Put,Delete,Get}On`, `Txn_CommitOn`, `Lease_{Grant,Revoke,TimeToLive,Leases}On`):
  their connections are `isEtcdConnG`, whose stream contract S3.4 gates on `clientReady` (which itself holds
  `etcdConnStream`). The walk counts one `len(vs)+len(vs)` (Txn two), fewer than the auth-off siblings' four (more
  truncation: 41 notes against 33), plus `Dn`, `cd'`, and a NEW rule 7 `∃ Q : IProp` "in a stuck term
  `isBroadcastChanInternal`". It appears in exactly these eight. My reading: `Q` is grpc's `ctxDoneCh` broadcast payload
  (the only use of `isBroadcastChanInternal` in the client/grpc stack), inside `ctxOk`'s `ctxErrs` disjunct. It reaches
  the axiom's side because `clientReady` sits left of the gates' wands, which flips the stream contract and the
  `grpcStreamerOk` in its pre. That is the same flip as model-param's item (a). `Q` is an argument of the Perennial
  channel predicate only, like `P` inside `isCancelCtxOf`, and no post mentions it. I traced this from the shape, not
  with an instrumented walk. No precedent on lean (lean has no authd axioms).
- **E, `New_user_dist`** (reversed polarity: its post returns `isNewClient`): rule 2 `len(vs)×2k / 9` for k = 1..5 and
  rule 7 `Dn`, `cd'`. The returned client's stream contracts put the user's call-option backoff contracts at the axiom's
  side. "Supplied directly 9" = the pre's token plus the 8 unary contracts' pres. Not a mint: the claimed contract
  `etcdStreamIcOk` is proved in-process from the translated code (`Client.streamClientInterceptor`, S3.4;
  `clientv3.New.wp_proof`). That code calls the backoff only from the stream's retry (`waitRetryBackoff`, proved),
  lending its own caller's token, as NewStream's entry says. No lean precedent.

## 4. Full gates and tcb (GD-2, at `1332aaad20`)

`etc/gates.sh` (`GATES_FAILFAST=0`, integpin manifest, `PERENNIAL_CHECKOUT=/shared/perennial-01f1c6ee1`, under flock and a
64G cap): **all passed** (log `/shared/tmp/pingates/gates.log`): tcb 375 axioms / 0 sorries / 91 opaques, axiom-tok ok,
collections 69 match, model-param ok (502 by 488 pairs), mode ok (466, baseline 466), bounds 389, tier ok, links,
goose, gen-init, issues, k8s and premisefix all ok. `etc/tcb-report.py --check`: trust base matches
`etc/tcb-baseline.txt` (375 axioms, 0 sorries, 91 opaques).

## Needs the lead's judgment

(a) model-param, the 32 `grpcStreamerOk/{Req,Rep}` *received* pairs: a new key with no precedent on lean. It arises
from the §25 `wgsGuard` wand, not from S3.4 itself. My reading is that it is S3.4's entry read at the flipped polarity:
the interceptor calls the streamer at its own registered models, whose registration the depositor supplies. The
judgment needed is whether that is right, or whether `wgsGuard`'s placement of `watchSrvFacts` left of a wand should
instead be treated as a statement shape to review (the walk sees a registry atom handed to the axiom's user there).
(b) mode: raising the two baseline rows (a ratchet) rather than moving specC/specRAt/specC_dist over the slot.
(c) axiom-tok, `New_user_dist` (group E above): backoff-callback tokens `len(vs)×2k` against 9 supplied, read as
NewStream's decision-1b lending at the reversed polarity, backed by the proved `streamClientInterceptor`.
(d) axiom-tok, NEW: rule 7 `Q` (`ctxDoneCh`'s broadcast payload) in the 8 gated auth-on axioms (group C). It comes
from the same `clientReady`-left-of-a-wand flip as (a), and was traced by shape only (an instrumented walk would
confirm it). Also their single `len(vs)` pair (the walk truncates more there).
(e) axiom-tok entries A/B (15 lines) are KV_Put_dist's S3.4 keys, mechanical, but they rest on the line's
pre-S3.4 entries, which were themselves marked for the lead's or etcd-grove-03's confirmation (F2, F7).

### Handoff GD-1 (2026-11-27; context limit)

Drafted and passing: `mode` (`mode: ok (466, baseline 466)`) and `model-param` (`ok`, on integpin's `--reuse` jsonl).
`axiom-tok` has been run but its entries are not drafted (section 3 says what is left). The full `gates.sh` and
`tcb --check` have not been run. Rule #8: no Lean, statement, premise or axiom changed.

### Handoff GD-2 (2026-11-27; coordinator's stop at the context limit)

Everything is drafted and green: mode, model-param, axiom-tok (`1332aaad20`). The full `gates.sh` passed and
`tcb-report --check` is ok (section 4). Rule #8: no Lean, statement, premise or axiom changed. What is left is the
lead's judgment on (a) to (e). Nothing is landed or posted.
