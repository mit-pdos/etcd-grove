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

## 3. `axiom-tok`: NOT drafted yet (context limit)

Run at this branch (`--check --raw`; log and raw kept at `/shared/tmp/pingates/atok.{log,jsonl}`): 63 need an entry and
2 are unknown (`NewServer_dist`/`Serve_dist`, at the scenario cap, as before). The direct findings are the 24 client
axioms. The other ~39 are the rule-5 cascade (tainted `grpcConn`, `credsYieldRaw`, `grpcConnOptsRaw` via
`New_user_dist`, `metadata.builtRawMDRaw`, …), which should clear once the 24 have entries. The sample I checked,
`KV_Compact_dist`, shows exactly KV_Put_dist's S3.4 keys: rule 2 `8/1`, `8+len(vs)+len(vs)/1`, … up to 4 pairs of
`len(vs)` (presumably with rule-7 `Dn`/`cd'`, as KV_Put_dist).

**What is left.** For each of the 24, extend its existing entry line (`etc/axiom-tok-allow.txt`, the lines ~321-327,
~378-420) with the extra keys the log lists for it, modeled on lean's `KV_Put_dist` line 192:
- 8/1 axioms: KV_Put_dist's key list.
- Txn (10/1): Txn_Commit_dist's.
- Watch/RequestProgress/WatchOn (8/0): the `…/supplieddirectly0` analogue.
- New_user_dist: read its own keys, since its polarity is reversed and it has no lean precedent.
Then rerun `--check --reuse-raw /shared/tmp/pingates/atok.jsonl` (seconds) and
`--selftest --reuse-raw` (real-pass `EtcdServer.leaseTimeToLive`). After that run the full `etc/gates.sh` (`GATES_FAILFAST=0`,
`LAKE_PACKAGES=/shared/tmp/integpin-manifest.json PERENNIAL_CHECKOUT=/shared/perennial-01f1c6ee1`) and `tcb-report --check`.

## Needs the lead's judgment

(a) model-param, the 32 `grpcStreamerOk/{Req,Rep}` *received* pairs: a new key with no precedent on lean. It arises
from the §25 `wgsGuard` wand, not from S3.4 itself. My reading is that it is S3.4's entry read at the flipped polarity:
the interceptor calls the streamer at its own registered models, whose registration the depositor supplies. The
judgment needed is whether that is right, or whether `wgsGuard`'s placement of `watchSrvFacts` left of a wand should
instead be treated as a statement shape to review (the walk sees a registry atom handed to the axiom's user there).
(b) mode: raising the two baseline rows (a ratchet) rather than moving specC/specRAt/specC_dist over the slot.
(c) axiom-tok: `New_user_dist`'s new keys once drafted (reversed polarity, no lean precedent).

### Handoff GD-1 (2026-11-27; context limit)

Drafted and passing: `mode` (`mode: ok (466, baseline 466)`) and `model-param` (`ok`, on integpin's `--reuse` jsonl).
`axiom-tok` has been run but its entries are not drafted (section 3 says what is left). The full `gates.sh` and
`tcb --check` have not been run. Rule #8: no Lean, statement, premise or axiom changed.
