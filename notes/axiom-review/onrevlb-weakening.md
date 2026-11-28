# Auth-on revision lower bounds: two false conjuncts dropped (2026-11-27)

Branch `etcd-safe-onrevlb/2026-11-27` (from lean `a6d58d572d`). This change weakens two landed interim
axioms. It shrinks trust, so it was pre-approved.

## The false conjuncts

`kvRevLbZ γk n` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRequest.lean:1428`) says that the
**auth-off** model `kvModel γk L₀` of a committed raft prefix is longer than `n`. With auth on, the
member's revisions come from `kvModelOn` (`KVAuthModel.lean:1763`). `kvModelOn` skips a request that is
denied at apply time, while `kvModel` applies it. The two lengths drift apart in both directions.

**Witness** (dsverify-net's independent review; reproduced here). A user `a` with no role puts `x`. The put is
denied at apply. A permitted user `b` then runs `k` transactions of `If(Version(x)=0).Then(Put y)`, and then
puts `z`. In `kvModel`, `a`'s put applies, so each transaction sees `x` and takes the empty else
branch, which does not bump the revision. In `kvModelOn` (and in Go), each transaction puts `y`. For `k ≥ 2`,
the reply revision of `b`'s put is at least `kvModel`'s length, so `kvRevLb` is false. Go test against fork
`d26dd5da6f38`: `onrevlb-weakening/revlb_test.go`. Its output is in `onrevlb-weakening/test-output.txt`, where
the reply revision is 5 and `kvModel`'s length is 4.

| axiom | Today | With this change |
|---|---|---|
| `KV_PutOn_dist` (`Spec/.../dist/KVPutOnDist.lean`) | a success gives `… ∗ kvRevLb Γ.kv m.hdr.revision ∗ writeCheckedD …` | a success gives `… ∗ writeCheckedD …`, with no `kvRevLb` |
| `Txn_CommitOn_dist` (`Spec/.../dist/TxnCommitOnDist.lean`) | a success gives `… ∗ client.txnRevLb Γ.kv (txnWireOf b.model) m ∗ (if … checked)` | a success gives `… ∗ (if … checked)`, with no `txnRevLb` |

The in-process auth-on contracts give these bounds only with auth off. `etcdPutSpecMW`
(`Proof/go_etcd_io/etcd/client/v3/KVServiceOn.lean:480-489`) has `⌜on = false⌝ → kvRevLb …`, and
`etcdTxnSpecMW` (`:627`) has `⌜on = false⌝ → txnRevLb …`. The proved handlers in `Results.lean:1016/1095/1893`
carry the same guard. `client.client_put_on` (`ResultsOn.lean:58`) and `client_txn_on` (`:371`) have none.
No proof used these conjuncts. Two positional patterns lost one `-`: `dist/client/grantPut.lean:138` and
`dist/client/RunAuth.lean:319`. The other patterns end in a `-` that takes the rest, so they are unchanged.

**Why the F9 reviews missed it.** `etc/dist-axiom-diff.py` paired these axioms with the auth-off
`kv.Put.spec`/`txn.Commit.spec`. Those specs have the bounds unguarded, so the bounds were not a difference.
No review (`f7-a.md`, `f7-rerev-a.md`, `f7-txn-review.md`, `f7-txn-nested-review.md`,
`f9-auth-combined-review.md`) discussed `kvRevLb` at auth on.

## (b) Audit: every auth-on dist axiom's post against its auth-on contract

**The state σ at auth on.** `writeAuD` (`AuthViewDist.lean:151`), `clientOpAuOn` (`KVServiceOn.lean:945`)
and `kvOpAuM on` (`ServerKVOn.lean:342`) are all `kvAu1G γk …` (`InvRequest.lean:1036`). That is an AU over
`etcdKV γk σ`, the ghost variable `γk.st`. With auth on, `kvInvOn` holds its other half at
`kvStateOf (kvModelOn γk st₀ L) (kvLeasesOn γk st₀ L)` (`KVAuthModel.lean:1943-1947`). So σ is the
`kvModelOn` state. The replies' σ is `kvStateOf x.log lt`, built from the member's applied log
(`putReplied`/`deleteReplied`/`txnReplied`/`rangeReplyOk`, `KVService.lean:420/662/243/…`). The
`*Ans_st` lemmas (`KVService.lean:2034-2200`) derive the posts' pure facts from those predicates for any `lt`,
in either mode. They need `kvRevLb` only to pass on the one the auth-off answer carries.

| axiom | auth-on contract | conjuncts the contract does not give | action |
|---|---|---|---|
| `KV_PutOn_dist` | `client_put_on` / `etcdPutSpecMW true` | `kvRevLb Γ.kv m.hdr.revision` (`m.hdr.revision = σ.rev+1`, `kvRevFits`, `kvLogOk σ` are `putAns_st`'s, from `putReplied`) | **dropped** |
| `Txn_CommitOn_dist` | `client_txn_on` / `etcdTxnSpecMW true` | `client.txnRevLb` (verdict, responses, revision, `kvRevFits`, both `kvLogOk`s are `txnAns_st`'s) | **dropped** |
| `KV_DeleteOn_dist` | `client_delete_on` | none (revision `(kvOpStep … σ).rev`, `kvRevFits`, both `kvLogOk`s: `delAns_st`, from `deleteReplied`; `rangeEnd ≠ [0]` is a premise) | kept(2026-11-27: the pairing later found a missing `reqShape` premise, not a revision fact: `onpairs-deleteon.md`) |
| `KV_GetOn_dist` | `client_range_on` | none (`m.hdr.revision = σ.rev`, `kvRevFits`, `kvLogOk`, selection: `rangeAns_st`; `serializable = false` is a premise) | kept |
| `WatchOn_dist` | no auth-on in-process contract (`watcher.Watch.spec` + `v3rpc.watchSpec`) | `cmpOkOf Γ.kv` is `kvRevLbZ`-based (`kvCmpPermit`, `InvRequest.lean:1519`), but at auth on the server never compacts: `srvKVInvsOn` has `E.Cp = kvCpOk γr.kv` and `γr.kv.cmp = false` (`KVApplyOn.lean:399-401`), so `kvCpOk` forces `-1` and a response's compact revision is `0`, `cmpOkOf`'s first disjunct. Its events are reads of the AU's σ (`kvModelOn`). | kept (backed by that argument; no theorem) |
| `Lease_GrantOn_dist`, `Lease_RevokeOn_dist` | `client_lease_grant_on`, `client_lease_revoke_on` | none: no revision fact claimed (the theorems' `etcdReached … m.hdr.revision` is not copied) | kept |
| `Lease_TimeToLiveOn_dist`, `Lease_LeasesOn_dist` | `lessor.*.spec` at `etcdLease*SpecOn` | none: no revision fact claimed | kept |
| `New_user_dist`, the five `Auth_*_dist` | `clientv3.New.spec`, `v3rpc.adminReplied` | none: no revision fact (`adminRepliedD`, `AuthViewDist.lean:171`) | kept |

The audit is about revision facts (`m.hdr.revision = …`, `kvRevFits`, `kvLogOk`, `kvRevLb`-like facts). The
other conjuncts are the F7/F9 reviews' and were not re-reviewed. No STOP: nothing unbacked is used by a proof.

## (a) The gate's blind spot

`etc/dist-axiom-diff.py` now takes a `theorem` as a pair's source: its statement up to `:= by`. It still
takes an `abbrev` spec. So an axiom can be paired with a proved contract that has no spec of its own. The
selftest gained a theorem-sourced pair (`etc/dist-axiom-diff-selftest/SrcOn.lean`). It passes as listed,
and it is refused when the copy adds a `kvRevLb` the theorem does not give.

`KV_PutOn_dist` is now paired with `client.client_put_on`, and `Txn_CommitOn_dist` with
`client.client_txn_on`, each with its own `dev` lines. The post's line says `putReplied`/`txnReplied` is
replaced by what it gives, and it states that there is no revision bound. A re-added `kvRevLb` would now be an
unlisted difference. The new pairing also surfaced `client_txn_on`'s `hsh` (`kvShapeAll`), which the dist
axiom does not take. `f7-txn-nested-review.md` ("Noted") already argued that this matters only for a refusal's
content, and the `dev` line cites it.

**Not done (next), updated 2026-11-27** (`onpairs-deleteon.md`, branch `etcd-safe-onpairs/2026-11-27`):
- Done there. `KV_DeleteOn_dist`, `KV_GetOn_dist`, `Lease_GrantOn_dist` and `Lease_RevokeOn_dist` are paired
  with `client_delete_on`, `client_range_on`, `client_lease_grant_on` and `client_lease_revoke_on`.
- The delete pairing found an over-claim: no `auth.reqShape` premise. The premise is now added to the axiom.
- Left:
  - generalize `client_delete_on` to any `opts` (untrusted; overlaps dsverify-net's Q2);
  - `client_lease_ttl_on` and `client_lease_leases_on`, then their pairs;
  - an auth-on watch contract for `WatchOn_dist`.
  `Lease_TimeToLiveOn_dist`, `Lease_LeasesOn_dist` and `WatchOn_dist` stay paired with the generic client
  specs. A `def`-instantiating gate extension was not built, because a service spec's text does not line up
  with a client triple.
