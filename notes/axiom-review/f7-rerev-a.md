# F7 re-review, groups A+B after the fixes (`etcd-safe-f7` @ `6d9d9fd662`)

Read-only (`axiom` skill; nothing built). Since `d946f6cbda`: `A` → `Γ.au`, UserAdd's bound and `□` update; the
other admin drafts unchanged. Go: `client/v3/client.go:285-307`, `etcdserver/v3_server.go:107-152,326-372,1035-1058`.

## Verdicts
| Draft | Verdict |
|---|---|
| `New_user_dist` | SOUND (needs the Serve tie, condition C below) |
| `KV_PutOn_dist`, `KV_DeleteOn_dist` | SOUND (they do not read `Γ.au`; nothing changed in substance) |
| `Txn_CommitOn_dist` | SOUND (read-only branch now at `Γ.au mid`; condition C) |
| `KV_GetOn_dist` + `authFloorD`/`readCheckedD` | SOUND (condition C). Precision note N1 (`readAuthedD`), not a soundness gap |
| `Auth_UserAdd_dist` | SOUND (bound added as asked; the `□ (∀ um, ⌜…⌝ → histAu …)` form matches the mirror) |
| `Auth_UserGrantRole_dist`, `_RoleAdd_`, `_RoleGrantPermission_`, `_AuthEnable_` | SOUND (unchanged since B) |

**Condition C (for promoting any draft that reads `Γ.au`).** These drafts are sound only while every axiom that
serves `etcdSvc Γ mid` with `Γ.auth = true` takes `memberUpOn(L) … (Γ.au mid)`. Today that holds vacuously
(`Serve_dist` requires `Γ.auth = false`); with `Serve_dist_proposed` it holds through the tie. No other
serve axiom (an in-process `Serve`, `grpc.Server.Serve` over a table) can be allowed to serve an auth-on `Γ`
without this tie.

## 1. Is the free-name attack closed? Yes.

- **A client can still get address facts for a `Γ` whose `Γ.au mid` it owns.** `etcdAddr_set` (`S2Interim.lean:131`)
  takes any `Γ`, and so does `net.Listen`'s `addr_set_proto_tok`. So a draft can be *instantiated* before any start
  allocates `Γ.au` (for instance `ofKV` with `au` overridden by injective names whose `hist` the prover allocated).
- **That is sound, because a success arm needs a server that answers.** In Go, a call that reaches no server, or an
  empty grpc server (`Unimplemented`), fails. `New` fails too: `getToken` returns every error except
  `ErrAuthNotEnabled` (`client.go:298-303`). An auth-off member that would answer `ErrAuthNotEnabled` is served only
  by `Serve_dist` at an auth-off `Γ₀`. Its address was set once, to `etcdSvc Γ₀ mid` (`addrUnset` and
  `netAddrLeft` are spent once per address). The opaque `etcdSvc` has no law, so no proof can move a fact from
  `etcdSvc Γ₀ mid` to `etcdSvc Γ mid` (a proxy at a second address can't either: it would need to convert
  `grpcSrvPI` bytes into `grpcCliPI` bytes for another table). So with today's axioms, no Go run reaches a success
  arm at an auth-on `Γ`.
- **With `Serve_dist_proposed`, `Γ.au mid` is the serving member's real names.** `memberUpOnL … (Γ.au mid)` asks for
  `E.authMode = .on (Γ.au mid)` of the `E` in the `NewServer` post that built the member's `isServerReqM true`/`srvAuthLb`
  (`memberUpOn_intro`, `Served.lean:191`). In today's `NewServer` that `γa` is fresh (`∃ γa`). In P-A1's proposal,
  `NewServer` consumes `authNamesFreshD γa`, which holds the whole `hist`, `pub`, `cur`, `fen`, `cap`, … authorities
  (all 12 fields). So a prover that allocated `Γ.au mid` gives up its authority to start the member, and keeps
  only fragments that are true. An auth-off `NewServer` (`on = false`, `Hγa = True`) has `E.authOn = false`, so
  `E.authMode = .off` (`authOn` is read off `authMode`, `memberUpOn_served`), and it cannot meet `.on γa`. Two
  members cannot share one `Γ.au` value (exclusive tokens), so the injectivity premise is redundant, as stated.
- Residual (usability only): a **restarted** member cannot meet `memberUpOnL` at the old `Γ.au mid`
  (`authNamesFreshD` needs `hist` at `[bootState]`, but that history has grown), so auth-on restarts cannot serve a fixed `Γ`.

## 2. `authFloorD`'s index alignment: aligned with what Go guarantees.

Go (`v3_server.go:139-151`): `LinearizableReadNotify` gives a read index ≥ every commit before the call. The member
waits until it has applied up to that index. Only then does `doSerialize` check auth at the member's current state,
and it fails with `ErrAuthOldRevision` if the auth revision moved during the call (`:1053`). A read-only `Txn` does
the same unless `IsTxnSerializable` (`txn.go:338`; an empty txn counts as serializable, as does the model's
`txnSerializable = all opIsSerGet []`). The drafts exclude serializable reads by premise.

`authFloorD` is the proven `authFloorAt` (`ReadOn.lean:437`: `srvRLogLb A`, `c ≤ ai0+|A|`, `i ≤ m`,
`authStateAt γa i (kvRaftOfOn … A).1`) with the raft log `A` (fillers included) replaced by the requested log
`L` and the read index `c` replaced by the caller's `L₀`. Each step is supported:
- `srvAuthAtLog Γ.kv srvAuthSt0 L = (kvRaftOfOn Γ.kv.c0 Γ.kv.ch0 (srvAuthSt0, Γ.kv.log0, []) L).1`, and
  `kvRaftOfOn_eqv` (`KVAuthModel.lean:2306`) equates it across `srvEqv A L`, given `c0 ≤ ai0`. `kvCongr`
  includes `c0`, `ch0` and `log0`, so the view's start values are the member's.
- `γ.raft.log` is the **committed** log (`srvLogCore` keeps `ownCommittedOps (opsOf (srvLE γ Lf))` with its
  authority). So the caller's `srvReqLogLb γR L₀` is committed before the call, and the in-process caller's
  `committedAtLeast γr c` (`etcdRangeSpecOnW`) can be built from it (as the barriers do with
  `committedAtLeast_of_rlog`). `authFloorAt`'s `A` extends that commit, so `L ⊒ L₀`.
- A lagging member at state index `j ≥ m ≥ i` checked at a state no older than the cluster's after `L ⊒ L₀`. That
  is what `rangeClassFrom`/`txnClassFrom` at `m` plus the floor say, and no more.

Retirement obligations: `srvReqLogLb L₀ ⊢ committedAtLeast (ai0+|A₀|)` (in the log invariant), `c0 ≤ ai0` per member.

**N1 (precision, not soundness):** `readAuthedD`'s `L` is only `L₀ <+: L`, with no `srvReqLogLb γR L`, and `rv` is
free, so the cluster-level claim admits any extension of `L₀`, including uncommitted ones. It is true whenever
Go succeeds (take the member's applied prefix), but it says little. Suggested fix: add `srvReqLogLb γR L` for
`readAuthedD`'s `L` inside `readCheckedD`, as `authFloorD` has.

## 3. New holes from the fixes: none found.

- `DistView.au` joins `etcdSvc`'s argument. Auth-off contracts and `Serve_dist` ignore it, and `ofKV`'s constant
  `au` fails the drafts' injectivity premise, so no existing fact becomes usable by a draft.
- Put, Delete, admin read no per-member name; their success is cluster-level, tied by `ρ.rd.kv.hist = Γ.kv.hist`.
- UserAdd's `□` update may be offered to several attempts; at most one applies a step (review B), so sound.
Not tried: the lease drafts (rows 11-14), the proven server model, building section 2's lemmas.
