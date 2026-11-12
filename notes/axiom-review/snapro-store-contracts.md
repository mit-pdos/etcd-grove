# The store contracts restated in `SnapRO.lean` (`NewAlarmStore`, `NewAuthStore`, `NewLessor`, `AlarmStore.restore`): survive

**Reviewed** 2026-11-06, at `mvcc-api` `b4bc6a538c` (etcd fork `ce3dbc097f`; go1.27.3), by the
`axiom` skill. No branch (no commit, no `lake`, as asked). The commits: `ccbb723710` (the components'
contracts at the backend `B`'s batch lock and its `bkWT`/`bkRT`, in place of mvcc's
`storeWT`/`storeRT`), `726ac24773` (the stores' contracts at `BkRef`, `srvBkTie d`, `fun _ => Pk`),
`9d274ffee8` (`BkRef` → `mvcc.KBReal`), `1b56c352f8` (the lessor's `T`/`R`: reviewed separately,
[lease-newlessor-wbtok](lease-newlessor-wbtok.md)). Compared against `lean`'s `11c367d87b`.

## The axioms and what changed

The trust-boundary axioms whose conclusions are these contracts:

| axiom | its conclusion here |
|---|---|
| `v3alarm.NewAlarmStore.wp_proof` | `alarmApplyOk a` (`SnapRO.lean:88`) |
| `auth.NewAuthStore.wp_proof` | `authApplyOk stl RD` (`:110`, = `authApplyOkM .off`), `authRecoverOk stl` (`:278`) |
| `lease.NewLessor.wp_proof` | `lessorApplyOk lp` (`:134`) |
| `v3alarm.AlarmStore.restore.wp_proof` | none of them (its spec, `Spec/.../v3alarm/AlarmStore__restore.lean`, is over any `γB`, `P`; unchanged by these commits); it reaches them through `EtcdServer.restoreAlarms` (proved) and `AlarmStore.Recover` (proved), which give `alarmApplyOk` from `NewAlarmStore`'s |

On `lean` each contract was `∀ (d : mvcc.KBReal) W Pk (γ : mvcc.StoreNames) f RW, ⌜γ.kb = some d⌝ -∗
isBackend d.γB d.P W Pk d.be -∗ plHookRO d.γB f -∗ ⌜f ≠ nil⌝ -∗ rwLens RW (… d.be) -∗
apply.isAlarmStore a γ Pk #f RW` (and the same for auth, the lessor with `mvcc.bkRTx`), the store's
clauses (`apply/Contracts.lean`) at `mvcc.csContract Pk #f`, `mvcc.storeWT γ`, `mvcc.storeRT γ`. Now:
no `γ`; `apply.isAlarmStore a (fun _ => Pk) f (srvBkTie d) RW`, each clause `∀ B : KBReal` with
`BT B = srvBkTie d B = ⌜B = d⌝`, at `csContractA (Pk B) f`, `bkWT B`, `bkRT B`.

## Verdict: survive

Instance by instance, each restated contract is the old one: the restatement is a re-encoding, not
a new claim. And the old claims are true of the Go code (checked again below). No counterexample.

### The re-encoding

- `γ` occurred only through `γ.kb = some d`: `kbWT (some d) = backend.wbTok d.γB = bkWT d`;
  `kbRT (some d) = rdTok d.γB d.P d.be ∗ bOpen d.γB rdOpen = bkRT d` (`InvStore.lean` at
  `11c367d87b`, `:1694-1704`; `Contracts.lean:128-133`); `mvcc.bkRTx` is the same pair.
- `BT B = ⌜B = d⌝` and `Pk B = Pk`: the `∀ B` collapses to `B = d`.
- `csContractA P f Pre Q Post = Pre ∗ hookRun P f Pre Q ∗ (Q ={⊤}=∗ P ∗ Post)`
  (`lease/MvccShapes.lean:89`) and, at `f ≠ nil` (a premise of every contract),
  `hookRun P f Pre Q = □ {{ P ∗ Pre }} f() {{ Q }}` (`Spec/.../mvcc/Api.lean:331`): `mvcc.csContract
  P #f`. The `nil` arm (a view shift in place of the hook) is unreachable here.
- `BkRef` (`726ac24773`) → `KBReal` (`9d274ffee8`): `d : KBReal` has `d.P := KBReal.P d` (fixed
  hook/safe-range/tracked rows, `InvStore.lean:105-111`), as on `lean`; the `BkRef` interlude (any
  `P`) never reached `lean`. The extra fields (`gx`, `cm`, `hookMax`, `limit`, `BT`) occur in the
  contracts only through `d.P` and `srvBkTie d` (equality), never in a resource the contract
  hands out. So `∀ d : KBReal` is the same set of instances as before.
- `authRecoverOk`: `dn : BkRef` → `dn : KBReal`, `.b` → `.be`, the triple unchanged.

### The claims against the Go code

- **Alarm** (`server/etcdserver/api/v3alarm/alarms.go`, `storage/schema/alarm.go`): `Get` reads the
  map under `a.mu`, returns a slice. `Activate` (`a.mu`; an alarm already set returns without a
  write, `Pre` back, the `wbTok` not returned: over-charged, sound) calls `MustPutAlarm`:
  `BatchTx()`, `LockInsideApply` (the hook `f` under `Pk`), `proto.Marshal(AlarmMember)` (no
  error), `UnsafePut(Alarm, v, nil)`: the key non-empty at `at ≠ NONE` (the premise,
  `nonissues/etcd-alarm-activate-none-zero-fatal.md`), far below `MaxKeySize`, a `nil` value; the
  `alarm` bucket exists: `RW` lends `srvRestRW d.γB = ∃ r, rbOwn d.γB r ∗ ⌜restPresent r⌝`, so the
  tracked rest buckets, `alarm` among them, are present (`InvRest.lean:479`). `Deactivate` likewise
  with `UnsafeDelete`. `RW` also lends `alarmBeOn a d.be` (half of `a.be`), which pins the write to
  `d`: `a.be` changes only under `a.mu` in `Recover`, which needs that half.
- **Auth**: the same shape for every write request (`authReqContract(N)`, `AuthEnable`,
  `AuthDisable`, `Authenticate`), the clauses' pre and post term for term the old ones with
  `storeWT γ`/`storeRT γ` replaced (attack 1); the store's code was reviewed in
  [auth-newauthstore-bkref](auth-newauthstore-bkref.md) and `notes/audit.md`'s `NewAuthStore` row.
  `authRecoverOk`: `Recover` (`server/auth/store.go:399-418`) sets `as.be` under `as.beMu` and reads
  the auth buckets through one read transaction (at `authBoot`/empty users:
  `refreshRangePermCache` over no user), then sets `enabled`.
- **Lessor**: [lease-newlessor-wbtok](lease-newlessor-wbtok.md).
- **`AlarmStore.restore`**: over an empty or absent alarm bucket, tracked (`P.RB "alarm"`) and in the
  table: `CreateAlarmBucket` (one write-back), `GetAllAlarms` through one read transaction (the
  pooled slot) finds nothing, `ForceCommit` (no write-back); no error, the map unchanged. Unchanged
  by these commits; its round-4 premise `P.RB` is still there.

## Attacks tried

1. **A clause stronger than before.** Diffed `apply/Contracts.lean` (`11c367d87b..HEAD`) clause by
   clause for `isAlarmStore`, `isAuthStore`, `authReqContract(N)`, `isApplyLessor`: every write
   clause takes `csContractA (Pk B) f … ∗ bkWT B ∗ bkRT B ∗ BT B ∗ RW` where it took `csContract P f …
   ∗ storeWT γ ∗ storeRT γ ∗ RW`, and gives `bkRT B ∗ BT B` where it gave `storeRT γ`; nothing else.
   (`isApplyLessor`'s `Revoke` clause did change, `80f9b8e6b4`, but it is derived from the proved
   `lessor.Revoke.spec`, not an axiom's conclusion; `Grant`/`Checkpoint` now give `RW` back: the
   lessor review.)
2. **A backend the store is not on.** Each contract takes `rwLens RW (… ∗ xBeOn x d.be)`, the user's
   half of the store's backend field, so `d.be` is the store's current backend; a closed backend
   is excluded by `bkRT`'s `bOpen` share. As before.
3. **Two `KBReal`s for one backend.** A client could only exploit a second record `d'` with
   `d'.be = d.be` if it had `isBackend d'.γB d'.P …` at it, which only the backend's constructors
   give, once per `*backend`; `srvBkTie` is equality, so no record mixes two backends' tokens.
4. **The hook.** `f ≠ nil` and `plHookRO d.γB f`: Go's `LockInsideApply` runs exactly the frozen
   hook, whose triple from `Pk ∗ Pre` the client supplies; the contract consumes the client's view
   shift `Q ={⊤}=∗ Pk ∗ Post` once, at the lock.
5. **A write without the batch lock, a double write-back.** Every write clause takes one `bkWT B`
   (consumed) and goes through `LockInsideApply`/`Unlock` in Go; the contracts expose no lock token
   to the client (`isAlarmStore`/`isAuthStore` are whole-method triples). Blocked.

## Not tried

`clusterApplyOk` (`SnapRO.lean:251`, the same re-encoding; not one of these axioms' conclusions);
the auth store's read clauses (`RD`, unchanged); a Go run (none of the attacks reached a Go
behaviour that differs from the claim, so there was no program to run).
