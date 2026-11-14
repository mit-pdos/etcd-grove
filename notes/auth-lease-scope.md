# Scope: lease RBAC with auth on, end to end (`auth-on-leases`)

2026-11-14 · Scope agent for etcd-grove-81 · worktree `/shared/etcd-grove-scope-lease`, branch
`auth-lease-scope` (from lean `7c9a02aec4`) · notes only: no Lean edits, no builds. The goal was
approved by the user on 2026-11-14 as a next step. Go evidence was run at the etcd fork pin
`2eaeb872bc` (clone `/shared/tmp/auth-lease-scope/etcd`, `GOWORK=off`, 32G cap):
`notes/auth-lease-scope/zz_authlease_store_test.go` (copy into `server/auth`) and
`notes/auth-lease-scope/zz_authlease_rows_test.go` (copy into `tests/integration`). Both pass, the
integration tests 3 of 3 runs, together with etcd's own `TestV3AuthWithLease*` and
`TestPutWithLeaseInTXN` (§4).

## 0. Summary

- **Recommendation: a new closed theorem, `etcd_authlease_safe`**, one member with auth on and leases
  granted and revoked by request. Do not extend `etcd_auth_safe`/`etcd_auth3_safe`'s driver (§1).
- **What blocks it today** is one design choice made on 2026-10-28 (E3zb) and 2026-11-02 (the
  lease-grant plan's D1, question 2): **with auth on, the cluster grants no lease**. That coupling
  sits in four places:
  - the grant guard `srvGrantGuard lg on`, `False` when `on`;
  - the boot slot `lease.bootCfg`'s `on = true → m = .none`;
  - the built server's `lease.srvInvAt`, `□ (⌜on⌝ → srvLessorNil s)`;
  - the auth-on apply track, proved over `apply.lessorNil`/`lookupNil`, and the specs `apply`,
    `applyEntries` and `applyEntryNormal`, which take `srvLessorNilM E.authOn s`.

  Lifting it is the bulk of the work (S2 and S3). The rest is small: the posts (S1) and the
  example (S4).
- **The empty-user gap is a one-definition fix** (S1). `leaseCheckFrom` names its principal through
  `infoBoundM`, which with auth on also admits `info.Username = ""` unbound. The three check proofs
  already establish the stronger disjunct, `principalBound … (some info)`
  (`infoBoundM_of_ctxBound`, `ReqOn.lean:542`). The code refuses a token-less caller on every lease
  method, keyless leases included (E2).
- **The `TimeToLive` TOCTOU stays a margin in S1–S4.** A spec over the returned keys is false at the
  pin (`issues/etcd-lease-timetolive-keys-toctou.md`). It needs a fork fix and a stronger
  `EtcdServer.leaseTimeToLive` axiom post, which is trusted text: optional stage S6.
- **Lease expiry with auth on is left out of S1–S4.** A new coupling, "with auth on, no lease
  expires during the run", reuses the existing opaque deployment premise `lease.leasesNoExpiry`.
  The expiry path runs `authStore.WithRoot`, which mints a root token `<random prefix>.0` off the
  apply thread. Only the prefix's randomness keeps two such tokens apart, and a repeat panics (E7).
  Proving it needs a freshness assumption on `genTokenPrefix`, which is trusted text: optional
  stage S5.
- **Trusted text in S1–S4: none** (§3), apart from one docstring sentence of `NewLessor`'s axiom
  that becomes stale.
- **Estimate:** S1–S4 take 25 to 38 agent-days. S5 takes 5 to 8 more, S6 3 to 5 more, each after
  its trust decision (§5).

## 1. Goal

**In plain words.** With auth on, a principal can grant a lease only with a valid token. A principal
can revoke, renew, list, or read the keys of a lease only if it may write (revoke, renew) or read
(list, `TimeToLive` with keys) every key the lease holds when the server checks, or if it is an
admin. A put with a lease, at top level or inside a transaction, also needs write permission on every
key the lease already holds. These are the six lease rows of `notes/auth-matrix.md`. Today their
checks are proved at the method level. But no auth-on server result involves a lease, and no closed
theorem states a lease row.

**The closed theorem: `etcd_authlease_safe`** (`examples/etcd/authlease`). Every real execution of
`n` steps of `authlease`'s initialization followed by `Main()`, from a fresh state with one thread,
has no stuck thread, no thread ended in a panic, and a main-thread result, if any, of `Ok` or
`Failed`. Its hypotheses are `etcd_auth_safe`'s, including D22's `authSchemaSrv`, plus the
revocable lease mode's (`srvLevels`), `leasePeersOk` and `lease.leasesNoExpiry`, as
`etcd_leasegrant_safe` takes them.

`Main` starts one member with auth on, using the simple token provider. Through a root client it
sets up authkv's state (a root user, a role `r` with READWRITE on `[a, b)`, a user `u` with `r`, a
user `v` without it) and enables auth. Root grants lease `Lz` and puts `z` (outside `[a, b)`) with
it. `u` grants lease `Lu` and puts `a` with it. Then come these checks, each a panic if it fails:

1. **The token-less and invalid-token principals** (authkv's `anon` and `bad`): `Grant`,
   `Revoke(Lu)`, `TimeToLive(Lu)` with and without keys, `Leases` and one `KeepAlive(Lu)` are all
   refused. These are GHSA-q8m4's lease rows.
2. **`u` and leased puts**: `Put(a', WithLease(Lz))` and the same put inside a `Txn` are refused, and
   root's `Get(a')` then finds no such key. This is GHSA-x35m's lease half.
3. **`u` and revocation**: `Revoke(Lz)` is refused, and root's `Get(z)` still returns `z`.
4. **`u`'s reads of `Lz`**: `TimeToLive(Lz, WithAttachedKeys)`, `Leases` (while `Lz` holds `z`) and
   `KeepAlive(Lz)` are refused. This is GHSA-3p4g, within the checked-keys margin: the check is
   "refused if a key the server checked is unreadable", not "every key returned is readable".
5. **`v` against `Lu`**, whose key `a` `v` may not touch: as in 3 and 4.

A refusal is any error, as in authkv. Nothing requires an allowed call to succeed: that would be a
liveness claim. An allowed call's failure ends `Main` with `Failed`.

**Why a new theorem, not authkv's or auth3's driver extended:**
- `etcd_auth_safe` runs lease mode `none`. Leases need the revocable mode, so its `BootFacts` would
  change, and it would gain `leasesNoExpiry` and the revocable mode's premises: hypotheses added to
  an approved closed theorem.
- authkv's lemmas are being reused by auth3 A2 (`/shared/etcd-grove-auth3`) and adapted by k8s 7f
  (the watch files). A lease workload in the same proofs would serialize three lines of work.
- authkv's history check ("a key names its writer") does not hold under revocation: a revocation
  deletes keys other principals attached. The new driver states the lease facts as checks 2–5
  instead of a history.
- The new example reuses authkv's exported Go helpers (`SetUp`'s shape, principals, `newUserClient`)
  and, through its Lean results, authkv's start (`authkv_startServer` at the revocable mode).
  auth3's B can fold leases in later.

## 2. What changes

File references are to lean `7c9a02aec4`. "Draft" statements are sketches for the Draft stage, not
final Lean.

### 2.1 The empty-user gap: `leaseCheckFrom` (S1)

- `leaseCheckFrom` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseCheck.lean:102`) has
  `∃ info, infoBoundM E.authOn s E ctx info ∗ (adminVerdictFrom … ∨ K info)`. With auth on,
  `infoBoundM` (`ReqOn.lean:465`) is `⌜info.Username' = ""⌝ ∨ principalBound s M ctx (some info)`.
  So for an absent or keyless lease, where `K info` holds trivially, a proof can choose the empty
  user.
- The code refuses that: `checkLeaseRenew`, `checkLeaseTimeToLive` and `checkLeaseLeases` return
  `auth.ErrUserEmpty` for a `nil` auth info (`v3_server.go:585, 617, 764`), and E2 shows it for every
  lease method. The empty-user disjunct is `doSerialize`'s stand-in for a context without a user; the
  lease checks do not have one.
- **Draft:**

  ```lean
  def leaseCheckFrom (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface) (n : Nat)
      (K : AuthInfo → IProp GF) : IProp GF :=
    iprop(auth.enabledVerdictFrom E.authMode n false ∨
      ∃ info : AuthInfo, □ (⌜E.authOn = true⌝ → principalBound s E.authMode ctx (some info)) ∗
        (adminVerdictFrom E.authMode n info GoInterface.nil ∨ K info))
  ```

  The three check proofs stop at `infoBoundM_of_ctxBound` (`EtcdServer__checkLeaseRenew.lean:97`,
  `__checkLeaseLeases.lean:103`, `__checkLeaseTimeToLive.lean:108`). They take
  `principalBound_of_ctxBoundOrTLS` (the lemma's own last step) instead.
- **Its users** (no statement text changes, only the definition):
  - the three checks' specs, `EtcdServer.LeaseLeases.spec`, `LeaseRenew.spec` and
    `LeaseTimeToLive.spec`;
  - their proofs (`EtcdServer__LeaseLeases.lean`, `__LeaseRenew.lean`, `__LeaseTimeToLive.lean`);
  - v3rpc's `InvLeaseKeepAlive.lean` and `InvLeaseRead.lean`.

  `etc/importers.py --uses leaseCheckFrom` lists them.
- **What remains admitted, correctly:** a principal bound through the TLS fallback (`srvTLSId`). With
  `ClientCertAuthEnabled`, `AuthInfoFromTLS` makes the user the certificate's common name
  (`auth/store.go:1040-1043`), which may be empty. Then a keyless lease's renewal passes the code with
  `Username = ""`. `principalBound` covers that case, and the post stays true.
- `leaseCheckFrom` is part of the lease-keys plan's frozen Part B vocabulary
  (`notes/lease-keys-plan.md`, "Part B frozen"). The change needs a `notes/decisions.md` entry, and a
  ledger entry (`notes/specs-only/ledger.md`) before the edit.
- **Effect.** `LeaseLeases.spec`/`LeaseRenew.spec` say "authenticated" (a bound, non-nil auth info)
  on success with auth on, which GHSA-q8m4's unauthenticated `LeaseLeases`/`LeaseKeepAlive` violate. No other lease post needs
  `authedOutB`: `LeaseTimeToLive.spec` has it (`EtcdServer__LeaseTimeToLive.lean`, post).

### 2.2 The apply layer with a lessor, at the latest state (S2)

This is the lease-keys plan's Part A, ported from the class track (`chainLeaseClass`, `kvPost`) to
the latest-state track that the auth-on server uses (`kvPostFL`, `AuthApplyLatest*`). It is Q5's
option (a), deferred on 2026-10-31.

- `apply.checkLeasePuts.specNil` and `apply.lessorNil` (`apply/AuthApplyLatestPut.lean:30, 45`), and
  `apply.lookupNil` (`AuthApplyLatest.lean:122`), go. In their place:

  ```lean
  /-- the lease part of a check at the latest state: auth off; or the principal (non-empty) an admin
  at `hs`'s last state, with no revision check (`IsAdminPermitted`, `store.go:915-936`); or every key
  `I` attaches to `id` write-permitted there (`isOpPermitted`, revision checked) -/
  def apply.leasePassedL (on : auth.AuthMode) (hs : List auth.AuthState) (a : auth.AuthInfoM)
      (I : ItemMap) (id : w64) : Prop :=
    adminL on hs a ∨ passedL on hs a (leasePerms I id)
  def apply.leasePerms (I : ItemMap) (id : w64) : List Perm3 :=
    (lease.keysOf I id).map fun k => (k, [], .write)

  abbrev apply.checkLeasePuts.specL : Prop :=      -- one spec per function: replaces specNil
    ∀ st le RD on Lf hs (γl : GName) L I ai info dq id,
    {{ isPkgInit … ∗ apply.isAuthStoreL st RD on Lf ∗ txn.isTxnLessor le γl ∗
        lease.lessorUser γl L I ∗ ai ↦{dq} info ∗ RD ∗ Lf hs ∗ ⌜apply.shapedL on hs (leasePerms I id)⌝ }}
      checkLeasePuts st ai le id
    {{ err, RET err; lease.lessorUser γl L I ∗ ai ↦{dq} info ∗ RD ∗ Lf hs ∗ authApplyErrIs err ∗
        ⌜on.isOn = false → err = nil⌝ ∗ (∀ _ : err = nil, apply.leaseKeysClass on info I id) ∗
        ⌜(err = nil → leasePassedL on hs (authInfoM info) I id) ∧
         (err ≠ nil → ¬ leasePassedL on hs (authInfoM info) I id)⌝ }}
  ```

- `apply.checkPutAuth.specL` (`AuthApplyLatestPut.lean`, after `specNil`) takes
  `lessorUser γl L I` for `lookupNil le`. Its pass/refuse verdict becomes
  `passedL … (putPerms o) ∧ leasePassedL … I o.leaseID`. The order is `IsPutPermitted(key)`, then
  the lease's keys, then the `PrevKv` read (`apply/auth.go:73-94`).
- `apply.authApplierV3.Put.specL`, `Txn.specL` (`AuthApplyLatestTxn.lean:246-267`) and
  `checkTxnReqs_latest` drop `apply.lessorNil p`. They lend `kvOwn`'s `lessorUser` to the checks, as
  the class track's proofs do (`kvOwn_lend`). `Txn.specL`'s `opChecked (.put o) L` becomes
  `L = putPerms o` with the lease part `leasePassedL … I o.leaseID`.
- **New: `apply.authApplierV3.LeaseRevoke.specL`**, `checkLeasePuts` then the inner `LeaseRevoke`
  (`apply/auth.go:191-196`). Its outcome is decided at the latest state by `leasePassedL … I id`.
  - **Model detail (E5):** the admin shortcut does not check the header's revision, and a keyless
    lease passes for any principal, the empty header included (`checkLeasePutsKeys` calls no
    `IsPutPermitted`).
  - **No `LeaseGrant` check at apply:** `authApplierV3` overrides no `LeaseGrant`
    (`apply/auth.go:43-233`), so a grant is applied whatever its header.
- `apply.kvPostFL` (`AuthApplyLatest.lean:107`) gains `chainLeaseClass E.authMode info I c rq oc` at
  `I = mvcc.leaseItemsOf (mvcc.stateAfter log)`, as `kvPost`/`kvPostF` have
  (`Chain.lean:1082, 1615, 1629`).
- `DispatchKVL.lean:199-208`, `UberKVLBase.lean:61` and `Results.lean:1698-1725`
  (`apply_applier_kv_latest`, `server_uber_kvl`, `server_uber_kvl_on`) lose `lessorNil` and
  `srvLessorNil`.
- `reqLeaseClass` is carried through `uberApplier.dispatch`/`Apply` (`notes/auth-matrix.md:83-84`,
  "the dispatch does not carry it yet").
- **Callers:** the auth-on server's `srv_uberKVL_on` (`UberOn.lean`), and through it
  `applyEntryNormal.specOn` and `NewServer`'s auth-on construction (S3).

### 2.3 The auth-on server with leases: removing `srvLessorNil` (S3)

**The coupling, four places, all definitions in `Proof/` (no trusted text):**

| place | today | Draft |
|---|---|---|
| `srvGrantGuard lg on` (`InvApplier.lean:519`) | `⌜lg = true ∧ on = false⌝` | `⌜lg = true⌝` (`lookupNil_of_guard`, `UberOn.lean`, goes) |
| `lease.bootCfg lm m on` (`LeaseApi.lean:67`, sealed boot-hub slot) | `… ∧ (on = true → m = .none) ∧ …` | `… ∧ (on = true → m = .revocable → lease.leasesNoExpiry) ∧ …`; `bootCfg_auth` and `bootCfg_of_run`'s `hon` change with it |
| `lease.srvInvAt on s E m σ₀` (`LeaseApi.lean:132`) | first conjunct `□ (⌜on = true⌝ → srvLessorNil s)` | dropped; `srvInvAt_lessorNil`/`srvInv_lessorNil` go |
| `srvUberOn s` (`ServerOnDefs.lean:260`) | `∀ γc, srvLessorNil s -∗ ∃ stl, … ∗ apply.uberKVC …` | `∀ γc, ∃ stl, … ∗ apply.uberKVC …` (the KV contract's methods take the owner's lessor from `kvOwn`, as in mode off) |

**The specs that take the premise, restated without it** (proved internal specs, but exported in
`interface/`):
- `EtcdServer.apply.spec` (`Spec/…/EtcdServer__apply.lean:101`), `applyEntries.spec`
  (`__applyEntries.lean:81`), `applyEntryNormal.spec` (`__applyEntryNormal.lean:86`) and `specOn`
  (its `srvLessorNil s`) each drop `srvLessorNilM E.authOn s`;
- `srvLessorNil`/`srvLessorNilM` (`ServerOnDefs.lean:245`, `UberOn.lean:60`) go.

Their users: `EtcdServer__apply.lean:210, 1257`, `__applyEntryNormal.lean:2057, 2082`,
`__applyAll.lean:93`, `ModeSpecs.lean:135-610`, `AuthComp.lean:147-293`, `NewServer.lean:1906`,
`NewServerR.lean:1838`, `examples/etcd/auth/startServer.lean:153` and
`examples/etcd/auth3/startMember.lean:169`.

**The auth-on model gains the lease table** (`KVAuthModel.lean`):
- `kvEntryOn` (`:340`) runs `kvEntry c₀ ch [] s.2 m`, "at the empty lease table". It becomes a step
  on `auth.AuthState × mvcc.Log × LeaseTable`, as the off model's `kvEntrySt`
  (`KVModelDefs.lean:457`).
- The refusal test `isKVKind ∧ ¬ kvGranted s.1 rq` (`:220`, over `reqPerms`, `:195`) becomes
  `¬ kvGrantedL s.1 (leaseItemsOf (stateAfter s.2)) rq`:

  ```lean
  def kvGrantedL (st : auth.AuthState) (I : ItemMap) (rq : apply.IRRModel) : Prop :=
    kvGranted st rq ∧ leaseGrantedM st I rq
  def leaseGrantedM st I rq : Prop := match apply.dispatchKind rq with
    | .put => ∀ o, rq.put = some o → leaseOk st (apply.principalOf rq) I o.leaseID
    | .txn => ∀ t, rq.txnW = some t → ∀ o ∈ txn.putsW t, leaseOk st (apply.principalOf rq) I o.leaseID
    | .leaseRevoke => ∀ id, rq.leaseRevoke = some id → leaseOk st (apply.principalOf rq) I id
    | _ => True                                        -- a grant is not checked at apply
  def leaseOk st a I id : Prop := st.enabled = false ∨
    ((authInfoM a).user ≠ "" ∧ ∃ u, st.users !! (authInfoM a).user = some u ∧ auth.isRoot u) ∨
    ∀ k, I.lookup ⟨k⟩ = some id → kvGrantedPerm st a (k, [], .write)
  ```

  The admin disjunct has no revision condition (E5).
- `plainEntryOn` (`:647`) and `entryShapeOn` (`:711`) admit the proposers' lease kinds at the
  revocable mode: a put or transaction put with a lease, a grant (`grantKindOk`) and a revocation
  (`revokeKindOk`). `kvDet`/`kvShapeAll` cover the lease keys (point keys, the cache's shape).
- `kvInvOn` (`:900`) holds the model's lease table. `kvOwn`'s lease items are
  `leaseItemsOf (stateAfter log)`, as with auth off.
- `plainCover` (`KVModelDefs.lean:72`) and `rqOk` (`apply/Chain.lean:290`) already admit grants and
  revocations by mode. What is new is that the auth-on server reaches them.

**The entry points with auth on:**
- `srvGrantsLeases E ρ := ρ.rd.kv.lg = true` (`LeaseGrant.lean:43`, drops `E.authOn = false`);
  `srvRevokesLeases E ρ := ρ.rd.kv.lm = .revocable` (`RevokeCtx.lean:65`, the same).
- `EtcdServer.LeaseGrant.spec` (`Spec/…/EtcdServer__LeaseGrant.lean:64`) and `LeaseRevoke.spec`
  (`__LeaseRevoke.lean:52`), **Draft:**
  - `isServerReq s E ρ` becomes `isServerReqM E.authOn s E ρ`;
  - the success post gains `authedOutB s E.authMode (GoInterface.ok ctx) GoInterface.nil`
    (`requireAuthInfo`'s, `v3_server.go:447, 477`);
  - `LeaseRevoke`'s success post also gains `revokeGrantOn s E ctx id`: the revocation's entry was
    applied with `leaseOk` at the model's state for the stamped header, bound to the context. This
    is the shape of `Put.specOn`'s `writeGrantOn`.

  Callers: `v3rpc/ServerLeaseGrant.lean`, `ServerLeaseRevoke.lean`, v3rpc `Results.lean`, and
  `etcdstart/ServedLease.lean`'s `etcdLeaseServedAt` (its registrations take
  `v3rpc.etcdModelOfServer E γr false`, which becomes the mode, `E.authOn`). Behind them are the
  client's `etcdLeaseGrantSpecLive`/`etcdLeaseTTLSpecLive`/`etcdLeaseLeasesSpecLive`
  (`client/v3/InvLeaseGrant.lean:102-188`) and the revocation's and keep-alive's registrations.
- `EtcdServer.revokeExpiredLeases.spec` (`Spec/…/EtcdServer__revokeExpiredLeases.lean:51`) takes
  `lease.expiredLeases (srvGrantGuard E.lg E.authMode.isOn) ls`, whose guard used to imply auth off.
  It gains `⌜E.authOn = false⌝`. `run`'s expiry arm discharges that from the channel's payload,
  `¬ leasesNoExpiry` (`lessor__ExpiredLeasesC.lean:34`), and the new `bootCfg` row. So
  `WithRoot`'s auth-on branch stays unreached (S5 lifts this).
- `NewServer`'s auth-on construction (`NewServer.lean:1900-1912`, the `HLnil` block) and
  `NewServerR`'s (`:1832-1842`) lose the block. `etcdstart/newServerMode.lean:97`
  (`bootCfg_of_run … (fun h => absurd …)`) passes the new row.

### 2.4 The `TimeToLive` TOCTOU (issues/etcd-lease-timetolive-keys-toctou.md)

- **At the pin a spec over the returned keys is false.** The issue's test reproduces it on the leader
  and on a follower. The specs say so as their margin (`EtcdServer__LeaseTimeToLive.lean`,
  `__checkLeaseTimeToLive.lean`, `__LeaseRenew.lean`), and the issue is filed in `issues/` with
  `upstream: none`.
- **Recommendation for S1–S4: keep the margin.** Check 4 of the driver claims only what the spec
  gives. With one member and the keys of `Lz`/`Lu` fixed before the checks (no detach: the driver
  never deletes or re-puts `z` or `a`), "`u` may read every key of `Lz` at a lessor index `≥ m`"
  contradicts `z ∈ keys(Lz)` there. So a passing `TimeToLive(Lz, WithKeys)` panics in the model, and
  the theorem excludes it. Nothing claims "the returned keys are readable".
- **Optional S6 (trusted text, a hard stop):** a fork commit that runs `IsRangePermitted` on
  `resp.Keys` after `leaseTimeToLive` returns, as the issue's "Fix" proposes. Then:
  - `EtcdServer.leaseTimeToLive.wp_proof`'s post (an axiom, `Spec/…/EtcdServer__leaseTimeToLive.lean`)
    gains read ownership of `w.Keys'` and its byte slices. Today it states none, so the fixed loop
    could not read them.
  - `LeaseTimeToLive.spec`'s verdict moves to `[∗list] k ∈ w.Keys', permVerdictFrom … .read`.
  - `LeaseTTLRespM`/`etcdLeaseTTLSpecLive` gain the keys.

  `LeaseRenew` has the same shape (`nonissues/etcd-lease-renew-keys-follower-lag.md`), with a
  different fix: run the check on the leader. Recommend asking the user first whether to file the
  issue upstream (it is not filed), and doing the fork fix after upstream's answer.

### 2.5 Lease expiry with auth on (optional S5)

- With auth on, the leader's expiry loop revokes through `s.LeaseRevoke(s.authStore.WithRoot(s.ctx), …)`
  (`server.go:881`).
- `WithRoot` (`auth/store.go:1175-1213`) draws a random prefix and assigns `"<prefix>.0"` to `root`
  in the provider's map, off the apply thread. A token assigned twice panics
  (`simple_token.go:132-139`). E7 shows the shape, a fresh prefix per call, and the panic on a repeat.
- `auth.authStore.WithRoot.spec` is proved in mode `off` only (its docstring, "two departures"). The
  auth-on branch needs the right to issue `<prefix>.0` (`tokFresh`, `auth/Tokens.lean:107`).
  - The `Authenticate` path gets that right from the entry's index.
  - For the root token only the prefix's randomness separates two calls. So a proof needs
    `genTokenPrefix` (an axiom, `Proof/…/auth/tokenSimple__genTokenPrefix.lean:23`) to return a
    prefix never returned before, or an extension in the style of `idIssueExt`.
  - Either way it is trusted text, and a claim about randomness: the user's decision.

## 3. Trusted text touched

- **S1–S4: none.**
  - `lease.NewLessor.wp_proof`'s text takes the guard `GA` as a parameter, unchanged. It is
    instantiated at `srvGrantGuard lg on`, now `lg` alone. It was already used at `lg = true` with
    auth off, so no new trust.
  - Its docstring's sentence "a server whose guard is `False` … finds no lease (`lookupNil_of_guard`)"
    (`Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean:198-201`) goes stale and should be
    corrected. That is a docstring edit in a trust-boundary file: flagged for the coordinator, no
    meaning change.
  - `lease.leasesNoExpiry` (opaque, `lease/LessorBackend.lean:77`) is reused unchanged, as a
    hypothesis of the new closed theorem only (as `etcd_leasegrant_safe`'s `Hlne`).
  - `etc/tcb-baseline.txt` is unchanged. A new collection, `etc/tcb-collections/authlease.txt`.
- **S5:** `genTokenPrefix`'s freshness, or a new extension (§2.5).
- **S6:** `EtcdServer.leaseTimeToLive.wp_proof`'s post (§2.4), plus a fork commit.
- **Hub:** `lease.bootCfg` is a boot-hub slot (`LeaseApi.lean` header). Its body change is a hub
  change, a request to the coordinator.
- **Frozen statements:** `leaseCheckFrom` (Part B, frozen 2026-10-31). The lease-keys plan's Part A
  statements are not touched: the class track stays, and S2 adds the latest track's.

## 4. Go evidence at the pin (`2eaeb872bc`)

Code citations are to the pin (`git show 2eaeb872bc:<path>`; `.lake/go-src/etcd` is at `249d76be`,
not at the pin). Tests: `notes/auth-lease-scope/zz_authlease_rows_test.go` (`TestAuthLeaseScopeRows`,
`TestAuthLeaseScopeExpiry`) and `zz_authlease_store_test.go` (`TestAuthLeaseScopeAdminIgnoresRevision`,
`TestAuthLeaseScopeWithRootToken`). All pass, the integration tests 3 of 3 runs together with
etcd's `TestV3AuthWithLease*` and `TestPutWithLeaseInTXN`.

| # | claim the plan rests on | code | test |
|---|---|---|---|
| E1 | `LeaseGrant` needs a token; any authenticated user may grant | `v3_server.go:434-456` (`requireAuthInfo` at 447); no `LeaseGrant` in `authApplierV3` (`apply/auth.go:43-233`) | Rows: anon refused "user name is empty", `u` granted |
| E2 | the token-less principal is refused by every lease method, keyless leases included (the code is stronger than `LeaseLeases`/`LeaseRenew`'s posts: §2.1) | `requireAuthInfo` `:1277-1291`; `checkLeaseRenew` `:585`, `checkLeaseTimeToLive` `:617`, `checkLeaseLeases` `:764` | Rows: anon `Leases`, `KeepAliveOnce`, `TimeToLive` (with and without keys), `Revoke` of a keyless lease, each "user name is empty" |
| E3 | a keyless lease: any authenticated user may renew, read with keys and revoke it (no key to check) | `checkLeasePutsKeys` `apply/auth.go:207-220`; the API checks' loops | Rows: `u` on root's keyless lease |
| E4 | a lease holding a key `u` may not write or read: `u`'s leased put (also in a `Txn`), `TimeToLive` with keys, `Leases`, `KeepAlive` and `Revoke` are refused; `TimeToLive` without keys passes (authenticated only); root's `Leases` passes | `checkPutAuth` `apply/auth.go:73-94`, `checkTxnReqsPermission`; `LeaseTimeToLive` `:698-722`; `checkLeaseLeases` `:751-786`; `checkLeaseRenew` `:574-605`; `authApplierV3.LeaseRevoke` `:191-196` | Rows |
| E5 | `IsAdminPermitted` ignores the auth info's revision, `isOpPermitted` checks it: at apply, root with a stale header revision passes `checkLeasePuts`' admin shortcut (`leaseOk`'s admin disjunct); the empty header fails both | `auth/store.go:915-936`, `:862-901` | Store: `IsAdminPermitted(root, rev 1)` nil, `IsPutPermitted(root, rev 1)` `ErrAuthOldRevision`, empty info `ErrUserEmpty` for both |
| E6 | a revocation deletes the lease's keys, after only `checkLeasePuts` at apply | `apply/auth.go:191-196`, `backend.go`'s `LeaseRevoke` | Rows: `u` revokes its lease, `Get(a)` empty |
| E7 | with auth on, expiry revokes through `WithRoot`'s root token `<16 letters>.0`, minted off the apply thread; each call draws a new prefix; assigning a token twice panics | `server.go:855-900` (881), `auth/store.go:1175-1213`, `simple_token.go:110-144, 212-224` | Expiry: an expired lease's key deleted with auth on. Store: the token's shape, `AuthInfoFromCtx` gives root, two calls differ, a repeat `assign` panics |
| E8 | the TLS fallback can give a non-nil auth info with an empty user (the case `principalBound`'s `srvTLSId` keeps) | `v3_server.go:1206-1216`, `auth/store.go:1036-1043` | code reading only (no client certificate set up) |
| E9 | the TOCTOU (keys checked are not the keys returned) | `v3_server.go:698-722`, `:636-696` | `issues/etcd-lease-timetolive-keys-toctou/` (reproduced 2026-11-02) |

## 5. Stages, hard stops, estimates

**S0: probe (1 day; Lean in an unlinked scratch file, not landed).**
- `checkLeasePuts.specL` over `lessorUser` against the real store's `isAuthStoreL`: does the
  latest-state contract give `IsAdminPermitted` at the latest state, with no revision?
- `Put.specL`'s proof with `kvOwn_lend` in place of `lessorNil`.
- `kvEntryOn` on the triple state, with the statements of `kvRaftOfOn_append`/`_ops` elaborated.
- The list of `bootCfg_auth`/`srvInv_lessorNil` consumers (§2.3) checked with `etc/importers.py`.
- **CP0:** the findings.

**S1: the empty-user fix (1 to 2 days).** The ledger entry, the `decisions.md` entry (Part B frozen
vocabulary), `leaseCheckFrom` (§2.1), the three proofs, the interfaces. **Hard stop:** the frozen
definition's change, before the edit.

**S2: the apply layer at the latest state with a lessor (5 to 8 days).** Draft (§2.2), Review,
Freeze, Prove. **Hard stops:** the Freeze package. `kvPostFL` and `apply_txn_latest` are
`Results.lean` exports, so their statements change.

**S3: the auth-on server with leases (10 to 15 days).**
- The model (§2.3), the four couplings, the apply specs without `srvLessorNilM`, `NewServer`/
  `NewServerR`, `LeaseGrant`/`LeaseRevoke` with auth on, `revokeExpiredLeases`' premise, and the
  served registrations at the mode.
- authkv and auth3 adapt mechanically: `startServer.lean`, `startMember.lean`.
- **Hard stops:** the Freeze package (exported: `NewServer.specG`'s slots, the apply specs, the
  lease entry points); the hub slot `bootCfg`; the `NewLessor` docstring edit.

**S4: the example and `etcd_authlease_safe` (8 to 12 days).**
- Go `examples/etcd/authlease/authlease.go` (about 250 lines) and its test, run 20 times; goose;
  `gen-init`.
- The client's lease calls at auth on (`Grant`, `Revoke`, `TimeToLive`, `Leases`, `KeepAlive` over
  the wire's refusals), `Main`, adequacy, and the collection.
- A requirement snippet for `examples/specreq/` (lease RBAC refusals), so the spec plan's lease specs
  are judged against it.
- **Hard stops:** the theorem's statement (CP4); the landing.

**S5 (optional, later):** expiry with auth on (5 to 8 days). Needs the trust decision of §2.5.

**S6 (optional, later):** the TOCTOU fix (3 to 5 days). Needs the user's filing decision, a fork
commit and the axiom post of §2.4.

**Total S0–S4:** 25 to 38 agent-days. The S3 range is the widest: the auth-on model's lemmas
(`KVAuthModel.lean` is 1405 lines) all take the third component.

**Decisions needed:**
- **Q1, the theorem.** A new `etcd_authlease_safe` (recommended, §1), or authkv's driver extended
  with lease workloads per principal.
- **Q2, expiry.** S1–S4 with "auth on implies no lease expires during the run" (`lease.leasesNoExpiry`
  reused, revocation by request only), recommended. Or include expiry now, with S5's trust decision
  first.
- **Q3, the empty user.** Change the frozen `leaseCheckFrom` as in §2.1: recommended. The TLS-fallback
  empty common name stays admitted, as the code admits it.
- **Q4, the TOCTOU.** Keep the margin in S1–S4 (recommended). The user decides whether to file the
  issue upstream, and S6 comes after that.
- **Q5, the latest track's lease class.** Put `chainLeaseClass` into `kvPostFL` (the lease-keys plan's
  Q5 option (a), deferred then): recommended, as it is what carries the class to the auth-on server.
- **Q6, scope against `grpc-auth-matrix-theorem`.** This Scope takes the lease rows only (GHSA-q8m4's
  lease part). Registration of Compact, Maintenance and Cluster stays with that proposal or the guard
  Scope.
- **Q7, the hub request.** The `lease.bootCfg` body change (§2.3) goes to the coordinator as a hub
  change.

## 6. Overlap with ongoing work

| work | its files | shared with this Scope | order |
|---|---|---|---|
| **restart S7** (`/shared/etcd-grove-rs56`, `restart-s7`; S7.4 `BuildServer.specRestart` next) | `NewServer.lean`, `NewServerR.lean`, `LeaseApi.lean` (`srvLeaseRd` laws at `lease.srvInvAt`, S7.2'), `etcdstart/{Defs,Restart,newServerMode,Served,ServedLease}.lean` | **S3:** `LeaseApi.lean` (`srvInvAt`, `bootCfg`), `NewServer.lean:1900-1912`, `NewServerR.lean:1832-1842`, `etcdstart/newServerMode.lean:97`, `ServedLease.lean` (the registrations' mode) | S3 after S7 lands; S1, S2 independent |
| **k8s 7f-5** (`/shared/etcd-grove-k8s7f`) | the k8s etcd3 store; v3rpc watch (`recvLoop`, `sendLoop`, `WatchApi`); authkv's watch proofs adapted | none in S1–S3; S3's authkv adaptation (`startServer.lean`) is a different file from 7f's | independent |
| **http-boundary-fix** (`/shared/etcd-grove-auth3`) | `net/http`, `rafthttp`; through `srvPeerRt`/`RenewHTTP`, `http.netCtxOk(C)` in the lease specs | `EtcdServer__LeaseRenew.lean`, `__LeaseTimeToLive.lean` (S1 re-checks the proofs, no statement change); S6's `leaseTimeToLive` axiom | S1 rebases mechanically; S6 after it |
| **auth3 A2** (in the same worktree after the fix) | `examples/etcd/auth3/*` | S3: `auth3/startMember.lean:169` (`srvLessorNil`) | mechanical, whichever lands second |
| **auth-guard-completeness** (`/shared/etcd-grove-scope-guard`, Scope, nothing written yet) | the guard specs: `AuthGuard.lean`, `AuthBound.lean` (`authedOutB`, `principalBound`), `v3rpc/InvAuthAdmin.lean`, `EtcdServer__requireAuthInfo`, the guarded entry points | **both would touch:** `AuthBound.lean` (S1 uses `principalBound`, no change to it planned); `ReqOn.lean` (`infoBoundM`); `LeaseCheck.lean`; the specs `EtcdServer__LeaseGrant`, `__LeaseRevoke`, `__LeaseLeases`, `__LeaseRenew`, `__requireAuthInfo` if the guard Scope also takes GHSA-q8m4's lease rows | proposal: the lease rows and `LeaseCheck.lean` are this Scope's; the guard Scope keeps the `authedOutB`/`principalBound` definitions unchanged, or tells this one first |

Not in conflict: D22 (`authSchemaSrv`, the same hypothesis), out_size C2 and the WAL/crash ladder
(collections only).
