# auth-lease S4 item 4: the Freeze package (rev 2, 2026-11-16; L1 open, §8; rev 2's texts §9)

For etcd-grove-02. Branch `auth-lease-s4`. Draft `notes/auth-lease-s4-draft.md` §3 lists the exported
texts S4 changes; C5′'s (item 3) and etcdstart's (item 2) are already in the tree. This file gives the
rest as exact Lean text, old → new, with the Go behaviour each claims and the callers it reaches.

**Type-checked:** every new text is in `Scratch/S4Freeze.lean` (untracked; copy
`/shared/tmp/auth-lease-s4/S4Freeze.lean`) under a `…N`/`…_stmt` name beside the old one; theorem
statements are `Prop` definitions, so the probe holds no proof and no `sorry`.
`LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json etc/lean-check.py -a Scratch/S4Freeze.lean`: 0 errors.

**Trusted text: none new.** Every text below is the spec of proved code or a proved law. No axiom
changes. §4.4 strengthens two frozen `Spec/` posts of proved functions.

## 0. Where this departs from Draft §3

| # | Draft §3 row | here | why |
|---|---|---|---|
| D-a | `etcdPutSpecOn`: no lease filter | `⌜o.leaseID = 0 ∨ ρ.kv.lm = .revocable⌝` | the server admits a leased put only at the revocable lease mode (`putPermitOn`, S3b, `ReqOn.lean:936`); with no filter the served result `etcd_kv_auth_served_on` is unprovable at modes `none`/`mono` |
| D-b | `etcdPutSpecM on`: `⌜on = false → o.leaseID = 0⌝` | `⌜o.leaseID = 0 ∨ (on = true ∧ ρ.kv.lm = .revocable)⌝` | as D-a |
| D-c | `etcdTxnSpecOn`: S3b's leased form | `txn.txnPlain t ∨ (ρ.kv.lm = .revocable ∧ txnPlainL t)` | `txnPermitOn`'s condition (S3b, `ReqOn.lean:1345`) |
| D-d | `kv.Put.spec`: drop `leaseID = 0` | **no change** | `kv.Put.spec` is over `isKv`, whose members register the auth-off `etcdPutSpec` (lease `0`). Dropping the premise is unprovable. The auth-on leased put goes through `kv.Put.specG` (`KVMembers.lean:209`), which has no lease premise |
| D-e | new `isEtcdLeaseOn` + `client_lessor_isEtcdLeaseOn_served` | new results `client_lease_grant_on`, `client_lease_revoke_on` on the concrete `*lessor` (§3) | an interface bundle is for a client that does not know the concrete type ("Canonical specs are per (concrete type, method)"). The driver holds `isNewClient`'s `lessorAt lp eps`, the concrete `*lessor`. These are the siblings of `client_put_on` |
| D-f | (not in §3) | **§4.4: `EtcdServer.LeaseTimeToLive.spec`/`LeaseLeases.spec` posts strengthened**, plus v3rpc's `leaseTTLOut`/`leaseLeasesOut` | without it a refused `TimeToLive`/`Leases` cannot be told from a successful one (finding F4 below) |
| D-g | per-member law `lessor_keys_of_read` | exact statement §5, with new pure vocabulary | |

## 1. The KV specs' lease filters (client/v3 `KVServiceOn.lean`)

**Go.** `kvServer.Put` (`v3rpc/key.go`) checks the request (`checkPutRequest`: key not empty, …) and
calls `EtcdServer.Put`. A leased put is proposed and applied. With auth on, `applierV3backend.Put`
checks that the lease exists (`ErrLeaseNotFound` otherwise). The auth layer requires write permission on
the key (`checkPutAuth`). For the leased puts' at-apply check of "write on every key the lease holds",
see `notes/auth-matrix.md`. `Txn` is the same at each put (`checkTxnReqsPermission`, `applyTxn` → `put`).
The server spec (`EtcdServer.Put.spec`, frozen since S3b D3) admits `putPermitM E.authOn …`, whose
on-arm is `putPermitOn`: `op.leaseID = 0 ∨ γk.lm = .revocable`.

### 1.1 `etcdPutSpecOn` (`KVServiceOn.lean:50`)

```lean
-- old
      ∃ Q : KVState → IProp GF, ⌜o.leaseID = W64 0⌝ ∗
-- new
      ∃ Q : KVState → IProp GF, ⌜o.leaseID = W64 0 ∨ ρ.kv.lm = .revocable⌝ ∗
```
The docstring gains: "a put's lease `0`, or any lease at the revocable lease mode (the server's
`putPermitOn`, auth-lease S3b; a missing lease is the server's `ErrLeaseNotFound`, an error)". The reply
needs no change. `putReplied` already carries `∃ lt, ⌜E.authOn = false ∨ γr.kv.lm = .none → lt = []⌝ ∗
Q (kvStateOf x.log lt)` (S3a), and `EtcdServer.Put.spec` gives it.

### 1.2 `etcdPutSpecM` (`KVServiceOn.lean:331`)

```lean
-- old
      ∃ Q : KVState → IProp GF, ⌜o.leaseID = W64 0⌝ ∗
-- new
      ∃ Q : KVState → IProp GF, ⌜o.leaseID = W64 0 ∨ (on = true ∧ ρ.kv.lm = .revocable)⌝ ∗
```
**Variance (the free mode).** The filter is the caller's premise. `etcdPutSpecM_true : etcdPutSpecOn ⊢
etcdPutSpecM true` keeps holding, because the two filters are equal at `true`. `etcdPutSpecM_false :
etcdPutSpec … ⊢ etcdPutSpecM false` also keeps holding: at `false` the new filter is `o.leaseID = 0`,
the old one. So the registration's direction (`isGrpcRpcMd_mono`) is unchanged at both literals.

### 1.3 `etcdTxnSpecOn` (`KVServiceOn.lean:307`), write branch

```lean
-- old
        (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t ∧ txnNestOk t⌝ ∗
-- new
        (⌜txn.txnReadonly t = false ∧ (txn.txnPlain t ∨ (ρ.kv.lm = .revocable ∧ txnPlainL t)) ∧
            txnNoZeroEnd t ∧ txnNestOk t⌝ ∗
```
`txnPlainL t = txn.txnLeased t` (`KVAuthModel.lean:789`) is plain but for the puts' leases: gets at
revision 0, no `IgnoreLease`, a put's lease free. Its reply is `txnReplied`, whose writing arm
`txnAppliedOk` covers a leased transaction since S3b D7.

### 1.4 `etcdTxnSpecM` (`KVServiceOn.lean:374`), write branch

```lean
-- new
        (⌜txn.txnReadonly t = false ∧
            (txn.txnPlain t ∨ (on = true ∧ ρ.kv.lm = .revocable ∧ txnPlainL t)) ∧
            txnNoZeroEnd t ∧ txnNestOk t⌝ ∗
```
The variance is as in §1.2: at `false` the condition is `txnPlain t`, the old one.

### 1.5 What else moves (internal; item 5's forms)

- **v3rpc `kvDepPre`** (`ServerKV.lean:317`) has the put row `o.leaseID = W64 0` and the txn row
  `txn.txnPlain t`. `kvDepPreOn`/`kvDepPreM` are `kvDepPre ∧ shape`. They take the lease mode: the
  put row becomes `o.leaseID = 0 ∨ (on = true ∧ lm = .revocable)` and the txn row likewise. `srvKVAnsOn`'s
  `pre` is the field the exported `etcd_kv_auth_served_on` premise `v3rpc.kvServerAt p s (srvKVAnsOn …)`
  carries. The premise's text is unchanged, but its meaning is stronger: the handler serves more
  requests. Its producers are etcdstart's `grpcUpOn` and authN/auth3/authkv's starts. They re-prove it
  from the kvServer handlers, whose proofs widen with `EtcdServer.Put/Txn.spec` (already widened, S3b).
- The off texts (`etcdPutSpec`, `etcdTxnSpec`, `kvDepPre` at `on = false`) are unchanged in meaning.
- `kv.Put.spec`, `kv.Do.spec`'s `doRunOk`, `kv.Put.specM`/`doRunM`: unchanged (D-d).

**Callers.** `etcdPutSpecOn`/`etcdTxnSpecOn` are registered by `etcd_kv_auth_served_on`
(`AuthnServedOn.lean:307`) and consumed by `client_put_on`, `client_txn_on` (`ResultsOn.lean`) and the
authkv/auth3/authN clients (`etcd_auth.client_Put_on…`). Each consumer discharges the filter with
`Or.inl rfl` (lease `0`). Only the S4 driver's leased put uses the right disjunct, at `hlm : ρ.kv.lm =
.revocable` from `memberBootOn … .revocable` (item 2).

## 2. The lease client's specs at the metadata form (`Spec/…/client/v3/`)

**Go** (`client/v3/lease.go`, `retry.go`). `lessor.Grant`/`Revoke`/`TimeToLive`/`Leases` call
`l.remote.LeaseX(ctx, req, l.callOpts...)`. `retryLeaseClient.LeaseX` appends
`withRetryPolicy(repeatable)`. The interceptor sends each attempt with the context's outgoing
metadata, which carries the client's token after `Authenticate`. This is the same transport as
`retryKVClient.Put`, whose spec already takes `GrpcSpecMd`.

### 2.1 New definition `lessorRemoteAtC l conn addr` (client/v3 `InvLease.lean`)

This is `lessorRemoteAt` with its connection named, as `kvObjAtC` is for `kvObjAt`. Text: probe
§2.1. Law (form): `lessorRemoteAt l addr ⊣⊢ ∃ conn, lessorRemoteAtC l conn addr`.

### 2.2 `lessor.{Grant,Revoke,TimeToLive,Leases}.spec`

Diff, shown for Grant. The other three follow the same pattern; their full texts are probe §2.2:
```lean
-- old
  ∀ (l : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse) …,
  {{ … ∗ lessorRemoteAt l addr ∗
      isGrpcRpcs addr go!"/etcdserverpb.Lease/LeaseGrant" Spec ∗ □ ▷ Spec (ttl, W64 0) Q ∗ … }}
-- new
  ∀ (l conn : Loc) (addr : List GoString)
    (Spec : GrpcSpecMd (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse) …,
  {{ … ∗ lessorRemoteAtC l conn addr ∗
      isGrpcRpcsMd addr go!"/etcdserverpb.Lease/LeaseGrant" Spec ∗
      □ ▷ attemptPre conn (GoInterface.ok ctx) Spec (ttl, W64 0) Q ∗ … }}
```
The posts are unchanged. The precondition stays persistent (`□`), because the policy is repeatable:
an attempt may be sent again after a failure, so the request may be applied more than once (as in Go;
a grant applied twice makes two leases). The old spec is the new one at `GrpcSpec.md Spec`
(`attemptPre_md`, `isGrpcRpcs_md`, `lessorRemoteAt_conn`). Callers are `client_lessor_isEtcdLease`'s
proof, `leasekv`/`leasegrant`/`leasecatchup`/`leaseexpiry`'s drivers, and the cache's lease contract.
Each is restated in its proof body only.

### 2.3 `retryLeaseClient.{LeaseGrant,LeaseRevoke,LeaseTimeToLive,LeaseLeases}.spec`

These take the same change: `GrpcSpecMd`, `isGrpcRpcsMd`, and `□ ▷ attemptPre conn (GoInterface.ok
ctx) Spec req Q`. They already name `conn`. Full text for LeaseGrant: probe §2.3.
`retryLeaseClient.LeaseKeepAlive.spec` (a stream) is unchanged: D2 leaves KeepAlive out.

## 3. The client's linearizable lease calls with auth on (F3; replaces `isEtcdLeaseOn`)

The server side is S3c's registration `etcd_lease_auth_served_on` at `etcdLeaseGrantSpecOn` /
`etcdLeaseRevokeSpecOn`. Their permits (`leaseGrantPermitM`, `leaseRevokePermitM` at `E.authOn`) hand
the caller's `kvAu1G … (kvOpStep (.leaseGrant id ttl))` / `(.leaseRevoke id)` update to the server,
which fires it at the entry's apply (S3a F3, S3b).

### 3.1 `client_lease_grant_on` (client/v3 `ResultsOn.lean`, new): probe §3.1

```lean
{{ isPkgInit client ∗ lessorRemoteAt l [addr] ∗
    isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseGrant" (etcdLeaseGrantSpecOn s E ρ γl) ∗
    ctxOk ci cd ∗ ctxErrClient ci cd ∗ □ (∀ id : w64, kvOpAu1 ρ.kv (.leaseGrant id ttl) (Q id)) }}
  l.Grant(ci, ttl)
{{ resp err, (err = nil ∗ ∃ m h, <header, ID, TTL fields> ∗ ⌜m.id ≠ 0⌝ ∗
      etcdReached (EM := v3rpc.etcdModelOfServer E ρ.rd E.authOn) m.hdr.revision ∗
      (∃ i lo, lease.leaseLiveFrom γl i m.id lo ∗ lease.leaseReqIs γl m.id ttl) ∗
      ∃ tok, v3rpc.leaseGrantResT E.authOn s E ρ tok ttl m.id Q) ∨
    (err ≠ nil ∧ clientErr err ∧ resp = null ∗ statusErrOk err) }}
```
With auth on, `leaseGrantResT` gives `Q id` of the model's state before the grant, at a published log
(`pubAfterM`), the header's user being the token's (`hdrBoundT`). The update is persistent because the
call may be applied more than once (§2.2). A caller that keeps the model in an invariant (the drivers do;
`client_Put_on` takes `□ kvOpAu1`) supplies it. The caller's update ignores the grant fact
(`kvAu1_G`). That is why the result needs no connection-level token (`clientAttemptMd`), unlike
`client_put_on`, and the existential `tok` is the margin. **Proof:** `lessor.Grant.specN` at
`etcdLeaseGrantSpecOn`, the attempt precondition from `srvReqLogLb_nil` and the update.

### 3.2 `client_lease_revoke_on`: probe §3.2

The same shape: `□ kvOpAu1 ρ.kv (.leaseRevoke id) Q`, the post `leaseRevokeRespMsg resp m ∗ etcdReached
… ∗ ∃ tok, v3rpc.leaseRevokeResT E.authOn s E ρ tok id Q` (with auth on: granted at `L`, published, `Q`
of the state before).

The driver calls `cli.Grant`/`cli.Revoke`. These are promoted methods of the embedded `Lease`
interface, and the driver unfolds them as `etcd_auth.client_Put_on` does: a driver lemma, not an export.

## 4. The read handlers with auth on (D6)

### 4.1 `etcdLeaseTTLSpecOn s E γl` (client/v3 `LeaseReadServed.lean`, new): probe §4.1

```lean
fun md (req : w64 × Bool) Φ Ψe =>
  iprop((□ ∀ d, Ψe d) ∗ ∃ n m : Nat, auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ∗
    ∀ r : LeaseTTLRespM, ⌜r.id = req.1⌝ -∗
      (if req.2 then v3rpc.leaseCheckT s E (auth.mdTokenOf md) n
          (fun info => leaseKeysVerdictFrom E.authMode n info γl m req.1 .read)
        else iprop(True)) -∗ Φ r)
```
**Go** (`v3_server.go:698-724`, `checkLeaseTimeToLive` 607-634): with `Keys`, the check runs before
any lookup or forwarding. It takes the principal (`AuthInfoFromCtx`; none → `ErrUserEmpty`). An admin
passes. Otherwise each key of the local lessor's `Lookup(id)` needs read permission. Then
`leaseTimeToLive` runs, at the leader or forwarded, and the auth revision is re-checked
(`ErrAuthOldRevision`). The spec's success fact is the handler's (`leaseTTLOut`'s `leaseCheckFrom`) at
the token (`leaseCheckT`, S1's `leaseCheckT_of_from`). The caller supplies the lower bounds `n` (auth
store) and `m` (lessor), as `etcdRangeSpecOn` supplies its `n`. An error carries nothing (HS-4). The
weaker auth-off `etcdLeaseTTLSpec` stays (D6). The text has no mode gate: at auth off `leaseCheckT`
holds by its `enabledVerdictFrom … false` arm. It is named `…On` for the served result it belongs to.

### 4.2 `etcdLeaseLeasesSpecOn s E γl` (new): probe §4.2

A listing at some lessor index `i ≥ m` (`lease.leaseIdsAt γl i r.ids`) with every listed lease's keys
verdict at the token. **Go** (`v3_server.go:737-783`): `Leases()` first, then `checkLeaseLeases` on
exactly those leases (admin passes; else read on every key of each), then the auth-revision re-check.

### 4.3 `etcd_lease_read_auth_served_on` (client/v3 `AuthnServedOn.lean`, new): probe §4.3

The sibling of `etcd_lease_auth_served_on` (D6). Its premises: `hγa : E.authMode = .on γa`, the lease
server (`quotaLeaseServerAt`, `leaseServerAt`), the lease-read contract `v3rpc.raftLeaseRead s E
(mvccLeases E.γ) (E.RD ∗ levelTok 0) (mvccReaders E.γ 1)` (as `etcd_leaseReadMethodsOk`, at the lessor
`mvccLeases E.γ`), the interceptors, `grpcServerAt`, and the pools. It gives `isGrpcRpcMd` of
`LeaseTimeToLive`/`LeaseLeases` at §4.1/§4.2 with `γl := mvcc.api.mvccLeases E.γ`.
`grpcUpOn`'s `grpcLeaseUp` already holds the four unary registrations (`v3rpc.leaseRegs`).

### 4.4 Finding F4: the `ErrLeaseNotFound` arms (frozen `Spec/` posts strengthened)

`LeaseServer.LeaseTimeToLive`/`LeaseLeases` (`v3rpc/lease.go:62-91`) turn an error with
`errors.Is(err, lease.ErrLeaseNotFound)` into a **successful** reply: TTL `-1`, or an empty listing.
Today's posts lose the information that Go only reaches this after the auth check passed:
- `EtcdServer.LeaseTimeToLive.spec`'s error arm gives, at `ErrLeaseNotFound`, only `leaseTTLRow -∗
  leaseAbsentFrom`. So v3rpc's `leaseTTLOut` −1 arm carries no check, and a refused `TimeToLive`
  might as well be the −1 success;
- `EtcdServer.LeaseLeases.spec`'s error arm is any `applyErrIs err`. So `leaseLeasesOut` keeps an
  empty-listing success arm at auth on.

With those, no refusal of `TimeToLive(…, WithAttachedKeys)` or `Leases` is provable. That covers checks
1, 3, 4 and 5 of the approved program, and the program panics if they succeed.

**Go facts.** `checkLeaseTimeToLive`/`checkLeaseLeases` fail only with `AuthInfoFromCtx`'s errors (with
auth on, one of the auth package's error variables: `authErrVarIs`, its spec's post), `ErrUserEmpty`,
`IsRangePermitted`'s, and `ErrAuthOldRevision`. Each is a leaf error variable of package `auth`, so
`errors.Is` against the lease package's leaf `ErrLeaseNotFound` (`leaseNotFoundErr`) is false: they are
distinct `errors.New` values with different messages. `leaseTimeToLive` returns `ErrLeaseNotFound` only
after the check passed. `LeaseLeases` never returns it.

**New texts** (probe §4.4; both are proved functions, not axioms):
- `EtcdServer.LeaseTimeToLive.spec`, error arm:
  ```lean
  -- old
          □ (∀ e, ErrLeaseNotFound ↦□ GoInterface.ok e -∗ errIsTrue err (GoInterface.ok e) -∗
              leaseTTLRow s γl -∗ lease.leaseAbsentFrom γl m v.ID')
  -- new
          □ (∀ e, ErrLeaseNotFound ↦□ GoInterface.ok e -∗ errIsTrue err (GoInterface.ok e) -∗
              (leaseTTLRow s γl -∗ lease.leaseAbsentFrom γl m v.ID') ∗
              authedOutB s E.authMode (GoInterface.ok ctx) GoInterface.nil ∗
              (if v.Keys' then leaseCheckFrom s E (GoInterface.ok ctx) n
                  (fun info => leaseKeysVerdictFrom E.authMode n info γl m v.ID' .read) else True))
  ```
- `EtcdServer.LeaseLeases.spec`, error arm: `… ∗ applyErrIs err ∗ □ (∀ e, ErrLeaseNotFound ↦□ e -∗
  errIsTrue err e -∗ False)`.
- Internal (v3rpc `InvLeaseRead.lean`): `leaseTTLOut`'s −1 arm gains `authedOutB … ∗ (if Keys then
  leaseCheckFrom …)`, and `leaseLeasesOut`'s `⌜E.authOn = true⌝ ∗ … []` arm is deleted. The specs of
  `LeaseServer.LeaseTimeToLive`/`LeaseLeases` are stronger posts. Their consumers (the auth-off
  `etcd_leaseTTLHandlerOk`/`etcd_leaseLeasesHandlerOk`) keep proving the weaker auth-off specs.

**Proof obligation** (item 7, est. +1–2 days): in `checkLeaseTimeToLive`/`checkLeaseLeases`'s specs
(proved), an error is `authErrVarIs` or `ErrUserEmpty`/`ErrAuthOldRevision`/the range check's, all
auth-package leaves. From there, `errIsTrue err ErrLeaseNotFound → False` by the leaves' `errMsgOk`
messages (persistent points-to agreement on the `errorString`'s field). If a check's spec does not yet
expose its error as an auth variable, that spec's post is strengthened (proved specs; a form).

## 5. The per-member lessor law (server, new module `LessorFollows.lean`, re-exported from `Results`)

### 5.1 Vocabulary (pure, `KVAuthModel`-level; probe §5)

```lean
/-- The auth-on model of the committed log `A` holds the key `k` on the live lease `id`. -/
def leaseHeldOn (γk : KVNames) (id : w64) (k : GoString) (A : List EntryModel) : Prop :=
  id ∈ (kvLeasesOn γk srvAuthSt0 A).ids ∧
    (mvcc.leaseItemsOf (mvcc.stateAfter (kvModelOn γk srvAuthSt0 A))).lookup ⟨k⟩ = some id

/-- … at every prefix of `A` from `A₀` on. -/
def leaseHeldThrough (γk : KVNames) (id : w64) (k : GoString) (A₀ A : List EntryModel) : Prop :=
  ∀ A₁, A₀ <+: A₁ → A₁ <+: A → leaseHeldOn γk id k A₁

/-- A lessor snapshot holds `k` on the live lease `id`. -/
def lsHolds (σ : lease.LSnap) (id : w64) (k : GoString) : Prop :=
  (∃ l, σ.1.lookup id = some l) ∧ σ.2.1.lookup ⟨k⟩ = some id
```

### 5.2 The law

```lean
theorem lessor_keys_of_read (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (log : mvcc.Log)
    (A₀ : List EntryModel) (id : w64) (k : GoString) (hon : E.authOn = true)
    (hA₀ : uint.Z γr.raft.ai0 + A₀.length ≤ uint.Z c) :
    isServerReadM E.authOn s E γr ∗ readLogOk γr c log ∗ srvRLogLb γr.raft A₀ ⊢ |={⊤}=>
      ∃ m : Nat, lease.lessorLb (mvcc.api.mvccLeases E.γ) m ∗
        □ ∀ (i : Nat) (σ : lease.LSnap), ⌜m ≤ i⌝ -∗ lease.lessorAt (mvcc.api.mvccLeases E.γ) i σ -∗
          ∃ A : List EntryModel, srvRLogLb γr.raft A ∗
            ⌜A₀ <+: A ∧ (leaseHeldThrough γr.kv id k A₀ A → lsHolds σ id k)⌝
```
In words: after a linearizable read at a member (the barrier's `readLogOk` at a committed index `c`
covering the log `A₀`), the member's lessor has a lower bound `m`. Every snapshot it takes from `m` on is
taken while the member has applied a committed log `A ⊇ A₀`. The snapshot holds `k` on `id` if the
auth-on model held it at every prefix from `A₀` to `A`. The read gives the probe's
`leaseKeysVerdict_refused` input: the driver shows `leaseHeldThrough` for every committed `A` at which a
check could be answered (its model since barrier 2 changes only by its own refused steps, or by
re-deliveries that keep `k` on `id`). Then `leaseHoldsFrom` over the check's window refutes the passed
verdict. The law is stated at `E.authOn` with `hon`, a scope restriction: the auth-off lease theorems are
single-member and use `leaseTTLRow`, so no auth-off client needs the law, and the off model's
vocabulary would double it.

### 5.3 Why it is true of Go

- A member's lessor changes its live set and items only when the apply thread applies an entry:
  `Grant`, `Revoke` (also expiry, which proposes a `LeaseRevoke` entry), `Attach`/`Detach` from mvcc's
  put and delete (`kvstore_txn.go:226-290, 338`), and `Recover` at a snapshot install (the snapshot's
  state, the model at its index). `Checkpoint`, `Promote`, `Demote` and `Renew` change TTLs and expiry
  only.
- Within one entry the pair (`k` on `id`) changes at most once. `put` returns early when the key's
  lease is the same (`kvstore_txn.go:264`). `checkIntervals` refuses two puts of a key and a put that a
  delete in the same transaction covers. The nested-sibling case it misses
  (`issues/etcd-txn-check-intervals-sibling.md`) puts and then deletes, which ends without `k`, and the
  log premise `ReqOp.siblingSafeL` excludes it anyway. A revocation is its own entry. So if the model
  holds the pair before and after an entry, every snapshot taken while the entry was applied holds it.
- The read: `readLogOk γr c log` gives `appliedLogAt γr ci₀ L₀` with `c ≤ ci₀`, so the member had applied
  `A₀` when the read returned. Its lessor index then is `m`.

### 5.4 How it is proved (item 7; Draft §8 risk 1)

The server has no fact today tying lessor history indices to applied prefixes. `srvRestAt` holds the apply
thread's half of the live set (`ltHalf E T.ids`) at entry boundaries, and mvcc's `lease.leaseOwn γ L I`
ties the lessor's current items to the store's pending items. Neither is historical. The law needs
**one new internal conjunct**, `lessorFollows E γr A` in `srvRestT` (all modes share it). It is a
persistent mono-list, appended by the apply thread, mapping each applied index to the lessor index at
that point, plus a pointwise claim on each history snapshot: the agreement of §5.3 between the
boundaries `A`, `A ++ [e]`. Each lessor-touching applier maintains it: the Put, Txn, Delete,
LeaseGrant and LeaseRevoke appliers, `applySnapshot`'s `Recover`, and the boot. It needs the lessor's
and mvcc's write specs to report the index of each snapshot they push (`lessorAt γl i σ` of the new
one). Where a spec does not report it, that spec's post is strengthened (proved specs; a form). The
§5.3 per-entry fact comes from the entry's shape facts (`txnShape`, `siblingSafeL`, which the claims
already carry) and the model's `put` (same lease: unchanged). Estimate: Draft §7 item 7's 4–6 days. If
the per-push index is not available from the mvcc layer in that time, the next option is to put the tie
into the lessor's own invariant (its history is the sequence of `leaseOwn` values) and keep the
apply-thread side to entry boundaries.

**Fallback (Draft §8), corrected.** Draft §8 proposed running the lessor-side checks at member 0 only. That
does not avoid the tie: no single-member law exists either (`leaseTTLRow` gives only the
single-voter forwarding fact, not keys). The real fallback, if the tie cannot be built: the lessor-dependent
refusals (`u`'s and `v`'s `TimeToLive(…, WithAttachedKeys)` and `Leases`, checks 3–5) are run but
not panic-checked. The lessor-independent ones stay checked: check 1's (no token, invalid token: the
check fails at `AuthInfoFromCtx`/`ErrUserEmpty` before reading the lessor, with §4.4) and every
raft-path refusal. That changes the approved program (D1) and goes to the user.

## 6. Decisions for etcd-grove-02

1. **D-a–D-c** (the KV filters at the server's lease mode). Recommend: accept. It is the Draft's intent,
   as the server's frozen permits allow.
2. **D-d** (`kv.Put.spec` unchanged). Recommend: accept; the Draft row was unprovable and is not needed.
3. **D-e** (concrete `client_lease_grant_on`/`client_lease_revoke_on` instead of the bundle
   `isEtcdLeaseOn`). Recommend: accept (the canonical-spec principle; one fewer predicate).
4. **D-f / F4** (two frozen `Spec/` posts strengthened, proved code). Recommend: accept; without it checks
   1, 3–5 are unprovable.
5. **D-g** (the law's statement §5.2, `hon`-scoped, and the new internal conjunct §5.4). Recommend:
   accept, with §5.4's fallback order.

Review rounds: `/shared/tmp/auth-lease-s4/freeze-review-r*.md` (§7).

## 7. Review log

### Round 1 (fresh `spec-reviewer`, `/shared/tmp/auth-lease-s4/freeze-review-r1.md`): 12 first-tier findings, NOT yet applied

The round confirms the following as sound: §1's filters (they match `putPermitOn`/`txnPermitOn`, and the
views laws hold), D-d (`kv.Put.spec` unchanged), §2's lessor specs (`□ ▷ attemptPre` fits the repeatable
policy), §4.4's strengthened posts (true of Go), and D-e (concrete results over a bundle). The first-tier
findings and how each is to be handled in rev 2:

| finding | what | disposition (rev 2) |
|---|---|---|
| K1 | the driver's leased put/txn are not reachable through `client_put_on` (no options) / `client_txn_on` (`txnUpdAtOn` still `txnPlain`) | accept: `txnUpdAtOn`'s write branch widened as §1.3 (internal); `client_put_on` generalized to options `gs` with the filter as a pure premise (an exported result restated: add to §0 as D-j) |
| C1 | a grant-blind update plus `∃ tok` leaves the driver nothing to refute `u`'s/`v`'s revocations with, and lets a re-delivered update delete `z/lease` | accept: `opGrantT` covers `.leaseGrant`/`.leaseRevoke` (`writeGrantG … irrLease*`); the results take `lessorRemoteAtC l conn`, `clientOpAuOn … (.leaseRevoke id) Q`, post `∃ md, ⌜clientAttemptMd conn ci md⌝ ∗ leaseRevokeResT … (mdTokenOf md)` (`client_put_on`'s shape) |
| C2 | check 1's token-less/bad-token `Grant` refusal is unprovable: `etcdLeaseGrantSpecOn` (S3c, frozen) drops `requireAuthInfo`'s fact | accept, **D-h** (changes an S3c registration): reply gains `□ (⌜E.authOn = true⌝ → ∃ info, v3rpc.principalBoundT s E.authMode (mdTokenOf md) info)`; same for `etcdLeaseRevokeSpecOn` |
| C3 | `clientTokAt` lacks the client's `Lease` over the same connection | accept, **D-i**: `clientTokAt` gains `∃ lp, Client.Lease ↦□ lessorIfaceOf lp ∗ lessorRemoteAtC lp conn eps` (New's post strengthened) |
| R1 | `TimeToLive` without keys: success carries `True`, so check 1 is unprovable | accept: `leaseCheckT … (fun info => if req.2 then leaseKeysVerdictFrom … else True)`; keep the TTL-row fact (second tier) |
| R2 | `hγa` looks unneeded in the read served result | check in rev 2: if unused, drop it, so the result becomes the one read registration and the old specs become corollaries |
| L1 | **unsound**: a snapshot install (`Recover` empties the items, then `kv.Restore` re-attaches them) breaks the law; `nonissues/etcd-lease-keys-mid-apply.md` | accept: the law takes the member's no-snapshot-install mode (the boot's `NoSnapCount`/`NoSnapCatchUp`, a mode of the state, not a second law), or a conclusion weakened inside a restore; §5.3's `Recover` sentence is wrong |
| L2 | **no producer**: the driver cannot prove `leaseHeldThrough` (it sees the current model state only; persistent updates in an invariant) | **design decision**: (a) recommended: a client-held view of the lease-item history (as `authHistView`/`authHistCell` for the auth history, 5b), maintained by `kvInvOn`, with every item-changing entry needing its holder's (grant-told, C1) update; est. +3–5 days, write the driver's proof sketch against it first; (b) the law outputs `leaseHoldsFrom` under a driver-supplied invariant premise that the apply proof consults (departs from TaDa) |
| L3 | `hon : E.authOn = true` over a free mode breaks the hard rule; it conflicts with the Draft's "no literal modes" | **to the user**: state the law mode-generically (over `kvModelM`/the mode's table, if true at off) or at the literal `true` (the gate counts it) |
| (the rest) | second tier: `leaseHeldIn σ` over `KVState` vocabulary; `∃ log`; the docstring of `etcdLeaseGrantSpecOn` ("state after" → "before"); `checkLeaseLeases.spec` strengthened for certain; `ttlAns`/`leasesAns` in the change list; full texts of the other three `retryLeaseClient` specs; the token comes from per-RPC credentials | apply in rev 2 |

**Not done:** rev 2, then rounds 2 and 3. The session stopped here (its context was large; L2 and L3 need
decisions before rev 2 can be written).

## 8. Rev 2: stopped at the L1 hard stop (2026-11-16)

Rev 2 began with the driver's proof sketch, as decided. It stopped at the first hard stop: **the L1 premise
(the member installs no snapshot) cannot be discharged by the driver.** On etcd-grove-02's go, rev 2 then applied
everything independent of L1 (§9), with §5's law carrying L1 as a marked placeholder parameter
`memberNoSnapInstall`. L1 itself goes to the user.

### 8.1 L1: why the driver cannot discharge "no snapshot install"

- **Go.** No member installs a snapshot in the program's runs. A follower installs one only when the leader sends
  `MsgSnap`, and raft's `maybeSendAppend` sends one only if the follower's next entries are compacted from the
  leader's storage. With `NoSnapCatchUp = 2^48`, `compactRaftLog` compacts to `compactIdx snapi 2^48 = 1` while
  `snapi ≤ 2^48` (`Spec/.../EtcdServer__compactRaftLog.lean`), and every follower's `Next` is at least 2 after
  bootstrap. So the claim holds as long as the log stays below 2^48 entries, which the theorem's `n + 2 ≤ 2^28`
  steps ensure. Without a bound on steps it is false: a follower that lags 2^48 entries gets a snapshot.
- **The proofs today.** Nothing in them excludes an install:
  - raft's queued-message certificate admits any `MsgSnap` whose snapshot is certified (`qCert`,
    `InvRawnodeReady.lean:548`);
  - the raft-level no-snapshot mode `RaftNames.reNoSnap` ("leaders' progress stays at `Next ≥ 2`, storage's first
    index at most 2") was dropped at raft's level (U8 v2; `UniNames.noSnap : γ.raft.reNoSnap = false`);
  - etcd creates a certified raft snapshot every `SnapshotCount` (= `DefaultSnapshotCount`) applied entries. The
    log length is unbounded in the logic: elections add entries, and no time receipt is tied to log indices.
  - auth3's results say the same: "the proof covers snapshot installs … but this run never reaches one".
- **What discharging it needs** (none of it is driver work):
  - (i) a raft fact: no `MsgSnap` while the storage's first index is at most 2 and every follower's `Next ≥ 2`.
    This is the dropped mode's invariant, now as a raft API fact.
  - (ii) etcd's compaction at index 1 only while `snapi ≤ 2^48`, which `compactRaftLog.spec` already gives.
  - (iii) a bound `< 2^48` on log indices, from time receipts (`receiptBound GF ≤ 2^48` is already fixed by the
    adequacy theorem, `etcdstart`'s `Hrb48`), so raft's log append would have to carry a receipt per index.
  - (iv) a server-level mode or fact that carries (i)–(iii) to the per-member law.
  This is a change to raft's API and invariant (sealed package, `etc/api/raft.txt`) plus a server-level mode.
  Estimate: 5–10 agent-days. Uncertain: (iii) has no precedent here.

### 8.2 Options (to etcd-grove-02 / the user)

1. **Cluster-level no-install fact** (8.1 (i)–(iv)). It keeps the approved program and the law as decided (L1).
   Cost 5–10 days, and a raft API change.
2. **The law weakened in a restore window** (review r1's alternative). It is true at every member. The driver
   cannot exclude a restore, so checks 3–5's lessor-side refusals (`TimeToLive` with keys, `Leases`, for `u` and
   `v`) become unprovable. That is Draft §8's fallback: run but not panic-checked. It changes the approved program
   (D1), and it goes to the user.
3. **A different program.** The withdrawn fallback, or a program whose lessor-side checks are asked where no
   install can occur. No candidate is known: a leader can also step down and install a snapshot.

**Recommendation:** option 1 if the stage's budget allows, since it is true of Go and keeps the approved theorem.
Otherwise option 2, to the user.


### 8.2a Option 1, costed: how much of D21 M3 comes back

D21 M3 (`notes/decisions.md`, "D21 M3 carried out", 2026-10-19) proved exactly this fact for putget/putget3, and T-S
lifted it so that snapshots are covered. What is still in the tree, and what went:

| piece | M3 (2026-10-19) | today |
|---|---|---|
| the cluster's mode | `RaftNames.reNoSnap`, `reNoSnap_ok` (bootstrap log) | **kept** (field; `UniNames.noSnap` forces `false`) |
| the node's flag | `NGhost.ns`, `NsLink`, kept by every step | **kept** (`StepGhostMode.lean`), always `false` (`ownRaftPhys`'s `Hnsoff`) |
| the leader's progress clause | `PrLo` (`Next ≥ 2`, replicate ⇒ `Match ≥ 1`, not `StateSnapshot`) in `PrOkN` | **kept as text** (`Defs.lean:708-714`, 73 mentions); its proofs at `ns = true` are vacuous now and must be redone |
| the storage cap | `MemStorNames.cap`, `storCap`, `memCutInv`'s `Hccap`; `NsCap` = `storCap storage 1` | **gone**: `NsCap ns _ := ⌜ns = false⌝` (`InvRaftPhys.lean:849`); `storCap` left in 3 files only |
| the server's no-`MsgSnap` | `srvMsgNoSnap` from `isRaftMsg`; `"%Hone"` removed | `srvMsgNoSnap` **kept**, still used for ordinary messages (`ServerOn.lean:78`); `MsgSnap`s now go through the applier's bag (`isRNMsgSnapC`, `InvApplyAll.lean:134`) and `sendMergedSnap` |
| the run bound | `receiptBound ≤ SnapshotCatchUpEntries + 1` through the apply pool's count (`appliedi ≤ a`, `a < receiptBound`) | **the pool is kept** (`srvWTPool`, `⧗ a`, `InvApplier.lean:1150`); `etcdstart` already has `Hrb48 : receiptBound GF ≤ 2^48` and the examples set catch-up `2^48`, so the bound is free; the clause `appliedi ≤ a` must be re-checked |
| compaction | `compactRaftLog` at index 1 while `snapi ≤ scu` | **kept** in `compactRaftLog.spec` (`compactIdx`) |
| the fork's fix (A1) | raft's stale-`appResp` fix, so (N) `firstIndex ≤ Next ≤ lastIndex + 1` holds | **kept** (the pinned raft has it, `issues/raft-stale-term-appresp-index-zero-ack.md`) |

**The plan.**

1. **Raft (sealed API, `etc/api/raft.txt`).** Let the mode be on again. `NsCap` regains `storCap storage 1` at
   `ns = true` (the cap comes back on `MemoryStorage`: `MemStorNames.cap`, `Compact`/`ApplySnapshot` take
   `index ≤ cap`). Then re-prove `PrLo` at the leader in the mode, so that `maybeSendAppend`'s `ErrCompacted`
   branches are dead. The API gains one fact: in the no-snapshot mode a `Ready` hands out no `MsgSnap`, and
   `qCert`'s `reNoSnap = true` disjunct becomes live. Files: `InvRaftPhys`, `Defs` (`PrOkN`),
   `StepGhostMode`, `MemstorageApi` and the `MemoryStorage` proofs (`Compact`, `ApplySnapshot`), `raft.go`'s
   progress branches (`maybeSendAppend`, `handleAppendEntries`' reject path), `ApiVocab`, `InvApi`
   (`UniNames.noSnap` becomes a choice), `StartNode`'s allocation (`ownRaftGhost_alloc_boot`). **3–5 days**,
   the bulk of the work. M3 took about that from scratch, and the progress clauses' text survives.
2. **Server.**
   - In the mode, the applier's `MsgSnap` bag stays empty, so `sendMergedSnap` never runs.
   - `applySnapshot` is reached only with an empty snapshot, so no `Recover`/`Restore`.
   - The storage cap holds: `compactRaftLog` compacts at `compactIdx = 1` because `snapi ≤ appliedi <
     receiptBound ≤ 2^48 = scu`. The pool's `appliedi ≤ a` clause gives this, and it is re-added if it went
     with T-S.
   - `NewServer` and `bootOk` take the mode at the cluster's allocation (`ServerRaftNames`), where the boot
     premise has `scu = NoSnapCatchUp`.
   - **`memberNoSnapInstall s E γr` becomes `⌜γr.raft…reNoSnap = true⌝`**, a pure fact of the names, i.e. a mode
     of the state and not a token. Files: `InvApplyAll`, `ApplyAllSnap`, `EtcdServer__applySnapshot`,
     `EtcdServer__compactRaftLog`, `NewServer`/`NewServerR`, `InvBoot`, `InvApplier`.
   - **2–3 days.**
3. **Allocation and drivers.** `allocNOnM` and `memberBootOn` take the mode (all members `NoSnapCatchUp`); every
   closed example keeps `reNoSnap = false`, or `true` where it boots with these settings (its choice, proof
   bodies only); authlease takes `true`. **0.5–1 day.**
4. **The bound.** The receipt bound is already the adequacy theorem's: `receiptBound GF ≤ 2^48` (`Hrb48`, fixed by
   `ReceiptBoundLe` in `etcdstart`). Nothing new is needed from `threadBound`. The only bound fact needed is
   `snapi ≤ appliedi < receiptBound`, from the apply pool. **No new trusted text.**

**Total 6–9 agent-days.** It is a raft API change (sealed package) and needs an `interface/` diff review of raft's
API. Risks:
- (a) the T-S changes to `MemoryStorage` and `compactRaftLog` may have removed more than the cap, which would add
  1–2 days;
- (b) every cluster that today needs `reNoSnap = false` (snapshot-taking examples: partition, linkv3p, restart)
  keeps it, so the mode must stay a choice, not a default.

The alternative (option 2) costs nothing in Lean but changes the approved program (checks 3–5's lessor
refusals unchecked).

### 8.3 L2 and L3 under the sketch: a lighter realization of (a) (ACCEPTED by etcd-grove-02, 2026-11-16)

The driver's sketch found that the client already holds a view of the lease-key history. A KV state
`σ : KVState` keeps every revision's changes (`σ.changes`, `σ.at r`), and each key-value carries its lease, so
`mvcc.leaseItemsOf (σ.at r).kvs` is the item map at every revision. The client half `etcdKV γk σ` is that view.
Every change of it needs its holder's update (`kvAu1G`), and the driver keeps it in a cell (its invariant), as
`authHistCell` does. So (a) needs no new server ghost state (no `γk.lhist`, no new per-write update):

```lean
/-- `k` is on the lease `id` at every revision of `σ` from `r₀` on. -/
def leaseKeptIn (σ : KVState) (r₀ : Nat) (id : w64) (k : GoString) : Prop :=
  r₀ ≤ σ.rev ∧ ∀ r, r₀ ≤ r → r ≤ σ.rev → (mvcc.leaseItemsOf (σ.at r).kvs).lookup ⟨k⟩ = some id
-- the law's conclusion (replacing §5.2's ∃ A … leaseHeldThrough):
--   ∃ m, lessorLb γl m ∗ □ ∀ i σl, ⌜m ≤ i⌝ -∗ lessorAt γl i σl -∗
--     ∀ σ, etcdKV γr.kv σ ={E}=∗ etcdKV γr.kv σ ∗ ⌜leaseKeptIn σ (readRev log) id k → lsHolds σl id k⌝
```

- **The sketch** (checks 3–5):
  - The driver's cell holds `etcdKV σ` with `leaseKeptIn σ r_put Lz z/lease`, and the same for `(Lu, a/lease)`
    until it issues the final revocation.
  - Every update it hands out keeps the cell:
    - a re-delivered `Put(z/lease, Lz)` keeps the pair;
    - `u`'s `Revoke(Lz)` and leased `Put(a/x, Lz)` are refuted at their commit. The grant, told at `u`'s token
      (C1), needs write on `z/lease`, which `u` lacks;
    - `v`'s `Revoke(Lu)` is refuted the same way.
  - `r_put ≤` barrier 2's read revision, by the floors.
  - At a check's reply, the driver opens the cell and applies the law. The result is `lsHolds` at every index
    `≥ m`, which is the probe's `leaseHoldsFrom`, so `leaseKeysVerdict_refused` refutes the passed verdict.
  - Checks 1–2 and the end checks do not use the law. They use C1, C2 (D-h), R1 and K1 as dispositioned.
- **L3:** the hypothesis is in `KVState` terms, which both modes' models produce. So the law is stated over
  `isServerReadM E.authOn` with no `hon` and no literal. At auth off the same Go argument holds over the off model. Where `kvInv` holds the whole state (a granting
  cluster), the premise `etcdKV σ` is contradictory, so the law holds there trivially. To be checked in the proof.
- **Proof obligations this adds:**
  - liveness from the items: in the model, an attached key's lease is live, because a revocation deletes its keys
    at a revision and a put on a dead lease is refused;
  - the state at a committed prefix is a revision-prefix of the state `etcdKV` holds.
  Both are model or server lemmas.

## 9. Rev 2's texts (2026-11-16; `Scratch/S4Freeze.lean`, `etc/lean-check.py -a`: 0 errors)

Each r1 finding, applied (the Scratch name in brackets; old texts §1–§5 above where unchanged):

| finding | change | Scratch |
|---|---|---|
| K1 | `txnUpdAtOn`'s write branch: `txn.txnPlain t ∨ (ρ.kv.lm = .revocable ∧ txnPlainL t)` (internal); `client_put_on` generalized to options `gs` (`optsAt sl gs`, the request `putWireOf (opPutModel key val gs)`, premises `opSizeOk`, `¬ putPanics ∧ t = 2`, and the filter `leaseID = 0 ∨ ρ.kv.lm = .revocable`), at `etcdPutSpecOnN`. **D-j**: an exported result restated; the no-option form is the instance `gs := []`. `putPermitM_of_dep` (`ServerKVOn.lean:369-397`, `Or.inl hl`) is the one server-side place that changes. | `txnUpdAtOnN`, `client_put_on_stmt` |
| C1 | `v3rpc.opGrantT` gains the lease rows (`writeGrantG … (irrLeaseGrant id ttl)` / `(irrLeaseRevoke id)`, header at the token), so `clientGrant`/`clientOpAuOn` cover lease operations. The lease results take `lessorRemoteAtC l conn [addr]` and `□ clientOpAuOn … (.leaseGrant id ttl) (Q id)` (`∀ id`) / `(.leaseRevoke id) Q`; post `∃ md, ⌜clientAttemptMd conn ci md⌝ ∗ leaseGrantResT/leaseRevokeResT … (mdTokenOf md) …` (`client_put_on`'s shape; no `∃ tok`). | `opGrantTN`, `clientGrantN`, `clientOpAuOnN`, `client_lease_{grant,revoke}_on_stmt` |
| C2 / D-h | `etcdLeaseGrantSpecOn`/`etcdLeaseRevokeSpecOn` (S3c registrations): the reply also gets `□ (⌜E.authOn = true⌝ → ∃ info, principalBoundT s E.authMode (mdTokenOf md) info)` (`requireAuthInfo`'s fact, which `EtcdServer.LeaseGrant.spec`'s `authedOutB` gives); the client results carry it at their `md`. Docstring: `Q` of the state **before** the grant. | `etcdLeaseGrantSpecOnN`, `etcdLeaseRevokeSpecOnN` |
| C3 / D-i | `clientTokAt` gains `∃ lp, Client.Lease ↦□ *lessor lp ∗ lessorRemoteAtC lp conn eps`; `New`'s post (`InvClientNewResult.lean:180`, today `lessorAt lp eps`) strengthened to name the connection. | `clientTokAtN` |
| R1 | the TTL spec's success: `leaseCheckT s E (mdTokenOf md) n (fun info => if req.2 then leaseKeysVerdictFrom … else True)` (authentication with or without keys), and the TTL-row fact kept (second tier). Proof risk (review r1): the no-keys arm from `authedOutB` may need `requireAuthInfo.specC`'s `n`-relative form. | `etcdLeaseTTLSpecMd` |
| R2 | `hγa` dropped and `γl` freed (the lease-read contract's); the result is the one read registration, renamed `etcd_lease_read_served`, the specs `…SpecMd` (any mode); `etcd_leaseReadMethodsOk`'s texts become corollaries. If the proof finds a use of `hγa`, it comes back as a marked scope restriction. | `etcdLeaseTTLSpecMd`, `etcdLeaseLeasesSpecMd`, `etcd_lease_read_served_stmt` |
| L1 | open (§8): the law's premise `memberNoSnapInstall s E γr`, a **parameter of the statement** (no definition), marked as the placeholder | `lessor_keys_of_read_stmt` |
| L2, L3 | §8.3 (accepted): `leaseHeldOn`/`leaseHeldThrough` deleted; `leaseKeptIn σ r₀ id k` (pure, `KVState`); the law over `isServerReadM E.authOn` (no `hon`), its conclusion against `etcdKV γr.kv σ` at any mask with `kvN`, `srvRaftN`, threshold the read's revision `log.length`; `srvRLogLb A₀` and `ai0 + |A₀| ≤ c` gone (the read's revision replaces them) | `leaseKeptIn`, `lsHolds`, `lessor_keys_of_read_stmt` |
| second tier | full texts of `retryLeaseClient.LeaseRevoke/LeaseTimeToLive/LeaseLeases` (§2.3). `kv.Put.spec`'s docstring: "etcd's auth-off Put spec". §2's token sentence corrected: a user client's token comes from its per-RPC credentials, which grpc sends first (`attemptTokOk`); only the bad-token client's token is in the context. §4.4: `checkLeaseLeases.spec`'s error post strengthened from `applyErrIs` to the auth package's error variables (as `checkLeaseTimeToLive.spec`'s `authErrVarIs`), a frozen-spec change of a proved function, certain. The v3rpc contract's `ttlAns`/`leasesAns` (`InvLeaseRead.lean:65-93`) change with §4.4 (the −1 arm's check; no auth-on empty listing). `raftLeaseRead_server` (`v3rpc/Results.lean:2083`) re-proves them. `ErrLeaseNotFound`'s message fact in `etcdserver` (`errMsgOk`, the lease package's init): to check in item 7. | `retryLeaseClient.*.specN` |

**Not done:** review rounds 2–3 (after the L1 decision).
