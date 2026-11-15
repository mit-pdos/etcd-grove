# auth-lease S3b Draft: the request side with auth on (grant, revoke, leased put and transaction)

2026-11-15 · branch `auth-lease` (lean `17d12658f5`, S3a and S3a2 landed) · plan: `notes/auth-lease-handoff.md`
("S3b"), `notes/auth-lease-scope.md` §2.3 ("The entry points with auth on") and §7.3, S3a Draft F3 (§2, "What a
lease entry's claim carries"), S3a2 Draft §4a (`authTie` option (b)). Probe: `Scratch/S3bProbe.lean` (untracked;
copy `/shared/tmp/auth-lease-s3b/S3bProbe.lean`), §3.

**Revision 2 (2026-11-15)**: review round 1 (`/shared/tmp/auth-lease-s3b/review-r1.md`, fresh `spec-reviewer`) found
every statement true and provable and no closed theorem changed; first tier F1 (the served lease registrations at
the mode, Scope §5's S3 item, not placed: now decision D6, recommended in S3c, §0, §5, §7) and F2 (§6 missed the
exported `Results.lean` theorems that are a changed spec by name, and `reqPropOkOn`'s weaker premise of
`raftRequest`/`processInternalRaftRequestOnce`) applied; second tier S1 (`leaseGrantResM`'s header tied by
`pubAfterM`), S2 (the specs' pure premises into the precondition), S3 (laws, §6), S4 (callers, `authTie_of_kvOutL`,
docstrings), S5 (D1's alternative (c) weighed, kept (b): §7), S6 (the revocation's margin, D5) and the nits applied.

**Revision 1 (2026-11-15).**

## 0. What S3b does, and what it leaves

S3a/S3a2 gave the auth-on model the lease table and admit, at the revocable lease mode, grants, revocations and
leased puts and transactions (`plainEntryOn lm`, `plainReqL lm`); the apply thread decides them (`kvGrantedL`,
`authTie` option (b)). Nothing proposes them with auth on: `srvGrantsLeases`/`srvRevokesLeases` require auth off,
`reqPropOkOn` (the proposal's obligation with auth on) has no lease form, `putPermitOn` requires lease `0` and
`txnPermitM` `txn.txnPlain`. S3b adds the proposers at the server package's entry points:

- `EtcdServer.LeaseGrant`, `EtcdServer.LeaseRevoke` with auth on (§4), each carrying its client's update (F3);
- `EtcdServer.Put` with a lease, `EtcdServer.Txn` with leased puts, at the revocable mode (§2);
- the proposal's obligation `reqPropOkOn` with the lease forms (§2), discharged at the commit by S3a's
  `kvInvOn_commit_granted`/`kvModelOn_snoc_granted` (any kind, the lease arms of `kvOpStep` included);
- the answers: success of a leased put says its lease was live (§4.1); success of a revocation says it was granted
  (§4.3); errors, `ErrLeaseNotFound` included, stay `applyErrIs` errors (§4.4).

**Left to S3c** (as the brief and the Scope): `srvGrantGuard`, `lease.bootCfg`, `lease.srvInvAt`'s
`srvLessorNil`, `srvUberOn`, `NewServer`; a built auth-on server is still a cluster that grants none, so S3b's new
cases are reachable only in the specs' proofs, not by a closed theorem. **The served lease registrations at the
mode** (Scope §5's S3 item: v3rpc's lease handler contracts `lessorGrantOkG`/`lessorRevokeOk` at `isServerReqM
E.authOn` with the client's deposit, `ServerLeaseGrant`/`ServerLeaseRevoke`/`v3rpc/Results`' `lessor*_server`, and
etcdstart's `etcdLeaseServedAt` at `etcdModelOfServer E γr E.authOn`) are **not in S3b**: decision D6 recommends S3c,
beside the couplings `etcdLeaseServedAt` needs (`srvLeaseRd_srvInv`, `lease.bootCfg`); in S3b those callers stay at
auth off (they hold `isServerReq` and pass the off form of the new premises, `True`). **Left to S4**: the gRPC KV
path with a lease (`putPermitM_of_dep` keeps lease `0`), the client's `WithLease`, `Put`/`Txn` with a lease and the
linearizable `Lease.Grant`/`Revoke` client specs that fire the claims (F3's S4 half).

## 1. Vocabulary

**The cluster grants / revokes leases** (Scope §2.3, as approved):

```lean
-- old (LeaseGrant.lean:43, RevokeCtx.lean:65)
def srvGrantsLeases (E : apply.AEnv GF) (ρ : ReqNames) : Prop := ρ.rd.kv.lg = true ∧ E.authOn = false
def srvRevokesLeases (E : apply.AEnv GF) (ρ : ReqNames) : Prop := ρ.rd.kv.lm = .revocable ∧ E.authOn = false
-- new
def srvGrantsLeases (E : apply.AEnv GF) (ρ : ReqNames) : Prop := ρ.rd.kv.lg = true
def srvRevokesLeases (E : apply.AEnv GF) (ρ : ReqNames) : Prop := ρ.rd.kv.lm = .revocable
```

Users that read the auth-off half: `EtcdServer__LeaseGrant.lean:58` (`obtain ⟨hlg, hoff⟩`, the proof's mode-off
case split moves to `isServerReqM`), `EtcdServer__revokeExpiredLeases.lean:71` (builds `⟨hlm, hoff⟩`; auth off
still follows from the slice's grant guard until S3c), etcdstart `ServedLease.lean:263` and `:321` (`⟨hlg, Hoff⟩` →
`hlg`). Their docstrings (`LeaseGrant.lean:36-41`, `RevokeCtx.lean:59-63`) lose the auth-off sentence. The
v3rpc results that take `h : srvGrantsLeases E ρ` (`lessorGrantOkLive_of_server`, `lessorGrantOkL_of_server`,
`lessorRevokeOk_of_server` and their `_server` corollaries) keep their texts; they also take `isServerReq s E ρ`,
which gives auth off (`isServerReq_authOn`), so their meaning is unchanged. The `WithRoot.spec` docstring
(proved spec, `Spec/…/auth/authStore__WithRoot.lean:34`) names `srvRevokesLeases` as what keeps its one caller at
auth off; it becomes `srvGrantGuard` (form).

**`grantedAt` at the model's whole verdict** (the lease part included; handoff "S3a2 … Next", S3a2 §4a's reason
for (b)):

```lean
-- old (ProposeOn.lean:136)
def grantedAt (γk) (st₀) (rq) (L) : Prop := kvGranted (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L).1 rq
-- new
def grantedAt (γk) (st₀) (rq) (L) : Prop :=
  kvGrantedL (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L).1
    (mvcc.leaseItemsOf (mvcc.stateAfter (kvModelOn γk st₀ L))) rq
-- law restated (old: `↔ kvGranted (srvAuthAtLog γk st₀ L) rq`)
theorem grantedAt_iff : grantedAt γk st₀ rq L ↔
    kvGrantedL (srvAuthAtLog γk st₀ L) (mvcc.leaseItemsOf (mvcc.stateAfter (kvModelOn γk st₀ L))) rq
-- new laws
theorem grantedAt_kvGranted : grantedAt γk st₀ rq L → kvGranted (srvAuthAtLog γk st₀ L) rq
theorem grantedAt_plain (hp : plainCover rq) : grantedAt γk st₀ rq L ↔ kvGranted (srvAuthAtLog γk st₀ L) rq
theorem grantedAt_grant (hk : apply.dispatchKind rq = .leaseGrant) : grantedAt γk st₀ rq L
-- in the client's terms (review r1 S3): the update's `G σ` at the state it fires at
theorem writeGrantG_granted : writeGrantG γk st₀ Gb rq₀ L₀ σ ⊢ ∃ hm L, Gb hm ∗ authHistLb γk (admStates γk st₀ L) ∗
    ⌜L₀ <+: L ∧ kvGrantedL (srvAuthAtLog γk st₀ L) (mvcc.leaseItemsOf σ.kvs) (apply.withHeader rq₀ hm)⌝
```

(`σ = kvStateOf (kvModelOn L) (kvLeasesOn L)`, so `σ.kvs = stateAfter (kvModelOn L)`.)

It is the model's own guard (`kvEntryOn`'s `¬ kvGrantedL s.1 (leaseItemsOf (stateAfter s.2.1)) rq`), so the
commit proves it where it proves the old one (§2) and `grantedAt_of_applied` gets it from `authTie` (§3). It is the
old `grantedAt` on every request without a lease part (`grantedAt_plain`, from `leaseGrantedM_of_plainCover`;
`leaseGrantedM` is `True` on the other kinds but put, transaction and revocation), so authkv, auth3 and every closed
theorem (lease mode `none`: every admitted request is `plainCover` or admin) mean what they did. Why: the
clients' refusals of `etcd_authlease_safe`'s checks 2, 3 and 5 rest on the update's `writeGrantG` being refuted at
the commit; for `u`'s `Put(a', WithLease(Lz))` the permission part passes (`a'` is in `[a, b)`), only the lease part
refuses. One proof under `Proof/github_com` reads `grantedAt_iff` (`examples/etcd/auth/WorkAuth.lean:330`,
`akGranted_of_writeGrantG`, `.1` → `grantedAt_kvGranted`): a proof edit, its statement unchanged. Probe:
`kvGrantedL_grant`, `kvGrantedL_iff_plain`.

**Request constructors** (new, `InvProposer.lean` beside `irrPut`): `irrLeaseGrant id ttl := { irrEmpty with
leaseGrant := some ⟨id, ttl⟩ }`, `irrLeaseRevoke id := { irrEmpty with leaseRevoke := some id }` (the requests the
two proofs build inline today).

## 2. The proposal's obligation with auth on (`reqPropOkOn`) and the KV permits

**`reqPropOkOn`'s write disjunct widened** (`ProposeOn.lean:345`; the first, admin and `Authenticate` disjuncts
unchanged):

```lean
-- old
(∃ (op : KVOp) (Q : KVState → IProp GF) (γc : GName) (L₀ : List EntryModel),
  ⌜plainReq (withHeader rq₀ hm) ∧ reqKVOp (withHeader rq₀ hm) = some op ∧
    irrNoZeroEnd (withHeader rq₀ hm) ∧ rqShape .none (withHeader rq₀ hm) ∧
    kvShapeAll (withHeader rq₀ hm) ∧ Qr = grantedRes γk st₀ (withHeader rq₀ hm) γc Q⌝ ∗
  srvReqLogLb γ L₀ ∗ kvAu1G γk (kvOpStep op) (writeGrantG γk st₀ Gb rq₀ L₀) Q)
-- new
(∃ (op : KVOp) (Q : KVState → IProp GF) (γc : GName) (L₀ : List EntryModel),
  ⌜(plainReqL γk.lm (withHeader rq₀ hm) ∨ grantPropOk γk.lm (withHeader rq₀ hm) ∨
      revokePropOk γk.lm (withHeader rq₀ hm)) ∧ reqKVOp (withHeader rq₀ hm) = some op ∧
    irrNoZeroEnd (withHeader rq₀ hm) ∧ rqShape γk.lm (withHeader rq₀ hm) ∧
    kvShapeAll (withHeader rq₀ hm) ∧ Qr = grantedRes γk st₀ (withHeader rq₀ hm) γc Q⌝ ∗
  srvReqLogLb γ L₀ ∗ kvAu1G γk (kvOpStep op) (writeGrantG γk st₀ Gb rq₀ L₀) Q ∗
  grantIdOwn γk (withHeader rq₀ hm))
```

This is F3 as fixed: every grant, revocation, leased put and leased transaction carries its client's update,
fired at most once, as a KV write's (`kvAu1G … (writeGrantG …)`), at `op = .leaseGrant id ttl` (the id the member
fixed before `raftRequest`), `.leaseRevoke id`, `.put o`, `.txn t` (`reqKVOp` gives exactly these). The grant also
hands its id's claim right (`grantIdOwn`, the off form's; `True` for the other kinds and outside the revocable
mode), which `kvGrantIds_snoc` (generic in the log) consumes. At lease mode `none` the new disjunct is the old one
(`plainReqL_none`, `grantPropOk_false`, `revokePropOk_none`, `rqShape` at `.none`, `grantIdOwn_nonRev`).

`kv_prop_au_on`'s write branch (the commit) is unchanged in structure: granted (`grantedAt`, now `kvGrantedL`, which
is exactly `kvModelOn_snoc_granted`'s premise) → the update fires and the state steps by `kvReqStep rq σ = kvOpStep op
σ`; refused → the update is put back (`kvModelOn_snoc_refused` at `authKVKind`; a grant is never refused,
`grantedAt_grant`). New internal lemmas (forms): `commitOkOn_L` (`commitOkOn_plain` at `plainEntryOn`'s three
forms: a revocation's and a grant's `reqPerms` are `[]`, so `kvDet` holds), `entryShapeOn` from `rqShape γk.lm`,
`kvGrantIds_snoc` in place of `_keep` at a grant, `reqPropOkM_true_writeL` (`reqPropOkM_true_write` at the new
disjunct; the old lemma stays, for `plainReq`).

**`putPermitOn`** (`ReqOn.lean:895`):

```lean
-- old
iprop(⌜op.leaseID = W64 0 ∧ op.key ≠ []⌝ ∗ ∃ L₀, srvReqLogLb γ L₀ ∗
  kvAu1G γk (kvOpStep (.put op)) (writeGrantG γk srvAuthSt0 Gb (irrPut op) L₀) Q)
-- new
iprop(⌜(op.leaseID = W64 0 ∨ γk.lm = .revocable) ∧ op.key ≠ []⌝ ∗ ∃ L₀, srvReqLogLb γ L₀ ∗
  kvAu1G γk (kvOpStep (.put op)) (writeGrantG γk srvAuthSt0 Gb (irrPut op) L₀) Q)
```

`putPermitOn_reqPropOk` proves `plainReqL γk.lm (irrPut op)` by `plainReqL`'s right disjunct at a leased put, and
`rqShape γk.lm` (a put's `rqOk` is `putOk`, lease-free). `putPermitM false` (`putPermit`, auth off) is unchanged.

**`txnPermitOn` and `txnPermitM`** (`ReqOn.lean:1114, 1198`), the pure conjunct:

```lean
-- old
⌜txn.txnPlain t ∧ txnNoZeroEnd t ∧ txn.txnShape t⌝
-- new (txnPermitOn)
⌜(txn.txnPlain t ∨ (γk.lm = .revocable ∧ txnPlainL t)) ∧ txnNoZeroEnd t ∧ txn.txnShape t⌝
-- new (txnPermitM on)
⌜(txn.txnPlain t ∨ (on = true ∧ γk.lm = .revocable ∧ txnPlainL t)) ∧ txnNoZeroEnd t ∧ txn.txnShape t⌝
```

(`txnPlainL t = txn.txnLeased t`: plain but for its puts' leases, S3a2.) `txnPermit_of_false` keeps giving the off
`txnPermit` (the new disjunct needs `on = true`); `txnPermitOn_reqPropOk` proves `plainReqL γk.lm (irrTxn tw)` and
`rqShape γk.lm` by a leased `rqShape_of_txn` (`txn.TxnPre_of` needs only `txnShape`).

**The lease permits** (new, `ReqOn.lean`, the shape of `putPermitM`):

```lean
/-- what `LeaseGrant` of TTL `ttl` needs: off nothing (the off `kvInv` holds the whole state when the cluster
grants, no client), on its client's update at whichever id the member fixes -/
def leaseGrantPermitM (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (ttl : w64) (Q : w64 → KVState → IProp GF) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(∀ id : w64, ∃ L₀, srvReqLogLb γ L₀ ∗
      kvAu1G γk (kvOpStep (.leaseGrant id ttl)) (writeGrantG γk srvAuthSt0 Gb (irrLeaseGrant id ttl) L₀) (Q id))

def leaseRevokePermitM (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (id : w64) (Q : KVState → IProp GF) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(∃ L₀, srvReqLogLb γ L₀ ∗
      kvAu1G γk (kvOpStep (.leaseRevoke id)) (writeGrantG γk srvAuthSt0 Gb (irrLeaseRevoke id) L₀) Q)
```

and their results at the stamped header (`grantQhOn γk id ttl γc Q hm L := grantedRes γk srvAuthSt0 (withHeader
(irrLeaseGrant id ttl) hm) γc (Q id) L`, `revokeQhOn` likewise), with `…Permit…_reqPropOk` lemmas (internal), and
the laws a client uses without unfolding (review r1 S3): `leaseGrantPermitM_false`/`leaseRevokePermitM_false`
(`True`, introduction for the off callers), `_true` (the update, elimination), `_mono` (a binding admitting more,
`Gb' ⊢ Gb`: what a gRPC deposit at `hdrBoundT s E.authMode tok` converts by, as `putPermitOn_mono` does in
`putPermitM_of_dep`).

## 3. The tie the apply thread hands the proposer (`authTie`, frozen at S3a2 rev 6)

Two request-side readings need more than S3a2's `authTie`:
- **a revocation's success means it was granted** (§4.3: the client's result `Q` is in `grantedRes`'s left
  disjunct only when granted). `authTie` is guarded by `isKVKind`, which excludes `.leaseRevoke`.
- **a leased put's success means its lease was live** (§4.1): `authTie` says nothing of the lease's liveness, and
  `backendStep` admits an applied put of a dead lease (S3a2 §0); S3a2's lease exactness at the model's table
  (`leaseExactL`) reaches the server's KV arm (`kvOn_after_kv`'s `hout`) but is dropped there.

```lean
-- old (ReqOn.lean:90)
def authTie (st : auth.AuthState) (lb : mvcc.Log) (rq : apply.IRRModel) (out : apply.ApplyOut) : Prop :=
  apply.isKVKind (apply.dispatchKind rq) = true → ∀ o skip, out = .dispatched o skip →
    (o = .rejected .auth ↔ ¬ kvGrantedL st (mvcc.leaseItemsOf (mvcc.stateAfter lb)) rq)
-- new
def authTie (st : auth.AuthState) (lb : mvcc.Log) (lt : LeaseTable) (rq : apply.IRRModel)
    (out : apply.ApplyOut) : Prop :=
  apply.authKVKind (apply.dispatchKind rq) = true → ∀ o skip, out = .dispatched o skip →
    (o = .rejected .auth ↔ ¬ kvGrantedL st (mvcc.leaseItemsOf (mvcc.stateAfter lb)) rq) ∧
    (plainCover rq ∨ apply.leaseExactL lt.ids rq lb o)
```

`lt` is the model's table before the entry, beside `st` and `lb`; the carriers pass it:
- `resultIsWOn E γr rq F ar lb st` → `resultIsWOn E γr rq F ar lb st lt` (its `authTie st lb rq out` → `authTie st lb
  lt rq out`);
- `entryWitOn M ρ rq lb st` → `entryWitOn M ρ rq lb st lt` (its `∃ lt, kvRaftOfOn … (L.take m) = (st, lb, lt)`
  becomes `kvRaftOfOn … (L.take m) = (st, lb, lt)`: the `∃` moves out to `resultΨOn`);
- `resultΨOn`: `∃ ar lb st` → `∃ ar lb st lt`;
- `modelOutM true`: `∃ st lt, kvRaftOfOn … L = (st, lb, lt) ∧ authTie st lb lt rq out`.

The disjunct `plainCover rq ∨ leaseExactL …` is S3a2's `hex` (the frozen `apply_kv_after_on`'s), as the KV arm
has it: at `E.lg = false` the request is `plainCover` (`lm = .none`), at `E.lg = true` the dispatch post gives
`leaseExactL` at the model's table. All internal (`ReqOn`, no `Spec/` text, no `interface/`); in meaning they reach
`processInternalRaftRequestOnce.spec`, `raftRequest.spec` (through `appliedOkM`/`modelOutM`), the admin specs'
`appliedOkM true` posts and `isServerReqM true`'s wait condition (`resultΨM`), where the new tie is vacuous for every
admin kind and stronger for the KV kinds and the revocation (premise and post: the apply thread establishes it, the
proposer reads only the two directions below and S3a2's).

`authTie_of_kvOutL` (`ApplyNormalOn.lean:318`, internal) is restated: it gains `lt` and the premise `hex : ∀ o b,
out = .dispatched o b → plainCover rq ∨ leaseExactL lt.ids rq log o`; `authTie_nonKV` is restated as
`authTie_nonAuthKV` (premise `authKVKind … = false`). The docstrings of `authTie`, `ReqOn.lean`'s header (`:13`,
`:84-89`) and `processInternalRaftRequestOnce.spec` (`:56`, "the model's grant") gain the lease-exact half.

**Alternative weighed (review r1 S5), not chosen:** (c) a model-step tie, "the outcome's log after is the model's
log after the entry" (`o.logAfter lb = (kvEntryOn c₀ ch (st, lb, lt) e).2.1`), which the KV and revocation arms also
prove (`kvOn_after_kv`'s, `revokeOn_after`'s `hmod`). It names only the model, but `authTie` (and `resultIsWOn`,
`modelOutM`) would gain the entry `e`, `c₀` and the chain, a wider threading; (b) gives the same liveness facts
(`leaseExactL`'s put arm for a put, its txn arm, `oc.logAfter log ≠ log → PathsLeaseOk`, for a transaction) and is
S3a2's `hex`, already frozen in `apply_kv_after_on`.

**The apply side** (`EtcdServer__applyEntryNormal.lean`): the KV arm (`:2086`) by `authTie_of_kvOutL` with `hex`
(from `kvOn_after_kv`'s `hout`, which it already has); the revocation arm (`:1914`, today `authTie_nonKV`) by
`authTie_of_kvOutL` at its `HXo'` and `hex` by `leaseExactL`'s `True` at a revocation; the grant and admin arms by
`authTie_nonAuthKV` (`authKVKind … = false`). **The proposer**: `grantedAt_of_applied` at `authKVKind` (a
revocation included) and the new `leaseLive_of_tie` (§4.1).

**Probed** (`Scratch/S3bProbe.lean`, `etc/lean-check.py -a`, no `sorry`, axioms `propext`/`Classical.choice`/
`Quot.sound`): `authTieB` (the new text), `authTieB_of_kvOutL` (the apply side, from `kvGrantedL_of_kvOutL` and
`hex`), `hex_revoke`, `authTieB_nonAuthKV`, `kvGrantedL_of_tieB` (applied ⇒ granted at any `authKVKind`),
`leaseLive_of_tieB` (an applied put through any chain had its lease live at `lt`: the backend's applied put commits
one change, `leaseExactL`'s dead-lease arm keeps the log; `chainStep_applied_false` restated from v3rpc's
`ClientModel`), `kvGrantedL_grant`, `kvGrantedL_iff_plain`.

## 4. The entry points and their answers

### 4.1 `EtcdServer.Put.spec` (frozen `Spec/` text)

Pre unchanged in text (`putPermitM E.authOn …`, whose on body admits a lease at the revocable mode, §2). The
success post's client result gains the lease's liveness:

```lean
-- old
(∃ lt, ⌜E.authOn = false ∨ ρ.kv.lm = .none → lt = []⌝ ∗ Q (kvStateOf x.log lt))
-- new
(∃ lt, ⌜(E.authOn = false ∨ ρ.kv.lm = .none → lt = []) ∧ ¬ (kvStateOf x.log lt).leaseMissing op.leaseID⌝ ∗
  Q (kvStateOf x.log lt))
```

So the state the update fired at is one where the put commits (`kvOpStep (.put op) σ` is not the
`leaseMissing` identity). Off: `op.leaseID = 0` (`putPermit`), `leaseMissing_zero`. On: `leaseLive_of_tie` at
`modelOutM`'s `lt` (= `kvLeasesOn γk st₀ L`, the table `putQhOn_res` already returns). Why it is needed:
`etcd_authlease_safe`'s set-up puts `z` with `Lz` and `a` with `Lu`; check 3's refusal of `u`'s `Revoke(Lz)` and
root's `Get(z)` finding `z` rest on `z` being attached, which the client learns only from this conjunct. The
docstring gains one sentence, and its "`putPermitM`: off, the lease `0` …; on, also the key not empty" (`:29-32`)
is restated (on: the key not empty, the lease `0` or the mode revocable). `putQhOn_res`/`grantedRes_applied` are
restated to return the table `kvLeasesOn γk srvAuthSt0 L` (they return `∃ lt` today). Consumers destructuring the pure
conjunct (proof edits): `EtcdServer__Put.lean`, v3rpc `ServerKVOn.lean`, `examples/etcd/restart1/put.lean` (a closed
theorem's proof; its statement unchanged). `Results.lean:451`'s exported `put_applied : EtcdServer.Put.spec` changes
with it (§6; its docstring `:430-437` gains the sentence).

### 4.2 `EtcdServer.LeaseGrant.spec` (frozen `Spec/` text)

```lean
-- old
∀ (s E ρ ctx cd r) (ttl id0 : w64),
  srvGrantsLeases E ρ → (ρ.rd.kv.lm = .revocable → id0 = W64 0) →
  {{ isPkgInit … ∗ isServerReq s E ρ ∗ srvAuthAt s E ∗ srvLeadTimeReader s ∗ E.RD ∗ □ (|==> idCred ρ.ids 1) ∗
      context.isContext ctx cd ∗ context.libCtxOk ctx ∗ trace.spanCtxOk ctx ∗ context.startTimeOk ctx ∗
      leaseGrantReqOwn r ttl id0 }}
    s.LeaseGrant(ctx, r)
  {{ resp err, RET (resp, err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = nil ∧ resp ≠ null⌝ ∗ leaseGrantedResp E resp ttl) ∨
       (⌜resp = null ∧ err ≠ nil⌝ ∗ applyErrIs err)) }}
-- new
∀ (s E ρ ctx cd r) (ttl id0 : w64) (Q : w64 → KVState → IProp GF),
  {{ isPkgInit … ∗ ⌜srvGrantsLeases E ρ ∧ (ρ.rd.kv.lm = .revocable → id0 = W64 0)⌝ ∗ isServerReqM E.authOn s E ρ ∗ srvAuthAt s E ∗ srvLeadTimeReader s ∗ E.RD ∗
      □ (|==> idCred ρ.ids 1) ∗ context.isContext ctx cd ∗ context.libCtxOk ctx ∗ trace.spanCtxOk ctx ∗
      context.startTimeOk ctx ∗ leaseGrantReqOwn r ttl id0 ∗
      leaseGrantPermitM E.authOn ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) ttl Q }}
    s.LeaseGrant(ctx, r)
  {{ resp err, RET (resp, err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = nil ∧ resp ≠ null⌝ ∗ leaseGrantedResp E resp ttl ∗
          authedOutB s E.authMode (GoInterface.ok ctx) GoInterface.nil ∗ leaseGrantResM E.authOn s E ρ ctx ttl resp Q) ∨
       (⌜resp = null ∧ err ≠ nil⌝ ∗ applyErrIs err)) }}
-- with (new)
def leaseGrantResM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk) (ttl : w64) (resp : Loc)
    (Q : w64 → KVState → IProp GF) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(∃ (id : w64) (hm : apply.HeaderModel) (L : List EntryModel),
      structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗ hdrBoundM true s E (GoInterface.ok ctx) hm ∗
      pubAfterM true E ρ (apply.withHeader (irrLeaseGrant id ttl) hm) L ∗
      Q id (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)))
```

`pubAfterM` ties the header `hm`, the id and the prefix `L`: the committed log
holds, after `L`, the entry of the grant of `id` stamped with `hm` (review r1 S1: without it `hm` was bound to
nothing). The response's `ID` is also `leaseGrantedResp`'s; the two agree by the persistent points-to's agreement
(`icombine … gives`), no new law. Laws: `leaseGrantResM_false` (drop), `_true`.

- `isServerReq` → `isServerReqM E.authOn`, and `authedOutB` on success (`requireAuthInfo`'s, `v3_server.go:447`, at
  the span's context, carried to `ctx` by `principalBound_ctx`): the Scope's §2.3 Draft. `authedOutB` is what refuses
  check 1's token-less and invalid-token grants (a grant has no permission and no lease check at apply, so the model
  grants it to anyone: `grantedAt_grant`), with the client refuting `principalBound`'s TLS disjunct as authkv does
  (`□ (srvTLSId s -∗ False)`, `WorkAuth.lean:316`).
- The pure premises move into the precondition (review r1 S2, "convert one when you change it"); the callers
  (`lessor*_of_server`, a one-line `ipureintro`).
- Docstring: "`requireAuthInfo` returns `nil` with auth off" and the auth-off scope sentences are restated.
- The client's update (F3) at the id the member fixes (`∀ id`: the generated id is not known to the caller); its
  result `Q id` at the state of the committed prefix `L` before the entry, with the response's `ID` the update's
  id. A grant is never refused by the model, so its update always fires at the commit.
- The proof: the id loop as today; `requireAuthInfo` may now fail (auth on: return its error, `applyErrIs` from
  `authedOutB`); `raftRequest` at `reqPropOkM E.authOn` (on: §2's write disjunct at `.leaseGrant i ttl` with
  `grantIdOwn` from the loop's claim right, exactly the off proof's); the answer from `appliedOkM`'s `grantAnsM`
  (mode-generic, as today), `Q` from `grantQhOn`'s left disjunct (`grantedAt_grant`).

### 4.3 `EtcdServer.LeaseRevoke.spec` (frozen `Spec/` text)

```lean
-- old
∀ (s E ρ ctx cd r) (id : w64),
  srvRevokesLeases E ρ →
  {{ isPkgInit … ∗ isServerReq s E ρ ∗ srvAuthAt s E ∗ srvLeadTimeReader s ∗ E.RD ∗ □ (|==> idCred ρ.ids 1) ∗
      context.isContext ctx cd ∗ context.libCtxOk ctx ∗ trace.spanCtxOk ctx ∗ context.startTimeOk ctx ∗
      leaseRevokeReqRO r id }}
    s.LeaseRevoke(ctx, r)
  {{ resp err, RET (resp, err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = nil ∧ resp ≠ null⌝ ∗ leaseRevokedResp E resp) ∨ (⌜resp = null ∧ err ≠ nil⌝ ∗ applyErrIs err)) }}
-- new
∀ (s E ρ ctx cd r) (id : w64) (Q : KVState → IProp GF),
  {{ … ⌜srvRevokesLeases E ρ⌝ ∗ isServerReqM E.authOn s E ρ … ∗ leaseRevokeReqRO r id ∗
      leaseRevokePermitM E.authOn ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) id Q }}
    s.LeaseRevoke(ctx, r)
  {{ resp err, RET (resp, err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = nil ∧ resp ≠ null⌝ ∗ leaseRevokedResp E resp ∗
          authedOutB s E.authMode (GoInterface.ok ctx) GoInterface.nil ∗ leaseRevokeResM E.authOn s E ρ ctx id Q) ∨
       (⌜resp = null ∧ err ≠ nil⌝ ∗ applyErrIs err)) }}
-- with (new; the Scope's `revokeGrantOn`, in `Put.spec`'s shape)
def leaseRevokeResM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk) (id : w64)
    (Q : KVState → IProp GF) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(∃ (hm : apply.HeaderModel) (L : List EntryModel),
      hdrBoundM true s E (GoInterface.ok ctx) hm ∗
      ⌜grantedAt ρ.kv srvAuthSt0 (apply.withHeader (irrLeaseRevoke id) hm) L⌝ ∗
      pubAfterM true E ρ (apply.withHeader (irrLeaseRevoke id) hm) L ∗
      Q (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)))
```

- The success means the auth layer let it through (`authTie` at `authKVKind`, §3: a successful revocation's
  dispatched outcome is not `.rejected .auth`, whose answer is the auth error), so `grantedAt` (`leaseOk` of the
  header's principal on every key the lease holds, at the state the entry met) and the client's result.
- Proof: as the off one, plus the on case of `raftRequest` (`revokeQhOn`), `revokeAnsM` (mode-generic); the
  success's outcome is not the auth rejection because `appliedOkM`'s `dispatchAnswer … GoInterface.nil … o` is, at a
  revocation, `revokeOutcomeIs r nil o`, whose `.rejected .auth` case needs `err ≠ nil` (`apply/Chain.lean:1446`).
- The pure premise in the precondition (S2); laws `leaseRevokeResM_false`, `_true`; docstring as `LeaseGrant`'s.
- Margin (review r1 S6): the success does not say the lease was live at `σ` (Go's success implies the lessor found it,
  `lessor.Revoke` returns `ErrLeaseNotFound` otherwise; the model's revocation of a non-live id commits nothing,
  `keysLeasesLive`). No check reads it (D5); the docstring says so.

### 4.4 Errors, `ErrLeaseNotFound` included; `EtcdServer.Txn.spec`

- A leased put whose lease is not live at apply: the model's step is `leaseMissing`'s identity (the update fires,
  the state unchanged), the backend rejects (`.rejected .backend`, `ErrLeaseNotFound`), and `Put` returns the error
  branch (`appliedErr`, at a header bound to the context), with `applyErrIs` (the gRPC layer maps it, `togRPCError`).
  A revocation of a lease not live: `ErrLeaseNotFound` from the lessor, the same branch. **No client result on the
  error branch** (today's shape for every error): the client's `Q` of the missing-lease state stays in its `kvRes`.
  `etcd_authlease_safe` counts any error as a refusal and ends `Failed` on an allowed call's error, so it needs none
  (decision D4).
- `EtcdServer.Txn.spec`: text unchanged; its writing case's pre (`txnPermitM E.authOn`) admits leased puts at the
  revocable mode (§2), its post's `grantedAt` means `kvGrantedL` (§1). No liveness conjunct for a leased transaction:
  no check of the theorem reads one (check 2 refuses a leased transaction; it never succeeds). A margin (§6).

## 5. Callers

- v3rpc `ServerLeaseGrant`, `ServerLeaseRevoke`, v3rpc `Results` (`lessor*_of_server`, `lessor*_server`): they hold
  `isServerReq` (auth off). Proof edits only: `isServerReqM_false` after `isServerReq_authOn`, the off permits `True`,
  the off results dropped. Texts unchanged.
- v3rpc `ServerKVOn` (`putPermitM_of_dep`, `txnPermitM_of_dep`, the Put/Txn handlers): the new pure parts by their
  left disjuncts (lease `0`, `txnPlain`); the Put post's extra conjunct dropped. Texts unchanged.
- `EtcdServer__revokeExpiredLeases.lean:71`, etcdstart `ServedLease.lean:263, 321`, `examples/etcd/auth/WorkAuth.lean:330`,
  `examples/etcd/restart1/put.lean`: proof edits (§1, §4.1). Statements unchanged.
- Docstrings that the changes make false, restated (review r1 S4): `Spec/…/EtcdServer__Put.lean:29-32`,
  `__LeaseGrant.lean`/`__LeaseRevoke.lean` ("auth off" sentences), `LeaseGrant.lean:36-41`, `RevokeCtx.lean:59-63`,
  `ServerLeaseRevoke.lean:4`, `InvLease.lean:147`, `Results.lean:430`, `ReqOn.lean:13, 84-89`,
  `__processInternalRaftRequestOnce.lean:56`, `authStore__WithRoot.lean:34`.
- **D6 (the served registrations at the mode, recommended S3c).** Sketch of the contracts: `lessorGrantOkG`/
  `lessorRevokeOk` (`InvLease.lean:150, 168`) gain, at the mode, the client's deposit in the pre and its result in the
  post, as the KV handlers' `kvDepOwnM`: a lease deposit `leaseDepM on s E ρ tok d` (`d` a grant's `ttl` and `Q : w64 →
  KVState → IProp GF`, or a revocation's `id` and `Q`) giving `leaseGrantPermitM on ρ.raft ρ.kv (hdrBoundT s E.authMode
  tok) ttl Q` (`leaseRevokePermitM` likewise) by `_mono` at `hdrBoundM_tok`, the post gaining `leaseGrantResM`/
  `leaseRevokeResM` at `tok`; `lessor*_of_server` at `isServerReqM E.authOn`; `etcdLeaseServedAt` at
  `etcdModelOfServer E γr E.authOn`. Est. +2–3 days to S3c (the Scope's S3 total unchanged: it was in S3).

## 6. Statements this changes (for the Freeze)

**Text changes, frozen or exported:**

| statement | where | change |
|---|---|---|
| `EtcdServer.Put.spec` | `Spec/…/EtcdServer__Put.lean` | success post: `¬ (kvStateOf x.log lt).leaseMissing op.leaseID` (§4.1) |
| `EtcdServer.LeaseGrant.spec` | `Spec/…/EtcdServer__LeaseGrant.lean` | `isServerReqM E.authOn`, `leaseGrantPermitM`, `∀ Q`; success `authedOutB`, `leaseGrantResM` (§4.2) |
| `EtcdServer.LeaseRevoke.spec` | `Spec/…/EtcdServer__LeaseRevoke.lean` | `isServerReqM E.authOn`, `leaseRevokePermitM`, `∀ Q`; success `authedOutB`, `leaseRevokeResM` (§4.3) |
| `srvGrantsLeases`, `srvRevokesLeases` | `LeaseGrant.lean`, `RevokeCtx.lean` | the auth-off conjunct dropped (§1; the Scope's) |
| `grantedAt`, `grantedAt_iff` | `ProposeOn.lean` | `kvGranted` → `kvGrantedL` at the model's lease items (§1) |
| `reqPropOkOn` | `ProposeOn.lean` | the write disjunct at `plainReqL lm ∨ grantPropOk lm ∨ revokePropOk lm`, `rqShape lm`, `grantIdOwn` (§2; F3) |
| `putPermitOn`; `txnPermitOn`, `txnPermitM` | `ReqOn.lean` | lease `0` → `lease 0 ∨ lm = revocable`; `txnPlain` → `txnPlain ∨ (on ∧ revocable ∧ txnPlainL)` (§2) |
| `authTie` (+ `lt`), `resultIsWOn` (+ `lt`), `entryWitOn` (+ `lt`), `resultΨOn`, `modelOutM` | `ReqOn.lean` | `authKVKind` guard, the lease-exact disjunct, the table threaded (§3; frozen at S3a2 rev 6) |
| `put_applied` (exported) | `Results.lean:451` | its statement is `EtcdServer.Put.spec` by name: the new post conjunct (a text diff of `Results.lean` shows nothing; docstring `:430` updated) |
| `authTie_of_kvOutL`, `authTie_nonKV` → `authTie_nonAuthKV`, `putQhOn_res`, `grantedRes_applied` | `ApplyNormalOn.lean`, `ReqOn.lean` | internal: `lt` and `hex`; the `authKVKind` premise; the table returned (§3, §4.1) |

New: `leaseGrantPermitM`, `leaseRevokePermitM`, `leaseGrantResM`, `leaseRevokeResM` and their `_false`/`_true`/
`_mono` laws, `writeGrantG_granted`, `irrLeaseGrant`,
`irrLeaseRevoke`, `grantQhOn`, `revokeQhOn`, `grantedAt_kvGranted`, `grantedAt_plain`, `grantedAt_grant`,
`leaseLive_of_tie`, `authTie_nonAuthKV` (renaming `authTie_nonKV`), `commitOkOn_L`, `reqPropOkM_true_writeL`, the
permits' `_reqPropOk`/`_mono` lemmas.

**Meaning only (text unchanged):**
- Through `reqPropOkOn` (review r1 F2): the premise `reqPropOkM E.authOn` of `processInternalRaftRequestOnce.spec` and
  `raftRequest.spec` is weaker at `on` (a grant's, a revocation's, a leased put's and a leased transaction's proposal
  admitted at the revocable mode), so both specs are stronger; with them the exported `request_handoff`
  (`Results.lean:447`) and `server_raft_request` (`:2390`), statements by name.
- `deleteRange_applied` (`Results.lean:455`, `DeleteRange.spec` by name): its post's `grantedAt` (stronger at a leased
  kind; a delete has no lease part, so the same).
- Through `putPermitM`/`txnPermitM`: `EtcdServer.Txn.spec` (writing pre weaker at `on ∧ revocable`); v3rpc
  `kvServer.{Put,Txn}` and client `KVServiceOn` rows that carry `putPermitM E.authOn` (their callers pass lease `0`).
- Through `grantedAt`: `writeGrantG` (the client's update is told the lease part too), `grantedRes`, the posts of
  `Put`/`DeleteRange`/`Txn.spec` (stronger), v3rpc `writeGrantOn`, the client's `opGrantT`/served results with auth
  on. At every request without a lease part, the same (`grantedAt_plain`).
- Through `authTie`/`modelOutM`/`resultΨOn`: `appliedOkM true`, `processInternalRaftRequestOnce.spec`,
  `raftRequest.spec`, the admin specs' success posts (`UserAdd`, `RoleAdd`, `AuthEnable`, …: vacuous there),
  `isServerM true`/`isServerReqM true` (the wait's `resultΨM`) and every spec carrying them with auth on (request
  specs, apply specs, `start`, etcdstart's `Serve`, client `client_*_on`), as S3a2 §6 listed for its `authTie`
  change: premise and post, established exactly by the apply thread, read by the proposer.
- Through `srvGrantsLeases`/`srvRevokesLeases`: v3rpc `lessorGrantOkLive_server`, `lessorGrantOkL_server`,
  `lessorRevokeOk_server` (weaker premise, but their `isServerReq` premise keeps auth off: same meaning).

**Not changed in text:** `plainEntryOn`, `plainReqL`, `kvInvOn`, `kvEntryOn`, `outcomeOn`, `writeGrantG`,
`grantedRes`, `kvAu1G`, `putPermit`/`txnPermit` (auth off), `appliedOkM`, `raftRequest.spec`,
`processInternalRaftRequestOnce.spec`, every apply-layer statement (`apply/`), the snapshot path, `NewServer`.

**Closed theorems: none change.** Grep of `Proof/github_com/` (2026-11-15) for every changed name: only proof
bodies mention them (`WorkAuth.lean:330` `grantedAt_iff`; `restart1/put.lean` the Put post; etcdstart
`ServedLease.lean:321` `⟨hlg, Hoff⟩`); no closed statement mentions `grantedAt`, `reqPropOkOn`, `putPermitOn`,
`txnPermitM`, `authTie`, `resultΨOn`, `LeaseGrant.spec`, `LeaseRevoke.spec` or `srvGrantsLeases`. authkv, auth3 and
etcdstart run auth on at lease mode `none`, where every new disjunct is excluded (`plainReqL_none`,
`grantPropOk_false`, `revokePropOk_none`, `putPermitOn`/`txnPermitM`'s new disjuncts need `revocable`) and
`grantedAt` is the old one; every auth-off client goes through `isServerReq`/`putPermit`/`txnPermit`. No
`interface/` file mentions a changed name (grep); no `etc/api` list covers the server or v3rpc (etcdstart's does:
`ServedLease.lean` changes in a proof body only, `gen-interface --check` at the land stop).

**Trust base:** no axiom, `sorry`, opaque or trusted text is added or changed (the one `Spec/…/auth/
authStore__WithRoot.lean` docstring sentence is of a proved spec).

## 7. Decisions asked

- **D1. `authTie` widened** (§3; frozen at S3a2): the `authKVKind` guard and the lease-exact disjunct, the table `lt`
  threaded through `resultIsWOn`/`entryWitOn`/`resultΨOn`/`modelOutM`. Needed by §4.1 and §4.3; probed.
  **Recommended.** (Alternatives: a separate `leaseTie` conjunct in the same carriers, the same threading, two names;
  (c) a model-step tie, §3, a wider threading for the same facts.)
- **D2. `grantedAt` at `kvGrantedL`** (§1): the clients' refusals of checks 2, 3, 5 need the lease part in
  `writeGrantG`. **Recommended.** (Alternative: keep `grantedAt` and give the lease kinds a second
  `writeGrantGL`: two update shapes, `putPermitOn`'s depending on the lease.)
- **D3. `Put.spec`'s success post gains `¬ leaseMissing`** (§4.1; frozen `Spec/`): needed by the set-up's leased puts.
  **Recommended** in S3b (it is the server's answer; S4 only reads it).
- **D4. No client result on the error branch** (§4.4): `ErrLeaseNotFound` stays an `applyErrIs` error. **Recommended**
  (no consumer; a later client spec "ErrLeaseNotFound ⇒ the lease was missing" would add `Q` to `appliedErr`'s
  dispatched-rejection case, a change of `raftRequest.spec`'s error post).
- **D5. Margins**: a grant's success does not say the lease was added (`leaseGrantOk` at `σ`; the client's `Q id σ`
  can only condition on it); a revocation's success does not say the lease was live (review r1 S6); a leased
  transaction's success says nothing of its leases' liveness, although under D1 its proof is as cheap as the put's
  (`leaseExactL`'s txn arm) — left out because no check reads it and `Txn.spec`'s writing post would change text for
  nothing. **Recommended as margins**; S4 adds what its linearizable `Lease.Grant`/`Revoke` specs need, as stronger
  posts.
- **D6. The served lease registrations at the mode** (review r1 F1; Scope §5 puts them in S3): v3rpc's lease handler
  contracts at the mode with the client's deposit and `etcdLeaseServedAt` at `E.authOn`, sketched in §5. **Recommended:
  in S3c** (with the couplings `etcdLeaseServedAt`'s revocable branch needs), +2–3 days there. Alternative: in S3b
  (the handler contracts only; `etcdLeaseServedAt` still waits for S3c).

## 8. Order of work (after the Freeze), estimate 5–8 agent-days

1. Vocabulary: `srvGrantsLeases`/`srvRevokesLeases`, `grantedAt` (+ laws), `irrLeaseGrant`/`irrLeaseRevoke`.
2. `authTie` and its carriers (`ReqOn`), the apply arms (`EtcdServer__applyEntryNormal`: KV, revocation, others),
   `grantedAt_of_applied`, `leaseLive_of_tie` (the probe's).
3. `reqPropOkOn`'s write disjunct, `kv_prop_au_on`'s write branch (`commitOkOn_L`, `kvGrantIds_snoc`),
   `putPermitOn`/`txnPermitOn`/`txnPermitM` and their `_reqPropOk`, the lease permits.
4. `Put.spec` (+ `EtcdServer__Put`), `Txn` (proof), `LeaseGrant.spec`/`LeaseRevoke.spec` and their proofs.
5. Callers (§5), the docstrings listed in §5, `Results` re-check.
6. Land-stop checks: merge lean, full build (flock, 64G), `tcb-report --check`, `gen-interface --check` on every
   `etc/api` list, bounds and mode gates, closed statements unchanged (diff of `Proof/github_com` statements and
   the `Results.lean` closed statements). STATUS, the handoff, status-history.
