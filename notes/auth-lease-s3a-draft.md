# auth-lease S3a Draft: the auth-on model and apply thread with leases

2026-11-15 · branch `auth-lease` · plan `notes/auth-lease-scope.md` §2.3 as revised by etcd-grove-81 on
2026-11-15 (`questions.md`: S3 split into S3a/S3b/S3c, leased puts folded in). Design before plumbing: each
changed definition old → new, the lemmas it moves, what S3b/S3c take from it. Evidence: the S0 probe
(`Scratch/AuthLeaseProbeModel.lean`, the triple-state fold and its `_append`/`_ops`/bridge lemmas, proved), the
survey of the auth-on side's "no lease" dependencies (summarized in `/shared/tmp/auth-lease/s3-scope-gap.md`'s
addendum), S2's apply layer (on lean, `c3da59fa29`).

**Revision 6 (2026-11-15, §14) — FROZEN (etcd-grove-81; the stronger guard `⌜E.authOn = false ∨ γ.kv.lm =
.none → lt = []⌝` in place of `G`'s, wherever §14 writes the guard)**: the Prove step found the auth-on KV results stated at
`kvStateOf log` unprovable with the table in `kvInvOn` (ledger 2026-11-15); etcd-grove-81 decided (A), restating
them at the state with its table. §14 lists every statement that changes; §0–§13 unchanged.

**Revision 5 (2026-11-15) — FROZEN (S3a, decided by etcd-grove-81 after review round 4; no fifth round)**:
round 4's N1 (a) applied (`γr.raft.pre = []` in `srvKVInvsOn`, the table-agreement lemma, §3) and its smaller
points (§0, §3a, §4, §5, §8). The frozen-text changes signed off by etcd-grove-81: `specSnapM`'s `hnl` restated with
`keysLeasesLive` (§5) and `imageLeasesAt`'s mode argument (§4). §5's text is stable from here (restart3 A0 designs
against it).

**Revision 4 (2026-11-15), the S3a Freeze package**: review round 3's F1–F3 and second-tier points applied
(§1 `keysLeasesLive`, §3a the layer posts and `kvOwnAt`'s body, §4 `srvRestRp`/`imageLeasesAt`, §5 `hnl`'s text,
§7, §8); round 3 found the class-track design provable at every layer and no closed statement changed (§12).

**Revision 3 (2026-11-15)**: N1 decided by etcd-grove-81, (ii′): the lease-exact conjunct goes in the class
track's `kvPostF`, proved by the backend's `Put`/`Txn` and passed through the quota, capped and corrupt layers;
`backendStep` unchanged (§3a, §7's class-track list).

**Revision 2 (2026-11-15)**: review round 2's N2–N5 and second-tier points applied (§3, §3a, §5, §6, §7, §8);
N1 (§3a's source of the lease-exact facts: the class track) waits for etcd-grove-81's re-decision (§11).

**Revision 1 (2026-11-15)**, after review round 1 and etcd-grove-81's decisions (F1 (ii), F2 (a), F3 accepted):
new §3a (the lease-exact outcome), §5 rewritten (the snapshot path carries the leases), §2's claims of lease
entries (F3), and the second-tier points (S1–S3, S6).

## 0. What S3a does, and what it leaves

The auth-on KV model (`kvEntryOn`, `kvRaftOfOn`, `kvInvOn`, `outcomeOn`, the apply thread's mode-`on` proofs)
assumes today that no lease exists: it folds at the empty lease table, its log admits no lease request
(`plainEntryOn` → `plainReq` → `plainCover`, lease `0`), and the server is a cluster that grants none
(`srvKVInvsOn`'s `γr.kv.lg = false`). S3a gives the model a lease table, admits at the revocable lease mode
grants, revocations and leased puts (a put or a transaction's puts with a lease), refuses a request the auth
layer refuses including its lease part (S2's `authOutLL`/`txnOutLL`), keeps the clients' half of the KV state
(so the KV results stay meaningful in the revocable mode), and gives `srvRest` the auth-on table. It changes no
request-side statement (S3b: the proposers of grants, revocations and leased puts with auth on) and none of the
four couplings (S3c: `srvGrantGuard`, `lease.bootCfg`, `lease.srvInvAt`, `srvUberOn`; `NewServer`). S3a touches `NewServer`/the alloc proofs only to
prove `srvKVInvsOn`'s new rows (`γr.kv.lm = E.lm`, `γr.raft.pre = []`, review r4). Until S3c a
built auth-on server is still a cluster that grants none, so S3a's new cases are reachable only in the model and
the apply thread's proofs, not yet by a closed theorem: no closed statement changes (authkv and auth3 run the
lease mode `none` with auth on, where every new case is excluded by admission).

## 1. The model (`KVAuthModel.lean`)

**State.** `OnState := auth.AuthState × mvcc.Log × LeaseTable` (the probe's). `kvEntryOn`, `kvRaftOfOn`,
`kvOpOn` change type to it (names kept; the probe's `kvEntryOnL` etc. are these). `kvModelOn γk st₀ L` stays the
log (`.2.1`); new `kvLeasesOn γk st₀ L := (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L).2.2`.

**The step** (the probe's, proved; `kvGrantedL`, `leaseGrantedM`, `leaseOk` as the probe states them, `putsW` =
S2's `apply.txnPutsW`):

```lean
def kvEntryOn (c₀ : w64) (ch : apply.Chain) (s : OnState) (m : EntryModel) : OnState :=
  if m.typ = W32 0 ∧ m.data ≠ [] then
    match apply.irrDecode m.data with
    | some rq =>
      if uint.Z c₀ < uint.Z m.index ∧ apply.needAdminPermission rq = true then (adminNext rq s.1, s.2)
      else if apply.authKVKind (apply.dispatchKind rq) = true ∧
          ¬ kvGrantedL s.1 (mvcc.leaseItemsOf (mvcc.stateAfter s.2.1)) rq then s
      else (s.1, kvEntry c₀ ch s.2.2 s.2.1 m, kvTable c₀ ch s.2.2 m)
    | none => s
  else (s.1, kvEntry c₀ ch s.2.2 s.2.1 m, kvTable c₀ ch s.2.2 m)
```

- The guard is `authKVKind` (S2's, `apply/DispatchKVL.lean`), the ledger's model fix (2026-11-14): a refused
  revocation keeps the table and the log.
- `kvGrantedL st I rq := kvGranted st rq ∧ leaseGrantedM st I rq`; `leaseOk`'s three disjuncts are
  `leasePassedL`'s at one state (auth disabled is in `adminOk`; the admin case has no revision check, Scope E5;
  a lease attaching no key passes for any principal).
- A grant is never refused by the auth layer (no `authApplierV3.LeaseGrant`): `leaseGrantedM`'s `_ => True`.
- **Moved lemmas** (the 122 declarations mentioning the fold): `s.2` → `s.2.1` for the log, the table threaded.
  The probe proves `_append`, `_above`, `_filler`, `_emptyV2`, `_ops`; its bridge (`kvEntryOnL_fst_snd`) holds
  only at the empty table with no revocation, i.e. at the lease mode `none` (review r1 S2), so it ports the
  lemmas authkv/auth3 use, not the revocable mode's: there each lemma is restated over the table (the
  off model's lemmas, `kvTable_*`, `KVLemmas.lean`, are the pattern). Not mechanical; budgeted in S3a's estimate.
  `kvEntryOn_of_refused` takes `authKVKind` and `¬ kvGrantedL`; `kvEntryOn_of_granted` the table.

**Admission** (`plainEntryOn`, now at the lease mode):

```lean
def plainEntryOn (lm : lease.Mode) (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    ((plainReqL lm rq ∧ noZeroEnds rq ∧ kvShapeAll rq) ∨ grantPropOk lm rq ∨ revokePropOk lm rq) ∨
      (apply.adminKindOk rq ∧ apply.noSideEffect rq = false)
def plainLogOn (lm : lease.Mode) (A : List EntryModel) : Prop := ∀ m ∈ A, plainEntryOn lm m
```

- `grantPropOk`/`revokePropOk` are the off model's (`KVModelDefs.lean:169,176`: a grant at `lm ≠ none`, a
  revocation at `revocable`).
- **New `plainReqL lm rq`**: `plainReq rq`, or at `lm = .revocable` a put or a transaction as `plainCover` but a
  put's lease any id and a transaction plain but for its puts' leases (`txnPlainL`: gets at revision `0`, no
  `IgnoreLease`, `IgnoreValue` as today; a put's lease free). `plainReqL .none = plainReq` (a lemma), so authkv's
  and auth3's logs are what they were.
- `entryShapeOn lm`: `rqShape lm rq ∨ adminKindOk rq` (the off shape at the mode; `rqShape .none` as today).
- `entryDetOn`: `isKVKind` → `authKVKind` (the second place of the guard); `kvDet` unchanged (a revocation needs
  no permission of its own; its lease's keys' shape comes from the key invariant below).

**The keys' invariant** (S2 Draft §7, review r1 M3/r2; derived, not a conjunct of `kvInvOn`: a lemma of
`plainLogOn lm L` and `LogNoLease γk.log0`, through `txn = txnW.toModel` for a transaction's puts, review r1 S3):
`keysNonEmpty l := ∀ k id, mvcc.leaseItemsOf
(mvcc.stateAfter l) !! ⟨k⟩ = some id → k ≠ []`, kept by every entry of a `plainLogOn lm` log (a put's key is a
point key of the cache's shape, `kvShapeAll`; a revocation deletes; a grant writes nothing), true of a start
log with no lease (`mvcc.LogNoLease γk.log0`, as the off `kvInv` has). It gives `leaseShapedL` at every lease,
which S2's checks take (`kvShapedL`'s lease parts).

**The keys' leases are live** (review r2 N3, r3 F3; derived like `keysNonEmpty`, a lemma of `plainLogOn lm L`):
`keysLeasesLive (s : OnState) := ∀ k id, mvcc.leaseItemsOf (mvcc.stateAfter s.2.1) !! ⟨k⟩ = some id → id ∈ s.2.2.ids`
(a leased put applies only at a live lease, `leaseMissingIn`; a revocation deletes its keys and drops its id; a
refused one changes neither; a grant adds an id), true of a start log with no lease. It gives `outcomeOn` on a
revocation of a non-live id (no key, so `revokeLog` commits nothing) and, at the image, `Restore`'s premise (§5).

## 2. The KV invariant (`kvInvOn`)

```lean
def kvInvOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) : IProp GF :=
  inv kvN iprop(∃ L : List EntryModel,
    srvRLog γ L ∗
    ghostVar γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ L) (kvLeasesOn γk st₀ L)) ∗
    monoListAuthOwn γk.hist (1 : Qp).half (admStates γk st₀ L) ∗
    ⌜plainLogOn γk.lm L ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0, []) L ∧ srvIdxOkW γ.ai0 L ∧
      uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧ γk.ch0 = apply.alarmChain true false false ∧
      (γk.log0 ≠ [] ∧ mvcc.LogNoLease γk.log0) ∧ γ.raft.authOn = true ∧ kvLogSmall γk L⌝ ∗
    kvWorkOn γ.raft γk L ∗ kvGrantIds γk L)
```

- **The clients' half is kept** (`(1 : Qp).half` whatever the mode), unlike the off `kvInv`'s `kvStQ` (the whole
  variable at `γk.lg`: the off grant proposer fires no client update, the lease-grant plan's (C)). With auth on
  every committed lease request will carry its client's update (S3b: a grant's `kvOpStep (.leaseGrant id ttl)`,
  a revocation's `kvOpStep (.leaseRevoke id)`, a leased put's `kvOpStep (.put op)`), and no lease expires during
  the run (`lease.leasesNoExpiry`, Q2; S3c makes the expiry arm dead with auth on), so no step of the state is
  without a client. This is what keeps `etcdKV` and the KV results meaningful in the revocable mode
  (the survey's blocker 2).
- **What a lease entry's claim carries** (F3, accepted; S3b's obligation, a fixed statement): the proposal of
  a grant, a revocation or a leased put carries its client's update, fired at most once, as a KV write's
  (`kvAu1G γk (kvOpStep op) (writeGrantG …) Q`, `reqPropOkOn`'s second disjunct): `op = .leaseGrant id ttl` (the id
  the member fixed before `raftRequest`), `.leaseRevoke id`, `.put o` with `o.leaseID ≠ 0`, and a leased
  transaction's the existing `kvOpStep (.txn t)`. `reqPropOkOn` gains
  these at the revocable mode (S3b states it; S3a's `kvInvOn_commit_granted` consumes it, restated over
  `kvOpStep`'s lease arms, `KVModelDefs.lean:1096-1113`). S4: linearizable client specs of `Lease.Grant`/`Revoke`
  that fire them (accepted).
- The state now carries the table (`kvStateOf … (kvLeasesOn …)`), as the off `kvModelSt`.
- `kvGrantIds γk L` (the off one, generic in the log; lease-mono3 step 2's per-member prefixes) gives a grant's
  id freshness, as the off apply arm uses it.
- `mvcc.LogNoLease γk.log0` (the start log attaches no key): the keys' invariant's base; established at a first
  start as the off `kvInv_alloc` does; at a restart the auth-on snapshot path's lease-free premise (§5).
- Laws moved: `kvInvOn_alloc` (exported: `server_cluster_alloc_on`, `server_member_alloc_on`; `kvInvOn` appears
  in the etcdstart interface `Alloc3On.txt`, an interface diff reviewed at the Freeze), `kv_log_plain_on`,
  `kvInvOn_facts_snoc`, `kvInvOn_commit_granted`, `kvInvOn_keysA`, `kvInvOn_congr`.

## 3. The apply thread's model (`KVApplyOn`, `KVOutcomeOn`, `ApplyNormalOn`, `ApplyEntryOn`, `KVReadOn`)

- `outcomeOn` (`KVApplyOn.lean:45`): over `OnState`, the guard `authKVKind ∧ ¬ kvGrantedL …` (the third place),
  the write `(s.1, kvEntry c₀ ch s.2.2 s.2.1 m, kvTable c₀ ch s.2.2 m)`; `outcomeOn_eq` as today.
- `kvAppliedLOn`/`kvAppliedOn`: `s : OnState`; `kvAppliedOn γ γk st₀ A x st lt` with the table `lt`.
- **`authOutL_of_kvOutL`, `authTie_of_kvOutL`, `kvShapedL_of_log`** (S2's, over `plainCover`): replaced by their
  lease forms: `kvOutL` (S2) at the latest state `stl` of `hs` is the model's verdict `kvGrantedL stl I rq`
  (`KVAuthBridge`'s new `leaseOk_iff`: `leaseOk stl a I id ↔ leasePassedL` at `stl`, and its refusal, given the
  keys' shape), at `I = leaseItemsOf (stateAfter x.log)`, for every admitted kind (`plainReqL`, a revocation);
  `kvShapedL_of_log` from `kvShapeAll` and the keys' invariant. `plainCover` leaves these statements
  (`kv_outcome_on_latest`, `apply_kv_entry_pre_on`, `apply_kv_after_on`, `server_apply_not_nospace_on`, exported
  in `Results.lean`, restated at `plainReqL`/the admission).
- `kvRaftOfOn_keys`, `kvModelOn_snoc_granted`, `outcomeOn_of_authOutL`, `outcomeOn_of_kvOutL`, `kvOn_after_kv`,
  `kv_certPreW_on`, `kv_certPreVW_on`, `kv_entry_pre_on`, `kvEntryOn_below/_len/_keep/_nodata/_cc`,
  `applyStep_keep`, `kv_certPre_keep`: the table threaded; their `plainCover` premise → the admission.
- `entryOkOn` (`ApplyNormalOn.lean:48`): `apply.rqOk .none x.log rq` → `apply.rqOk lm x.log rq` (`entryOkM on lm`
  passes the mode it already has); a grant at `lm ≠ none`, a revocation at `revocable`.
- `srvKVInvsOn` (`KVApplyOn.lean:333`): `γr.kv.lg = false` → `γr.kv.lm = E.lm` (keeps `γr.kv.cmp = false`):
  the tie of the model's mode (admission at `γk.lm`) to the environment's (`entryOkM`, `logShapeM` at `E.lm`, the
  `ltHalf` tie at `E.lg`), as the off `srvKVInvs` has (`InvApplier.lean:375`; review r2 N5); and (review r4 N1
  (a)) `γr.raft.pre = []` (the starts prove it, as `applyAll.spec`'s and `specSnapM`'s `hpre0`), with the bridge
  lemma `appliedTableM_eq_model : γr.raft.pre = [] → (appliedTableM true γr A).ids = (kvRaftOfOn γr.kv.c0
  γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) A).2.2.ids`: the model's table (over `A`) and `srvRest`'s (over
  `pre ++ A`) agree. This ties the auth-on server to fresh starts (an auth-on restart, future work, revisits it).

## 3a. The lease-exact outcome of a leased put or transaction (F1 (ii))

S2's `backendStep` (`apply/Chain.lean:209-231`, not changed) lets a put with a lease be rejected whatever the
lease and a transaction be applied without `PathsLeaseOk`; the model (`backendLog`, `KVModelDefs.lean:344-361`)
is exact. The latest track's posts gain the missing fact, against the lessor's live set before the request:

```lean
/-- the apply-level lease exactness of a put's / a transaction's outcome at the live set `ids` -/
def apply.leaseExactL (ids : List w64) (rq : IRRModel) (log : mvcc.Log) (oc : Outcome) : Prop :=
  match dispatchKind rq with
  | .put => ∀ op, rq.put = some op →
      ((op.leaseID ≠ W64 0 ∧ op.leaseID ∉ ids) → oc.logAfter log = log) ∧
      (oc = .rejected .backend → (op.leaseID ≠ W64 0 ∧ op.leaseID ∉ ids) ∨
        (txn.needsPrev op = true ∧ mvcc.findKey op.key (mvcc.stateAfter log) = none))
  | .txn => ∀ t, rq.txn = some t →
      let br := t.branch (txn.txnOk (mvcc.stateAfter log) t)
      (oc.logAfter log ≠ log → txn.PathsLeaseOk (mvcc.stateAfter log) ids br) ∧
      (txn.txnLeased t → oc = .rejected .backend → ¬ (txn.PathsIgnOk (mvcc.stateAfter log) br ∧
        txn.PathsLeaseOk (mvcc.stateAfter log) ids br))
  | _ => True
```

(Review r2 N2: the rejection arm guarded by `txn.txnLeased`, as `checkTxn.spec`/`Txn.specSole` are
(`Spec/…/txn/Txn.lean:72-82`): `checkTxn` also rejects a get at a nonzero revision and a put with `IgnoreLease`
and a dead lease, where both `PathsIgnOk` and `PathsLeaseOk` hold; a lemma `txnPlainL t → txnLeased t`. The put arm
is right as stated and, with `kvOutL`, determines `backendLog` in every case, `needsPrev` included.)

- `kvOwn`'s body stays; new `kvOwnAt E log L := (∃ c, wSt E.γs log c) ∗ kvBk E ∗ (txn.leasesKnown L
  (stateAfter log) ∗ lessorUser (mvccLeases E.γ) L (leaseItemsOf (stateAfter log)) ∗ ltHalf E L) ∗ E.RD`
  (`kvOwn`'s with `leasesLive`'s live set exposed; review r3: all four parts, or the law is false) with the law `kvOwn E log ⊣⊢ ∃ L, kvOwnAt E log L` (review r2: `kvOwn_rd`,
  `kvOwn_lend` and the ~30 unfoldings of `kvOwn` stay; `mPreRest_lend` unfolds `leasesLive`, unaffected). `L` is
  the live set after the request, tied to the one before only through `ltHalf` when `E.lg` (a put, a transaction
  and a delete keep it); at `E.lg = false` unconstrained, harmless at the mode `none` (review r3). `kvPostFL` gains `∃ L, ⌜apply.leaseExactL L rq log oc⌝ ∗
  kvOwnAt E (oc.logAfter log) L` in place of its `kvOwn E (oc.logAfter log)` (a put or a transaction leaves the
  live set as it was). `ltHalf E L` ties `L` to `srvRest`'s auth-on table (§4).
- **Where it comes from (N1, (ii′)):** the class track's `kvPostF` (`apply/Chain.lean:1629`) gets the same
  conjunct: its `kvOwn E (oc.logAfter log)` becomes `∃ L, ⌜apply.leaseExactL L rq log oc⌝ ∗ kvOwnAt E
  (oc.logAfter log) L`. The backend's `Put`/`Txn` prove it (`txn.Put.spec`'s and `checkLease.spec`'s exactness in
  the live set, `applierV3backend__Put.lean:97-170`; the txn specs, lease-exact for `txnLeased` transactions,
  review r2), `DeleteRange` trivially (`leaseExactL`'s `_ => True`, the live set kept); the quota, capped and
  corrupt layers pass it through (their rejections leave the log, `leaseExactL`'s put arm holds of a log kept,
  the txn arm's applied case is vacuous); the auth layer's latest triples lift it (`auth_pass_kvPostFL` keeps the
  conjunct; `auth_reject_kvPostFL`'s rejection: `.rejected .auth`, the log kept). `backendStep` is unchanged.
- Changes to S2's latest statements (a Freeze item): `kvPostFL`'s body, `apply.kvOwn`'s split (`kvOwnAt`, its
  laws `kvOwn_lend`, `kvOwn_rd`, `mPreRest_lend` restated), the latest triples' posts through `kvPostFL`
  (`Put`/`Txn`/`DeleteRange`/`LeaseRevoke.specL`, `applierKVL`, the four layer triples); the class track and
  `Chain.lean`'s `backendStep` untouched.
- **Text vs meaning (review r4):** the posts whose text changes are the three `kvSpecL`s and `uberKVC`; those whose
  meaning changes through `kvPostFL` are `applierKVL`, `apply_applier_kv_latest`, `auth_pass_kvPostFL_nil`.
- **To the server (review r3 F1):** the three layer triples the auth-on KV branch reads keep only `kvOutL` today
  (`dispatch.wp_kvL` unfolds `kvPostFL`, `DispatchKVL.lean:727-735`). Their posts gain
  `⌜∀ o b, out = .dispatched o b → v3 = true → E.lg = true → apply.leaseExactL T rq x.log o⌝` at the caller's
  `ltHalf E T` (the pre's), proved by `ltHalf`'s agreement (`L = T`): `uberApplier.dispatch.kvSpecL`,
  `uberApplier.Apply.kvSpecL`, `apply.uberKVC`, `apply.Apply.kvSpecL` (exported as `apply_dispatch_kv_latest`,
  `apply_uber_apply_kv_latest`, `apply_apply_kv_latest`, `Results.lean:1789-1808`), and `applierKVL`'s triples;
  `apply_applier_kv_latest` and `auth_pass_kvPostFL_nil` with them.
- With it `kvOutL` + `leaseExactL` at `T = (appliedTableM true γr A).ids` determine `outcomeOn`'s write, so
  `outcomeOn_of_kvOutL` and `kv_outcome_on_latest` hold at `plainReqL`.

## 4. `srvRest`'s table with auth on (`InvRest.lean`, `AppliedTable.lean`)

`appliedTable γr A = kvLeases γr.kv (γr.raft.pre ++ A)` folds the off table, which ignores the auth layer
(`chainTable` passes `.auth` through): with auth on a refused revocation would leave it. New:

```lean
def appliedTableM (on : Bool) (γr : ReadNames) (A : List EntryModel) : LeaseTable :=
  if on then kvLeasesOn γr.kv srvAuthSt0 (γr.raft.pre ++ A) else appliedTable γr A
```

(Review r1 S1: `srvAuthSt0` fixed here, while `srvKVInvsOn` and the on lemmas are generic in `st₀`; every use
that meets `srvRest` instantiates `st₀ := srvAuthSt0` (`kvModelM true`, `KVModelM.lean:56`), so the laws relating
`kvInvOn γ γk st₀` to `srvRest` take `st₀ = srvAuthSt0` as a premise.) `srvRest E γr A` and `srvRestAt`'s callers
use `appliedTableM E.authOn γr A`; `appliedTableM false = appliedTable`
(`rfl`/`if_neg`), so the off proofs are unchanged up to that rewrite. `appliedTableM_snoc` (on): the table one
entry later is `kvEntryOn`'s, which differs from `kvTable` only at a refused revocation (where it keeps the
table, as the lessor does: the auth applier's `checkLeasePuts` refused, the inner `Revoke` never ran). The leased
arm's laws (`srvRest_applyG`, the grant/revoke `restOut_*`, `srvEver_*`) take the auth-on step for `on = true`.

**Also on the auth-on table (review r3 F2):** `srvRestRp` (`ApplyRDefs.lean:64`, in the `applyEntryNormal`,
`applyAll` and `applySnapshot` specs) and `imageLeasesAt` (`ImageLeases.lean:51`, `specSnapM`'s `hlease`,
`EtcdServer__applySnapshot.lean:152`) take the mode and read `appliedTableM E.authOn γr A` (`… false` the off
table, so the off proofs only rewrite); a named lemma `kvLeasesOn_none` (at the lease mode `none` the table is
empty, as `kvTableOf_plainOn` is used today) serves authkv/auth3; without it `hlease` is false of a real auth-on snapshot once the log holds a
refused revocation. The ~18 proof files with `leaseTTLsGeReq (appliedTable …)`-style premises move with them
(the off ones by the rewrite).

## 5. The snapshot path carries the leases (F2 (a))

Raft's no-snapshot mode is gone (`RawNode__Bootstrap.lean:66`, `setupNode.lean:85`: every cluster snapshots), so
the auth-on snapshot path carries the leases, as the auth-off revocable path does. The users of "auth on ⇒ no
lease" and their auth-off pattern:

| auth-on site | today | S3a | auth-off pattern |
|---|---|---|---|
| `srvKVInvsOn` (`KVApplyOn.lean:337`) | `γr.kv.lg = false` | dropped (`cmp = false` kept) | — |
| `ApplyAllSnap.lean:215, 391` (`snapRecv_imageOnR`, `applyAll.wp_proofSnapM`, 933-965) | `lg = false`, `E.lm = .none`, `kvTableOf_plainOn` | the image's table (`appliedTableM true`), the revocable lessor's restored live set | `imageLeasesAt_recs`, `RestLeased.lean:30`, `ImageLeases.lean` |
| `EtcdServer__applySnapshot.lean:122-135, 294` (`srvKVInvsM_lg`, `SnapApplyPost.lean:100`) | `lg = false` | the leased arm of `srvRest` after the install | the off install's leased arm |
| `SnapSendBranch.lean:491, 873` | `lg = false` on the send side | the image's leases sent | `SnapSendBranch.lean:423, 443` (`E.lg`-guarded table) |
| `MergedImageOn.lean:59, 116` | lease-free image | the merged image's table | `StopImage.lean:116` |
| `ImageOn.lean` (`imageRestAtOn`, `dbImageOn`) | `kvTableOf_plainOn`, `crevOf_plainOn` | the image at the auth-on table | `ImageLeases.lean` |
| `SnapRecvOn.lean:43-159, 290, 311, 333` (`kvEntryOn_growsOk`, `restorable`, `SnapImageFactsOn.nolease`, `kvTable_plainOn`, `kvTableOf_plainOn`) | lease-free log | `LogNoLease` replaced by the keys' invariant and the table; `restoreLogOk` with leased keys | `KVModelRestore.lean:234, 272` (off: still `LogNoLease`: the off log has no leased put either; the restore of leased keys is new on both sides) |
| `SnapAuthRecover.lean` (`authRecoverOn.spec`, `plainLogOn A'`) | `plainLogOn` | `plainLogOn lm` | — |
| **`Spec/…/EtcdServer__applySnapshot.lean:119`** (`specSnapM`'s `hnl : LogNoLease (kvModelM E.authOn γr.kv A')`), and its consumers `SnapApplyWalk`, `SnapApplyPost` (`srvSnapApplied_of_walk`), `SnapApplyKV`, `SnapApplyKVLemmas` (`leasesKnown_noLease`) | the model's log attaches no key | **a frozen spec premise restated** (r2 N3, r3 F3): `hnl : if E.authOn then ∀ k id, mvcc.leaseItemsOf (mvcc.stateAfter (kvModelM true γr.kv A')) !! ⟨k⟩ = some id → id ∈ (appliedTableM true γr A').ids else mvcc.LogNoLease (kvModelM false γr.kv A')` (from `keysLeasesLive`); mvcc's `store.Restore.spec` handles leased keys given every pending item's lease in `Recover`'s live set (`store__Restore.lean:156-158`) | none (the off log has no leased put) |
| `snapRecv_imageOn` (`SnapRecvOn.lean:477`) | `E.lg = false` | the image's table | — |
| `srvClusterBootOn_alloc` (`NewServerAllocOn.lean:65`) | `γk.lg = false` | the mode's (`γk.lm`) | `srvClusterBoot_alloc` |

**A new model invariant** (review r2 N3, its proof sketched in the r2 report): `keysLeasesLive (s : OnState)`:
every key the log's state attaches to a lease `id ≠ 0` has `id` in the table's ids (a leased put applies only at a
live lease, `leaseMissingIn`; a revocation deletes its keys and drops its id; a refused revocation changes
neither; a grant adds an id). Distinct from `keysNonEmpty`. It also gives `outcomeOn` on a revocation of a non-live
id (`backendStep` applies `revokeLog` unconditionally, `backendLog` keeps the log; with the invariant, a non-live
id has no key, so `revokeLog` commits nothing).

The off path is **not** a pattern for leased keys (the off log has no leased put, it rests on `LogNoLease`
throughout); it is one for the table and the lessor's records. `Restore`'s key-length bound on restored keys (review r4): derived inside `specSnapM`'s proof from `srvKVInvsOn`
and `srvRLogLb γr.raft A'` (the auth-on key lemma, `ServerOnDefs.lean:293`); no premise. Est. +7–11 agent-days for §5 (revised from +5–8;
S3 26–40 stays the coordinator's figure, at its upper half). Unchecked (r2): whether restored leased keys meet
`Restore`'s key-length bound (a Probe item). No closed theorem's statement changes (authkv and auth3 at the mode
`none` take the same path with an empty table); no premise is added to `etcd_authlease_safe`.

## 6. The mode-`on` apply proofs

- `EtcdServer__applyEntryNormal.wp_proofOn`: the KV branch as today (S2's latest triple, now over the lease
  verdict, its premises from the admission and the keys' invariant, no more `plainCover` discharge); new
  branches for a grant (the general `Apply.spec`, as a cluster request: the off arm's `srvEver_applyPre`,
  `kv_entry_grantFresh`, `grantReqA_of_res`), and a revocation (the latest triple's revocation, S2: `revokeOwn`,
  `ltHalf`, `revokeRestA`; the off arm's `revokeA_drop`, `revokeArM_of_res` for the lessor's side).
- **The revocation's KV side is new work** (review r2 N4): the off arm assumes a revocation deletes nothing
  (`kvEntry_revoke`, `kv_certPre_G`, `batchStep_plainMG` take `LogNoLease`, `ApplyCmpArm.lean:288-300, 367,
  657-668`); with leased puts it commits the lease's keys' deletions, which need the commit's certificate, the
  batch step and the history step for a non-empty commit (S2's backend revoke triple is already general).
- `EtcdServer__apply.wp_proofOn`: the batch's rows at the table (`kvAppliedOn`'s `lt`, `srvRest`'s on table).
- `ModeSpecs.applyEntryNormal.specOn` keeps its `srvLessorNil s` until S3c (unused since S2).
- The KV branch's verdict: `kvOutL` and `leaseExactL` (§3a) at the live set the `ltHalf` ties to
  `appliedTableM E.authOn γr A`.

## 7. Exported statements this changes (for the Freeze)

- Definitions with exported bodies: `kvEntryOn`, `kvRaftOfOn`, `kvOpOn`, `kvModelOn` (type of its fold),
  `plainEntryOn`/`plainLogOn` (new `lm` argument), `entryShapeOn`/`logShapeOn` (at `lm`), `entryDetOn`,
  `kvInvOn`, `outcomeOn`, `kvAppliedLOn`/`kvAppliedOn`, `entryOkOn`, `srvKVInvsOn`, `srvRest` (at
  `appliedTableM`); new `kvGrantedL`, `leaseGrantedM`, `leaseOk`, `kvLeasesOn`, `plainReqL`, `txnPlainL`,
  `keysNonEmpty`, `keysLeasesLive`, `appliedTableM`, `kvOwnAt`, `leaseExactL`.
- `Results.lean` (server): `kv_outcome_on_latest`, `apply_kv_entry_pre_on`, `apply_kv_after_on`,
  `server_apply_not_nospace_on` (premise `plainCover` → the admission), `server_cluster_alloc_on`,
  `server_member_alloc_on` (`kvInvOn`'s body).
- The latest track (§3a): `kvPostFL`'s body, new `apply.kvOwnAt` (with `kvOwn ⊣⊢ ∃ L, kvOwnAt`, `kvOwn`'s body
  kept) and `apply.leaseExactL`; through them the latest triples' posts (S2's statements, re-frozen here).
- **The class track (N1, (ii′)), every statement it changes:**
  - `apply.kvPostF`'s body (`apply/Chain.lean:1629`): `kvOwn E (oc.logAfter log)` → `∃ L, ⌜leaseExactL L rq log oc⌝
    ∗ kvOwnAt E (oc.logAfter log) L`. (`kvPost`, the floor-free post of `LeaseRevoke`, unchanged: a revocation's
    exactness is the model's invariant, §5.)
  - Through it, the meaning (not the text) of the 14 `Spec/` triples whose post is `kvPostF`:
    `applierV3backend.{Put,DeleteRange,Txn}.spec`, `quotaApplierV3.{Put,Txn}.spec`,
    `applierV3Capped.{Put,Txn}.spec`, `applierV3Corrupt.{Put,DeleteRange,Txn}.spec`,
    `authApplierV3.{Put,DeleteRange,Txn}.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/`), and of
    `apply.applierTriples` (`Chain.lean:2005-2023`, the KV clauses), which `applierSpec`, `uberApplier.dispatch.spec`
    and every chain contract read.
  - `apply/Results.lean`'s `chain_put`, `chain_deleteRange`, `chain_txn` (their statements over `kvPostF`; `chain_range`
    unchanged).
  - The proofs re-checked: the 14 triples' proofs, `newQuotaApplierV3`, `newApplierV3Capped`,
    `uberApplier__dispatch` (it unfolds `kvPostF` for the KV kinds), `AuthLemmas` (`auth_pass_kvPostF`,
    `auth_reject_kvPostF`), `kvPostF_backend`, and the server's readers of the dispatch post (the auth-off apply
    arm, which drops the new conjunct).
  - Not in any `interface/` file (no `etc/api` list covers the apply package or the server).
- **Closed statements: none change.** No `examples/` or `Proof/github_com/` file mentions `kvPostF`, `kvPost`,
  `applierTriples` or `kvInvOn`'s body in a statement: the closed theorems (`etcd_*_safe`) are adequacy statements
  over the Go programs' executions, unchanged in text and in meaning; authkv and auth3 run the lease mode `none`.
- The rest specs (§4, r3 F2): `srvRestRp` and `imageLeasesAt` at `appliedTableM E.authOn`, hence the meaning of
  `EtcdServer.applyEntryNormal.spec`, `applyAll.spec`/`specSnapM`, `applySnapshot.specSnapM` (their text unchanged
  but for `imageLeasesAt`'s new mode argument).
- The latest layers (§3a, r3 F1): `uberApplier.dispatch.kvSpecL`, `uberApplier.Apply.kvSpecL`, `apply.uberKVC`,
  `apply.Apply.kvSpecL` gain the `leaseExactL` conjunct; `apply_dispatch_kv_latest`, `apply_uber_apply_kv_latest`,
  `apply_apply_kv_latest`, `apply_applier_kv_latest` restated with them.
- The snapshot path (§5): **`EtcdServer.applySnapshot.specSnapM`'s `LogNoLease` premise** (a `Spec/` statement)
  replaced at auth on by the text in §5's table; the on image predicates (`imageRestAtOn`, `dbImageOn`,
  `SnapImageFactsOn`) at the table. (`applyAll.specSnapM`'s `lg = false` was already removed on 2026-11-05,
  `EtcdServer__applyAll.lean:217`.)
- Interfaces: `interface/…/etcdstart/Alloc3On.txt` (`kvInvOn` in a statement), regenerated and reviewed.
- Specs: `EtcdServer.applySnapshot.specSnapM` (above); otherwise `logShapeM true` → `logShapeOn E.lm` and
  `entryOkM` pass the mode they already take.
- Closed theorems: none (authkv, auth3 at the mode `none`).
- No axiom, no trusted text.

## 8. Order of work (after the Freeze)

0. Probe: `kvOwnAt` against `applierV3backend.Put`'s proof (§3a) (the key-length bound is closed, §5).
1. The model (§1) with the probe's lemmas; the keys' invariant; `KVAuthBridge`'s `leaseOk_iff`.
2. `kvInvOn` (§2) and its alloc; `srvRest`'s `appliedTableM` (§4).
3. The latest track's lease-exact outcome (§3a); the apply thread's model (§3).
4. The snapshot path (§5).
5. The mode-`on` apply proofs (§6), then the examples' proofs on the triple state (`auth/Hist.lean:180-212`,
   `auth/SetupInv.lean:631`, `auth/MainAlloc.lean:80-84`, `auth3/Main.lean:227`; proofs only, `plainLogOn .none`).
   `srvKVInvsOn`'s `γr.kv.lm = E.lm` is proved by the auth-on `NewServer` and alloc proofs in S3a (r3), not S3c.
   Stale comments on the removed `lookupNil` (`DispatchKVL.lean:12, 254`, `AuthApplyLatest.lean:13`,
   `UberKVLBase.lean:8`, `Results.lean:1733`) fixed.
Rebuild: `KVAuthModel` and its importers, about 1500 modules; full builds under the flock.

## 10. Review round 1 (fresh `spec-reviewer`, 2026-11-15, `/shared/tmp/auth-lease/s3a-review-r1.md`): decisions needed

Checked correct: the model's step against the Go auth applier (order, admin without revision, keyless lease,
empty principal, a refused revocation leaving lessor and table); `appliedTableM` = the lessor's live set
(`leasesLive`, `ltHalf`); no closed theorem changes; server-originated steps excluded (expiry by `leasesNoExpiry`,
checkpoints by `rqOk`, a server-picked grant id fixed before `raftRequest`). First-tier findings:

- **F1. The apply layer's outcome of a leased put/txn is not lease-exact.** `backendStep` (`apply/Chain.lean:209-231`)
  lets a put with a lease be rejected whatever the lease and applied with no lease condition (a txn: `PathsIgnOk`,
  not `PathsLeaseOk`), so `kvOutL` admits `.rejected .backend` where the model applies: `kv_outcome_on_latest`
  restated at `plainReqL` would be false. The exact facts exist below (`txn.Put.spec`, `checkLease.spec` exact in
  the live set `L`; `applierV3backend__Put.lean:97-170`). Options: (i) a lease-exact `backendStep` (a core
  definition of `Chain.lean`, every track's statements); (ii) **recommended**: a conjunct of the latest track's
  posts (`kvPostFL`, S2's), the outcome's lease part exact at the live set `L` of `kvOwn`'s `leasesLive` before the
  request, tied to the table by `ltHalf`; a change to S2's just-frozen latest statements (`kvPostFL`'s body, the
  methods' and `applierV3backend.Put/Txn`'s latest posts) — a Freeze item.
- **F2. §5's plan rests on raft's no-snapshot mode, which no cluster has any more** (`RawNode__Bootstrap.lean:66`,
  `setupNode.lean:85` require `reNoSnap = false`; U9: snapshots in every cluster). Neither the row nor the fallback
  works, and §5 missed four users of "auth on ⇒ no lease" (`EtcdServer__applySnapshot.lean:122-135` via
  `srvKVInvsM_lg`; `SnapSendBranch.lean:491, 873`; `MergedImageOn.lean:116`; `ImageOn.lean`'s
  `imageRestAtOn`/`dbImageOn`). auth3's statement covers installs (its run only avoids them). Options: (a)
  **recommended**: carry the leases through the auth-on snapshot path as the auth-off revocable path does
  (`imageLeasesAt_recs`, the image's lease table, the restored keys' invariant), est. +5–8 days; (b) a scope cut,
  stated as a premise of `etcd_authlease_safe` (the run installs and sends no snapshot), a world assumption about
  raft's behaviour that the user would have to accept.
- **F3. The client's claim of a lease entry** must be fixed in S3a: a grant's `kvOpAu1 (.leaseGrant id ttl)`, a
  revocation's `kvOpAu1 (.leaseRevoke id)`, a leased put's `kvOpAu1 (.put op)` (S3b's obligation); and (r1 S5)
  linearizable client specs of `Lease.Grant`/`Revoke` that fire them become a hard S4 dependency (none exist
  today), est. +3–5 days.

Second tier (to apply with the revision): `appliedTableM` generic in `st₀` (S1); the lemma port is not mechanical
beyond `lm = none` (S2); `keysNonEmpty` derived, relying on `txn = txnW.toModel` (S3); check that the txn and
backend specs cover leased transaction puts (S6, uncertain; the `checkTxn` lease path was proved for lease-0
workloads).

## 11. Review round 2 (fresh `spec-reviewer`, `/shared/tmp/auth-lease/s3a-review-r2.md`): N1, decided (ii′)

N2–N5 and the second-tier points are applied above. **N1:** §3a cannot be proved with the class track untouched.
The auth applier's latest `Put`/`Txn` triples reach the inner applier only through `applierSpec` →
`applierTriples` (`apply/AuthApplyLatestPut.lean:104`, `apply/Chain.lean:2005, 2023, 2086`), whose posts are the
class track's `kvPostF` (`Chain.lean:1629-1633`): `backendStep` and a `kvOwn` whose live set is not tied to the
pre's; `auth_pass_kvPostFL` lifts exactly that, so the latest layer has nothing to prove `leaseExactL` from (the
facts are inside `applierV3backend.Put`/`.Txn`'s proofs). Options:

- **(ii′) (recommended):** `kvPostF` gains the same conjunct (`∃ L, ⌜leaseExactL L rq log oc⌝ ∗ kvOwnAt E
  (oc.logAfter log) L`), proved by the backend's `Put`/`Txn` (where the facts are) and passed through the quota,
  capped and corrupt layers' `Put`/`Txn` specs and `kvPost`'s other users (a vacuous `True` for the other kinds).
  A change to the class track's `kvPostF` (lease-keys Part A's frozen vocabulary? `kvPost`/`kvPostF` are in
  `Chain.lean`; their users are the chain's `X.spec`s), but `backendStep` stays.
- (i): `backendStep` takes the live set (`Chain.lean`'s core definition; every track's outcome relation).

Either way the class track changes, which (ii) was chosen to avoid.

## 12. Review round 3 (fresh `spec-reviewer`, `/shared/tmp/auth-lease/s3a-review-r3.md`)

Found correct: the class-track conjunct (N1 (ii′)) provable at every layer (backend `Put`/`Txn` with the live set
in hand, ending in `kvPostF_backend`; quota rebuilding at the same outcome; capped/corrupt rejections keeping the
log; the auth layer's checks before the inner call, `auth.go:65-196`; Go's `checkLease` before `kv.Write`, under
`IgnoreLease` too); §7's class-track list complete for `kvPostF` (the 14 `Spec/` triples); **no closed statement
changes** (none of the changed names in any example's `Results`, `Adequacy*` or `MainLinked`; the only interface
diff `Alloc3On.txt`); N2, N4, N5 resolved. Its first-tier F1 (the conjunct to the server), F2 (`srvRestRp`,
`imageLeasesAt` on the off table) and F3 (`hnl`'s text, `keysLeasesLive`) and its second-tier points are applied
in revision 4 above; no round has reviewed revision 4's fixes yet.

## 13. Review round 4 (fresh `spec-reviewer`, `/shared/tmp/auth-lease/s3a-review-r4.md`): one first-tier finding

Round 3's F1–F3 resolved (the layer posts' conjunct by `ltHalf_agree` at `E.lg`; `srvRestRp` already takes `E`,
`imageLeasesAt` gains the mode, `srvEver` needs no change; `hnl`'s text matches `Restore`'s premise through
`SnapApplyWalk.lean:601-608`/`SnapApplyPost.lean:166`); no closed statement changes. **New N1 (first tier):** §3a's
determination step compares the model's table (folded over `A`, `KVApplyOn.lean:282-285`) with
`appliedTableM true` (folded over `γr.raft.pre ++ A`); they agree only when `γr.raft.pre = []`, which is a premise
of `applyAll.spec` and `specSnapM` (`hpre0`) but not visibly of `applyEntryNormal.spec`, `apply`'s spec or
`srvKVInvsOn`. Options: (a) **recommended**: `γr.raft.pre = []` in `srvKVInvsOn` beside `γr.kv.lm = E.lm` (an
internal definition S3a changes anyway; the starts already prove it), with the bridge lemma `pre = [] →
(appliedTableM true γr A).ids = (kvRaftOfOn … A).2.2.ids`; (b) a premise of the auth-on `applyEntryNormal`/`apply`
specs (frozen `Spec/` text). Second tier (to apply): `hnl`'s key-length bound derivable inside `specSnapM`'s proof
(`ServerOnDefs.lean:293`; closes §8's Probe item); a named lemma that the table is empty at the mode `none`; §0 to
say S3a touches `NewServer` only for the `lm` (and `pre`) tie; §3a to separate text-changing posts from
meaning-changing ones.

## 14. Revision 6 addendum: the KV results at the state with its table (decided (A) by etcd-grove-81)

**Finding** (S3a Prove, ledger 2026-11-15). §2 keeps the clients' half of `kvInvOn`'s variable in every lease mode
and puts the table in its state (`kvStateOf (kvModelOn γk st₀ L) (kvLeasesOn γk st₀ L)`). A client's update
therefore fires at the state with the table (`kvAu1`'s `COMM □ Q σ` at the variable's `σ`), and every result
stated as `Q (kvStateOf log)` (table `[]`) is unprovable once a lease is granted. The off mode proves the same text
by refuting a granting cluster from the client's half (`kvSt_client_lg`: at `γk.lg` the invariant owns the whole
variable, `kvStQ`); §2 removes that refutation with auth on by design. No request-side fact (`isServerReqM true`,
`putPermitM true`, `reqPropOkOn`, `srvReqFieldsAtM`) ties the auth-on mode to `none`. (Review r5 S1: the reader side
keeps the old text provable only through the transitional `γr.kv.lg = false` of `srvKVInvsOn`, which §5's step
removes; the ledger's other option (C), a transitional `lm = none` premise on the request side until S3b, would
have kept the old text and only deferred the change.)

**The restatement.** Wherever an applied write's or a linearizable read's result is handed on, `Q (kvStateOf l)`
becomes `∃ lt, ⌜on = false → lt = []⌝ ∗ Q (kvStateOf l lt)` (`on` the mode the statement is at: `E.authOn` for a
server or v3rpc row, the mode argument of an `…M on` form). Off, the guard gives back the old text (`lt = []`,
from `kvSt_client_lg`, as today); on, `lt` is the model's table at the entry (`kvLeasesOn γk srvAuthSt0 L`), which
the statement does not name (the client's `Q` gets the state it fired at; nothing above reads the table).

**Statements changed, old → new** (text; `G l := ∃ lt, ⌜E.authOn = false → lt = []⌝ ∗ Q (kvStateOf l lt)`):

| statement | file | old | new |
|---|---|---|---|
| `EtcdServer.Put.spec`'s success post | `Spec/…/etcdserver/EtcdServer__Put.lean:63` | `Q (kvStateOf x.log)` | `G x.log` |
| `EtcdServer.DeleteRange.spec`'s success post | `Spec/…/EtcdServer__DeleteRange.lean:59` | `Q (kvStateOf x.log)` | `G x.log` |
| `txnAppliedOk` (`EtcdServer.Txn.spec`'s writing post, by name) | `Proof/…/etcdserver/InvRead.lean:235` | `Q (kvStateOf x.log)` | `G x.log` |
| `putApplied`, `deleteApplied`, `txnAppliedAns` (v3rpc rows) | `Proof/…/api/v3rpc/ServerKV.lean:122, 152, 269` | `Q (kvStateOf x.log)` | `G x.log` |
| `rangeAnsOkM`, `txnReadAnsM` (v3rpc rows, internal; added by etcd-grove-81's decision, 2026-11-15) | `ServerKV.lean:214, 227` | `∃ L, srvRLogLb γr.raft L ∗ ⌜kvModelM on γr.kv L = log⌝ ∗ □ Q L` | the same with `⌜on = true → γr.kv.lm = .none → kvLeasesOn γr.kv srvAuthSt0 L = []⌝` inside the `∃ L` (proved in `ServerKVOn` from `kv_log_plain_on` and `kvLeasesOn_none`, `ReadOn.depQ_leases_none`) |
| `srvRest` with auth on (§4; form decided by etcd-grove-81, 2026-11-15: rev 5's meaning, the import order) | `InvRest.lean`, `ApplyRDefs.lean`, `ImageLeases.lean` | `srvRest E γr A` reading `appliedTableM E.authOn γr A` (§4) | `srvRestT E γr T A` (the table a parameter, `InvRest`; `srvRest = srvRestT … (appliedTable γr A)`, `rfl`) and `srvRestM on E γr A` (`ApplyRDefs`: `srvRest` off, `srvRestT … (appliedTableM true γr A)` on); `srvRestRpM on`, `imageLeasesAtT` likewise; `InvRest` is imported by `KVAuthModel`, so `srvRest` cannot read `kvLeasesOn` |
| `srvRestR`, `imageLeasesAt` and the run rows with auth on (§4, forms decided by the agent at the switch, 2026-11-15, reviewed at checkpoint) | `ApplyRDefs.lean`, `SnapApplyDefs.lean`, `KVModelM.lean`, the five apply specs | `srvRestR`/`srvRestRp`/`srvRest`, `imageLeasesAt` | `srvRestRM on` (`srvRestR` at `srvRestRpM on`/`srvRestM on`), `imageLeasesAtM on` (`imageLeasesAtT … (appliedTableM on …)`), `srvRestM`/`srvRestRpM` moved to `KVModelM`; the specs at `E.authOn` (`applyAll.specBatch` at `C.isOn`, its rows' mode); the start rows at `srvRestM`, from `NewServer`'s `srvRest E γr []` by `srvRestM_nil` (empty prefix) |
| `rangeDepQM on` (v3rpc) | `ServerKV.lean:300` | unchanged text (`□ Q (kvStM on γk L)`); its meaning on through `kvStOn` (below) | — |
| client `putReplied`, `deleteReplied`, `txnReplied` (writing), `rangeReplyOk`, `rangeErrReply`, `txnReplied` (read) | `Proof/…/client/v3/KVService.lean:240, 350, 492, 224, 329, 409` | `Q (kvStateOf x.log)` / `□ Q (kvStateOf log)` | `G x.log` / `∃ lt, ⌜E.authOn = false → lt = []⌝ ∗ □ Q (kvStateOf log lt)` |
| `readQ_of_ansM` (client `Results`) | `client/v3/Results.lean:1039-1046` | `□ Q (kvStateOf log)` | `∃ lt, ⌜on = false → lt = []⌝ ∗ □ Q (kvStateOf log lt)` |
| `client_get_value`, `client_get_value_rev`, `rangeReply_state` (client `Results`, through `rangeReplyOk`) | `client/v3/Results.lean:3422, 3456, 3493` | text unchanged; their proofs destructure `lt` | — |
| `revToken_of_put` (v3rpc `Results`, through `putApplied`) | `api/v3rpc/Results.lean` | text unchanged; meaning through `putApplied` | — |
| `srvKVCoreM_fire` (the watch's read update, review r5 F1) | `Proof/…/etcdserver/ReadOn.lean:488-495` | `∃ C, □ Q (kvStateOf C) ∗ ⌜L <+: C⌝` | `∃ C lt, ⌜on = false → lt = []⌝ ∗ □ Q (kvStateOf C lt) ∗ ⌜L <+: C⌝` |
| `srvKVFacts_fire`, `srvKVFacts_fire0` (client wrappers, r5 F1) | `Proof/…/client/v3/WatchFire.lean:180-185, 205-209` | `∃ C, □ Q (kvStateOf C) …` | `∃ C lt, □ Q (kvStateOf C lt) …` (no guard: `srvKVFacts` hides the mode, `InvWatch.lean:371-375`; the watch's statements already quantify the state, `OnceUpTo.lean:86` reads only `σ.changes`) |
| `kvLogOkTo` (the clients' well-formed state) | `Proof/…/etcdserver/KVLogOk.lean:60` | `σ = kvStateOf σ.log ∧ …` | `σ = kvStateOf σ.log σ.leases ∧ …` (the table free) |
| `kvStOn` (the read deposits' state; moved to `KVAuthModel`, a form already accepted) | `KVAuthModel.lean` | `kvStateOf (kvModelOn γk st₀ L)` | `kvStateOf (kvModelOn γk st₀ L) (kvLeasesOn γk st₀ L)` (must equal `kvInvOn`'s state, which the deposits' firing reads, `ReadOn.lean:666`) |

Through these, the meaning (not the text) of: `EtcdServer.Txn.spec` (writing post), `EtcdServer.Range.spec` and
`EtcdServer.start.spec` (`kvStM E.authOn`), the v3rpc `raftKV`/`kvPutOk`/`kvDeleteOk`/`kvTxnOk` conjuncts and
`srvKVAnsM`, the client's gRPC KV specs (`etcdPutSpec`, `etcdRangeSpec(E)`, `etcdDeleteSpec`, `etcdTxnSpec`,
`kvPutSpec`…`kvTxnSpec`), `etcd_*HandlerM`, `etcd_kv_served`, `client_*_any`, `client_*_end_to_end`; (r5 S3) the
auth-on client results `client_put_on`, `client_range_on`, `client_delete_on`, `client_txn_on` (`ResultsOn.lean:55,
150, 223, 329`) and `KVServiceOn`'s handler premises; `kv.Put.spec`, `kv.Get.spec`, `kv.Delete.spec`,
`txn.Commit.spec` (through `kvLogOk`); etcdstart's `Writer.spec`, `WritesKM` (in `interface/`, text unchanged), the
watch proof (`WatchFire.lean`, `watcher__Watch.lean:54`) and `OnceUpTo` (cache, compactwatch, k8s compactor).
**Proofs to re-check, statements unchanged (r5 S4):** `ReqOn.lean:969, 1000, 1262`, `KVService.lean:1767-1932`,
`kubernetes/Defs.lean:263`, k8s `etcd3/Compact.lean:168-170`, `txnlin/Calls.lean:443-498`,
`partition/WatchWrites.lean:110`, `ClientPutGet.lean:450, 510`, `ServerKVTxn.lean:723`.
Projection lemmas stated at the default table generalize to `{lt}` (a form): `revEvents_kvStateOf`,
`rangeEvents_kvStateOf` (`WatchStateDefs`), `kvStateOf_at_kvs`, `kvStateOf_changesAt`, `kvStateOf_rev_succ`,
`kvStateOf_commit_rev`, `kvLogOk_commit` and the `KVLogOk` lemmas (`kvStateOf_rev`, `kvStateOf_kvs` already are).

**Who relies on a lease-free auth-on state (the check, 2026-11-15).** Grep of `client/v3`, `api/v3rpc`,
`Proof/github_com` and `examples/` for `kvStateOf`, `kvLogOk(To)`, `.leases`, `leaseMissing` and the rows above:
- The readers of a state's table are `kvOpStep`'s `leaseMissing` (`PutThenGet.lean:61, 79`, `KMPut.lean:50`: at a
  put's lease `0`, false at any table) and its transaction case's `PathsLeaseOk` (`KVModelDefs.lean:1105`; its users
  `KMTxn.lean:83`, txnlin's `kvOpStep_txnOf_eq` through `pathsLeaseOk_plain`, accept any table): lease-insensitive
  (r5 S5).
- `kvLogOkTo`'s first conjunct is used only to rewrite a state to its log's for its events/key-values
  (`EtcdModelKV.lean:782`, `auth/Hist.lean:232`, `watch/StateEvents.lean:70, 127`, `KMWatch.lean:184`), all through
  projections that ignore the table: they hold with `σ = kvStateOf σ.log σ.leases`.
- The client's results consume `Q`'s state only through `kvStateOf_rev`/`kvStateOf_kvs`/`revEvents`/`readRev`
  (`ServerKVPut.lean:204, 419`, `ServerKVTxn.lean:654-731`, `ServerKVGet.lean:353`, `ClientPutGet.lean`,
  `client/v3/Results.lean:3441-3516`, `kubernetes/Defs.lean:222-242`): table-insensitive once generalized.
- The auth-on examples' predicates are table-insensitive: `etcd_auth.stateHistOk` (`auth/Hist.lean:86`, over
  `revEvents`), the boot states `kvStateOf (kvModelOn … (bootEntries …))` in `auth/MainAlloc.lean:80-84`,
  `auth3/Main.lean:227`, `etcdstart/Alloc3On.lean:153, 272` (the boot log's table is `[]`, `kvLeasesOn_conf`, so the
  texts stay); `restart1` (auth off: `lt = []` by the guard).
- The off examples (k8s, txnlin, watch, putget…) take the rows at `E.authOn = false`: the guard gives `lt = []`.
No consumer relies on the auth-on state having no leases.

**Closed theorems: none change.** No `Results`, `Adequacy*` or `MainLinked` file under `Proof/github_com/` mentions
any changed name in a statement (`kvStateOf`, `kvLogOk(To)`, `kvStOn`, the v3rpc and client rows, the server specs),
and `examples/` holds Go only; the closed theorems (`etcd_*_safe`) are adequacy statements over the Go programs'
executions. The `interface/` files: none covers `client/v3`, v3rpc or the server (`etc/api`), so no new interface
diff beyond §7's `Alloc3On.txt`.

**The guard (r5 S2), decided by etcd-grove-81 (2026-11-15): the stronger one; §14 approved as the rev-6 freeze.** `E.authOn = false → lt = []` tells the auth-on clients nothing,
though authkv/auth3/etcdstart run the lease mode `none`, where the table is empty. `⌜E.authOn = false ∨ γ.kv.lm =
.none → lt = []⌝` keeps their exact old meaning (provable from `kvInvOn`'s `plainLogOn γk.lm L` and `kvLeasesOn_none`);
no consumer found needs it. Naming the model's table is not possible for writes (the client rows carry no raft
log), so the existential stays. Recommendation: the stronger guard (it costs one lemma, and keeps the auth-on
examples' results at lease mode `none` exactly what they were).

Review round 5 (fresh `spec-reviewer`, `/shared/tmp/auth-lease/s3a-review-r5.md`): F1 (`srvKVCoreM_fire` and its
wrappers missing) and S1, S3–S6 applied above; S2 open; claims (1), (3), (4) confirmed (all 104
`Results`/`Adequacy`/`MainLinked` files searched: none under `Proof/github_com` mentions a changed name).

**Not covered here:** S3b's leased puts (their `kvOpStep (.put o)` with `o.leaseID ≠ 0` reads the table; the
results above already carry it).
