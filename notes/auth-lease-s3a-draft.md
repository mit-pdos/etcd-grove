# auth-lease S3a Draft: the auth-on model and apply thread with leases

2026-11-15 · branch `auth-lease` · plan `notes/auth-lease-scope.md` §2.3 as revised by etcd-grove-81 on
2026-11-15 (`questions.md`: S3 split into S3a/S3b/S3c, leased puts folded in). Design before plumbing: each
changed definition old → new, the lemmas it moves, what S3b/S3c take from it. Evidence: the S0 probe
(`Scratch/AuthLeaseProbeModel.lean`, the triple-state fold and its `_append`/`_ops`/bridge lemmas, proved), the
survey of the auth-on side's "no lease" dependencies (summarized in `/shared/tmp/auth-lease/s3-scope-gap.md`'s
addendum), S2's apply layer (on lean, `c3da59fa29`).

## 0. What S3a does, and what it leaves

The auth-on KV model (`kvEntryOn`, `kvRaftOfOn`, `kvInvOn`, `outcomeOn`, the apply thread's mode-`on` proofs)
assumes today that no lease exists: it folds at the empty lease table, its log admits no lease request
(`plainEntryOn` → `plainReq` → `plainCover`, lease `0`), and the server is a cluster that grants none
(`srvKVInvsOn`'s `γr.kv.lg = false`). S3a gives the model a lease table, admits at the revocable lease mode
grants, revocations and leased puts (a put or a transaction's puts with a lease), refuses a request the auth
layer refuses including its lease part (S2's `authOutLL`/`txnOutLL`), keeps the clients' half of the KV state
(so the KV results stay meaningful in the revocable mode), and gives `srvRest` the auth-on table. It changes no
request-side statement (S3b: the proposers of grants, revocations and leased puts with auth on) and none of the
four couplings (S3c: `srvGrantGuard`, `lease.bootCfg`, `lease.srvInvAt`, `srvUberOn`; `NewServer`). Until S3c a
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
- **Moved lemmas** (the 122 declarations mentioning the fold): mechanical, `s.2` → `s.2.1` for the log; the
  probe proves the shape of `_append`, `_above`, `_filler`, `_emptyV2`, `_ops` and a bridge
  (`kvEntryOnL_fst_snd`: at the empty table and no lease request, the new step's auth state and log are the old
  step's) through which the old lemmas port where a lease case is vacuous. `kvEntryOn_of_refused` takes
  `authKVKind` and `¬ kvGrantedL`; `kvEntryOn_of_granted` the table.

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

**The keys' invariant** (S2 Draft §7, review r1 M3/r2): `keysNonEmpty l := ∀ k id, mvcc.leaseItemsOf
(mvcc.stateAfter l) !! ⟨k⟩ = some id → k ≠ []`, kept by every entry of a `plainLogOn lm` log (a put's key is a
point key of the cache's shape, `kvShapeAll`; a revocation deletes; a grant writes nothing), true of a start
log with no lease (`mvcc.LogNoLease γk.log0`, as the off `kvInv` has). It gives `leaseShapedL` at every lease,
which S2's checks take (`kvShapedL`'s lease parts).

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
- `srvKVInvsOn` (`KVApplyOn.lean:333`): drops `γr.kv.lg = false` (keeps `γr.kv.cmp = false`).

## 4. `srvRest`'s table with auth on (`InvRest.lean`, `AppliedTable.lean`)

`appliedTable γr A = kvLeases γr.kv (γr.raft.pre ++ A)` folds the off table, which ignores the auth layer
(`chainTable` passes `.auth` through): with auth on a refused revocation would leave it. New:

```lean
def appliedTableM (on : Bool) (γr : ReadNames) (A : List EntryModel) : LeaseTable :=
  if on then kvLeasesOn γr.kv srvAuthSt0 (γr.raft.pre ++ A) else appliedTable γr A
```

`srvRest E γr A` and `srvRestAt`'s callers use `appliedTableM E.authOn γr A`; `appliedTableM false = appliedTable`
(`rfl`/`if_neg`), so the off proofs are unchanged up to that rewrite. `appliedTableM_snoc` (on): the table one
entry later is `kvEntryOn`'s, which differs from `kvTable` only at a refused revocation (where it keeps the
table, as the lessor does: the auth applier's `checkLeasePuts` refused, the inner `Revoke` never ran). The leased
arm's laws (`srvRest_applyG`, the grant/revoke `restOut_*`, `srvEver_*`) take the auth-on step for `on = true`.

## 5. The snapshot path (decided: an explicit lease-free premise for now)

The auth-on snapshot statements assume a lease-free log (`SnapRecvOn.lean:43-159, 290, 311, 333`,
`ApplyAllSnap.lean:215, 391`, `MergedImageOn.lean:59`, `SnapAuthRecover.lean`). Today the install
(`applyAll.wp_proofSnapM`, `ApplyAllSnap.lean:933-965`) takes `γr.kv.lg = false` from `srvKVInvsOn`, which S3a
drops (§3). The premise moves:

- `srvKVInvsOn` keeps a conditional row: `⌜γr.kv.cmp = false ∧ (γr.raft.raft.reNoSnap = false → γr.kv.lg = false)⌝`
  (an auth-on cluster that grants leases runs in raft's no-snapshot mode, `RaftNames.reNoSnap`, D19p/D21 M3,
  which the examples' `NoSnapCount`/`NoSnapCatchUp` configuration gives).
- The install's proof takes `γr.kv.lg = false` from that row when the cluster is not in the no-snapshot mode,
  and is unreachable otherwise — **if** the install's proof can derive `reNoSnap = false` from a snapshot being
  installed (raft's `InvRawnodeReady` states `reNoSnap = true → no MsgSnap`; whether a local snapshot can reach
  `applySnapshot` in the no-snapshot mode is to be checked in Probe).
- Fallback, if it cannot: the auth-on install's spec (`applyAll.specSnapM`) gains the explicit premise
  `γr.kv.lg = false`, discharged by its caller from the same row, and the S4 example's `run` shows the install
  unreached in the no-snapshot mode. Either way authkv and auth3 (mode `none`, `lg = false`) meet it trivially
  and their closed statements do not change; S4's example runs with `NoSnapCount`.

Recorded as a follow-up (`notes/auth-lease-handoff.md`): a revocable auth-on cluster's snapshots need the
image's lease table and the restored keys' invariant.

## 6. The mode-`on` apply proofs

- `EtcdServer__applyEntryNormal.wp_proofOn`: the KV branch as today (S2's latest triple, now over the lease
  verdict, its premises from the admission and the keys' invariant, no more `plainCover` discharge); new
  branches for a grant (the general `Apply.spec`, as a cluster request: the off arm's `srvEver_applyPre`,
  `kv_entry_grantFresh`, `grantReqA_of_res`), and a revocation (the latest triple's revocation, S2: `revokeOwn`,
  `ltHalf`, `revokeRestA`; the off arm's `revokeA_drop`, `revokeArM_of_res`) — each the off arm's step with the
  auth-on model (`kvEntryOn`, the refused case keeping the table).
- `EtcdServer__apply.wp_proofOn`: the batch's rows at the table (`kvAppliedOn`'s `lt`, `srvRest`'s on table).
- `ModeSpecs.applyEntryNormal.specOn` keeps its `srvLessorNil s` until S3c (unused since S2).

## 7. Exported statements this changes (for the Freeze)

- Definitions with exported bodies: `kvEntryOn`, `kvRaftOfOn`, `kvOpOn`, `kvModelOn` (type of its fold),
  `plainEntryOn`/`plainLogOn` (new `lm` argument), `entryShapeOn`/`logShapeOn` (at `lm`), `entryDetOn`,
  `kvInvOn`, `outcomeOn`, `kvAppliedLOn`/`kvAppliedOn`, `entryOkOn`, `srvKVInvsOn`, `srvRest` (at
  `appliedTableM`); new `kvGrantedL`, `leaseGrantedM`, `leaseOk`, `kvLeasesOn`, `plainReqL`, `txnPlainL`,
  `keysNonEmpty`, `appliedTableM`.
- `Results.lean` (server): `kv_outcome_on_latest`, `apply_kv_entry_pre_on`, `apply_kv_after_on`,
  `server_apply_not_nospace_on` (premise `plainCover` → the admission), `server_cluster_alloc_on`,
  `server_member_alloc_on` (`kvInvOn`'s body).
- Interfaces: `interface/…/etcdstart/Alloc3On.txt` (`kvInvOn` in a statement), regenerated and reviewed.
- Specs: none of `Spec/` changes in S3a (`logShapeM true` → `logShapeOn E.lm`: `logShapeM on lm` already takes
  the mode; `entryOkM` too). `applyAll.specSnapM`'s `γr.kv.lg = false` stays.
- Closed theorems: none (authkv, auth3 at the mode `none`).
- No axiom, no trusted text.

## 8. Order of work (after the Freeze)

1. The model (§1) with the probe's lemmas; the keys' invariant; `KVAuthBridge`'s `leaseOk_iff`.
2. `kvInvOn` (§2) and its alloc; `srvRest`'s `appliedTableM` (§4).
3. The apply thread's model (§3) and the snapshot premise (§5).
4. The mode-`on` apply proofs (§6), then the examples' adaptations (mechanical: `plainLogOn .none`).
Rebuild: `KVAuthModel` and its importers, about 1500 modules; full builds under the flock.
