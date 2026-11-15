# auth-lease S3a2 Draft: leased puts and leased transactions in the auth-on apply thread

2026-11-15 · branch `auth-lease` (off lean `b7e3cf342a`, S3a landed) · plan: `notes/auth-lease-handoff.md`
("Stage S3a2"), ledger 2026-11-15 "the latest track's certificate premise for a leased put or transaction"
(decision: (3) in S3a, then (1) as S3a2), `notes/auth-lease-s3a-draft.md` §3a, §6, §15. Evidence: the probe
`Scratch/S3a2Probe.lean` (untracked; §2), the code read below.

**Revision 1 (2026-11-15), the S3a2 Freeze package candidate.**

## 0. What S3a2 does, and what it leaves

S3a (rev 7) admits no leased put or leased transaction with auth on (`plainReqL lm := plainReq`), because the
latest triples' premise `certPreVW … (kvOutL …)` becomes, through `certPreW_inner`, the class track's `certPre`
over every `backendStep` outcome, and `backendStep` (`apply/Chain.lean:209-231`) admits an applied put of a lease
that is not live and an applied transaction without `PathsLeaseOk`. `kvNxOn` cannot certify those logs (the model
keeps the log there). S3a2 restricts the certificate the apply layers ask for to the outcomes that are lease-exact
at the live set the call runs against. That is ledger option (1), with `backendStep` unchanged. It then re-admits
leased puts and leased transactions at the revocable mode (`plainReqL` back to S3a rev 5 §1's text), so §6's KV arm
covers them over S3a session 5's lemmas (`backendLog_of_step`, `outcomeOn_of_kvOutLL`, `kvGrantedL_of_kvOutL`,
`kvShapedL_of_logL`, the `leaseOk` bridge).

S3a2 changes no request-side statement. S3b's proposers of a leased put with auth on are what make the new case
reachable by a server, so until S3b it is reachable only in the model and the apply thread's proofs. No closed
theorem changes (§6).

## 1. The class track's certificate at the live set

New, in `apply/Chain.lean` beside `certPre` (whose body does not change: the auth-off server, `dispatch.spec`'s
`certPreV` and the revocation and delete triples keep it):

```lean
/-- the certificates of the outcomes of `c` that are lease-exact at the live set `T` -/
def certPreT (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log) (T : List w64) : IProp GF :=
  iprop(□ ∀ oc : Outcome, ⌜chainStep backendStep c rq log oc ∧ leaseExactL T rq log oc⌝ -∗
    E.Nx (oc.logAfter log))

/-- `leasesLive` at the live set `T` -/
def leasesLiveAt (E : AEnv GF) (s : List EtcdKv) (T : List w64) : IProp GF :=
  iprop(txn.leasesKnown T s ∗ lease.lessorUser (mvccLeases E.γ) T (mvcc.leaseItemsOf s) ∗ ltHalf E T)

/-- `mPre` at the live set `T` (`mPre`'s body with `leasesLiveAt E (stateAfter log) T`) -/
def mPreAt (E : AEnv GF) (c : Chain) (a : GoInterface) (info : AuthInfo) (log : mvcc.Log) (T : List w64)
    (Pre Q Post : IProp GF) : IProp GF := …
```

Laws (proved in the probe): `mPre_iff_at : mPre E c a info log Pre Q Post ⊣⊢ ∃ T, mPreAt … T …`;
`certPreT_of_certPre : certPre E c rq log ⊢ certPreT E c rq log T` (any `T`); `certPreT_mono` (as `certPre_mono`,
for a wrapper chain); `leasesLive E s ⊣⊢ ∃ T, leasesLiveAt E s T`.

**`putPre`/`txnPre` bundle the certificate with the live set** (bodies change, signatures do not):

```lean
-- old
def putPre … := iprop(⌜rq.put = some o ∧ dispatchKind rq = .put ∧ putOk log⌝ ∗ certPre E c rq log ∗
    txn.putRequestIs r o ∗ mPre E c a info log Pre Q Post)
-- new
def putPre … := iprop(⌜rq.put = some o ∧ dispatchKind rq = .put ∧ putOk log⌝ ∗ txn.putRequestIs r o ∗
    ∃ T, certPreT E c rq log T ∗ mPreAt E c a info log T Pre Q Post)
```

and the same for `txnPre` (its pure conjunct `txn.TxnPreA log t ∧ putOk log` kept). The caller picks `T`. It has
to be the live set of the resources it passes, and `ltHalf` ties that set when `E.lg`. A caller holding the old
pre gets the new one (`putPre_of_old`, proved in the probe: split `mPre`, weaken `certPre`). `deletePre`,
`rangePre`, the revocation's pre and `certPre` itself are unchanged: a delete's and a revocation's `backendStep`
are deterministic, and `leaseExactL` is `True` on them.

Why bundle and not add a `T` argument (the handoff's literal "kvOwnAt E log T"): the ten class-track `Spec/`
triples name `putPre`/`txnPre`, so their texts stay as they are, and their callers (the wrapper layers, the class
`dispatch`) do not pick a `T` they do not otherwise have. The live set stays fixed at `T` throughout the call
either way.

## 2. The backend's `Put` and `Txn`: the certificate taken only when the lease is live (probe)

**`applierV3backend.Put`** (`applierV3backend__Put.lean:88-95` builds `E.Nx` of the committed log from `certPre`
before the lease check). New: the witness is built inside the live branch (`o.leaseID = 0 ∨ o.leaseID ∈ L`), from
`certPreT … L` at `applied (log ++ [putChangeOf …])`. That outcome is lease-exact at `L`: the dead-lease arm is
vacuous because the lease is live, and the rejection arm is vacuous because the outcome is applied. The dead
branch never needed the witness. **Probed** (`Scratch/S3a2Probe.lean`, `Put_wp_T`, checked with
`etc/lean-check.py -a`, no `sorry`): the proof is the current one with the destructuring of the new pre (`L` from
`mPreAt`, the same name it had) and the `ihave Hnx` block moved into the live branch.

**`applierV3backend.Txn`** — **finding: needs a stronger `txn.Txn.specSole`.** The backend builds the witness
inside the write wand it hands to `txn.Txn` (`applierV3backend__Txn.lean:83-108`). The wand is told only
`PathsIgnOk` (`Spec/…/txn/Txn.lean:62-65`), but `certPreT … L` asks for an applied transaction's `PathsLeaseOk
(stateAfter log) L br`. `txn.Txn`'s proof has that fact in hand when it calls the wand: `Hlok`, from `checkTxn`'s
`leasesOk`, is in scope at `txn/Txn.lean:182`, and the wand is called at `:256`. In Go, `checkTxn` runs before
`kv.Write` (`server/etcdserver/txn/txn.go:54-67`; `checkPut` calls `checkLease`, `put.go:71-72`). Proposed (a
frozen `Spec/` text, strengthened):

```lean
-- txn.Txn.specSole's write wand, old
∀ σ, ⌜txn.PathsIgnOk (stateAfter log) br⌝ -∗ Qr σ -∗ txn.txnBeginAU γ log t Qw
-- new
∀ σ, ⌜txn.PathsIgnOk (stateAfter log) br ∧ txn.PathsLeaseOk (stateAfter log) L br⌝ -∗ Qr σ -∗ txn.txnBeginAU γ log t Qw
```

(`br := t.branch (txnOk (stateAfter log) t)`, `L` the spec's live set.) It is a weaker obligation on the caller,
and `txn.Txn`'s proof changes by one line (`Hwand $$ %σr %⟨Hign, Hlok⟩ HQr`). The only caller that builds a write
wand is `applierV3backend.Txn` (`EtcdServer.Txn`'s read path uses `specRead`). **Probed** with a local copy of the
strengthened spec (`txn.TxnSpecSoleT`, `Txn_wp_T`, no `sorry`): `certPreT … L` at the applied outcome, with
`leaseExactL`'s txn arm from the wand's `PathsLeaseOk`. Not covered by any `etc/api` list, so there is no
interface diff. The text was frozen in `notes/mvcc-api-clients/clients-txn.md` §8 ("the wand's `PathsIgnOk`",
decided by the coordinator, 2026-11-06), so changing it needs sign-off.

The other class-track layers pass `certPreT` on unchanged. Quota, capped and corrupt use `certPreT_mono` for their
chain, and their rejections take no certificate. The auth layer's class-track `Put`/`Txn` use the `certPre_mono`
pattern at `T`. `uberApplier.dispatch`'s class track builds `putPre`/`txnPre` from its `certPreV` and `kvOwnPre`
(`putPre_of_old`), and `newQuotaApplierV3`/`newApplierV3Capped` re-check.

## 3. The latest track: `X` gains `leaseExactL T`

**`putPreW`/`txnPreW` bundle the same way** (bodies only, `AuthApplyLatest.lean:177-198`; `deletePreW` unchanged):

```lean
def putPreW … (X : Outcome → Prop) := iprop(⌜…⌝ ∗ txn.putRequestIs r o ∗
  ∃ T, certPreW E c rq log (fun oc => X oc ∧ leaseExactL T rq log oc) ∗ mPreAt E c a info log T Pre Q Post)
```

`authApplierV3.{Put,Txn}.specL`'s texts are unchanged (they name `putPreW`/`txnPreW`). In their proofs,
`mPreRest_lend` lends the live set, which `mPreAt` now fixes to `T`, and the inner certificate comes from the new
law (proved in the probe):

```lean
theorem certPreW_innerT (h : ∀ oc, chainStep backendStep c rq log oc → X oc) :
    certPreW E (.auth on c) rq log (fun oc => X oc ∧ leaseExactL T rq log oc) ⊢ certPreT E c rq log T
```

`Hpass` (every inner outcome meets the verdict, once the checks passed at the latest state) is what it is today.

**The four latest triples' certificate premise** (text change, the exported `apply_*_kv_latest`): in
`uberApplier.dispatch.kvSpecL` (`DispatchKVL.lean:222`), `uberApplier.Apply.kvSpecL` (`ApplyKVL.lean:61`),
`apply.uberKVC` (`ApplyFnKVL.lean:76`) and `apply.Apply.kvSpecL` (`ApplyFnKVL.lean:119`):

```lean
-- old
apply.certPreVW v3 E c rq log (apply.kvOutL E.authMode hs ai ci rq log)
-- new
apply.certPreVW v3 E c rq log (apply.kvOutLT E hs ai ci rq log T)
-- with (new, DispatchKVL)
def kvOutLT (E : AEnv GF) (hs) (ai) (ci : Chain) (rq : IRRModel) (log : mvcc.Log) (T : List w64)
    (oc : Outcome) : Prop :=
  kvOutL E.authMode hs ai ci rq log oc ∧ (E.lg = true → leaseExactL T rq log oc)
```

`T` is the triples' existing binder, the one in `ltHalf E T`. The `E.lg` guard follows the posts' existing
`⌜… → E.lg = true → leaseExactL T …⌝`: when `E.lg = false`, `ltHalf` is `True` and does not tie `kvOwn`'s live set to
`T`, so the guard is what lets the dispatch pass the certificate on at its real live set `L`. In the dispatch's
put/txn cases, `mPre_iff_at` splits `kvOwnPre`'s `mPre` at `L`, `ltHalf` agreement gives `E.lg = true → L = T`, and
`certPreW_mono` turns `kvOutLT … T` into `kvOutL … ∧ leaseExactL L` (`certPreW_tie`, proved in the probe). At
`E.lg = false` the certificate is `kvOutL`'s, and every outcome it admits is still admitted. Delete, range and
revocation weaken by `certPreW_mono`. **Posts unchanged.** They already carry `⌜v3 → E.lg → leaseExactL T …⌝`
(S3a §3a).

Exported, restated through the abbrevs: `apply_dispatch_kv_latest`, `apply_uber_apply_kv_latest`,
`apply_apply_kv_latest` (`Results.lean:1789-1808`). `apply_applier_kv_latest` and `auth_pass_kvPostFL_nil` change
in meaning only (`applierKVL`'s triples, through `putPreW`/`txnPreW`).

## 4. The server: admission widened, the KV arm over leased requests

**`plainReqL` back to S3a rev 5 §1** (`KVAuthModel.lean:802`; the text rev 7 replaced, `git show de3481d9ab`):

```lean
-- old (rev 7)
def plainReqL (_lm : lease.Mode) (rq : apply.IRRModel) : Prop := plainReq rq
-- new (= rev 5)
def plainReqL (lm : lease.Mode) (rq : apply.IRRModel) : Prop :=
  plainReq rq ∨ (lm = .revocable ∧ apply.noSideEffect rq = false ∧ apply.needAdminPermission rq = false ∧
    (apply.dispatchKind rq = .put ∨ (apply.dispatchKind rq = .txn ∧ ∀ t, rq.txn = some t → txnPlainL t)))
```

`plainReqL_none : plainReqL .none rq ↔ plainReq rq` keeps holding, so authkv's, auth3's and etcdstart's logs
(lease mode `none`) mean what they did. `plainReqL_iff` (rev 7) is deleted, and its users go back to
`plainReqL_none` or take the disjunction.

**The certificate the server gives** (`kv_certPreW_on`, `kv_certPreVW_on`, `ApplyEntryOn.lean:85-121`, internal):
`plainCover rq` becomes `plainReqL γk.lm rq` with `keysNonEmpty`, and the certificate is at
`kvOutLT E … (s.2.2.ids)`. For an outcome meeting it: when `E.lg = true`, `outcomeOn_of_kvOutLL` with
`leaseExactL s.2.2.ids`; when `E.lg = false`, `γk.lm = E.lm = .none` (`srvKVInvsOn`, `AEnv.lm_of_lg_false`), so
`plainReqL .none` gives `plainCover` (`outcomeOn_of_kvOutLL`'s left disjunct). The server's `T` is `srvRestM`'s
table, `(appliedTableM true γr A).ids`, which is the model's (`appliedTableM_eq_model`, `pre = []`).

**`applyEntryNormal.wp_proofOn`'s KV arm (v3 = true):** the dispatch post's `leaseExactL T` conjunct, today dropped
at the server (`%HXo, -, #Hdel`, `EtcdServer__applyEntryNormal.lean:2021`), goes to `kvOn_after_kv`/`outcomeOn_of_kvOutLL`. Its pre is `kvShapedL_of_logL`
with `keysNonEmpty_kvRaftOfOn` (S3a session 4), at `plainReqL lm`. The replay branch (v3 = false) and the
grant/revocation arms do not change in text. `plainOrCmpG_of_entryOn` and the destructurings of `plainReqL` (13
sites: `KVAuthModel`, `KVOutcomeOn`, `ProposeOn`, `ApplyEntryOn`, `EtcdServer__applyEntryNormal`) take the
disjunction.

**Exported server results** (`Results.lean`; none is used by another proof):

| result | old | new |
|---|---|---|
| `kv_outcome_on_latest` (:1816) | `(hp : plainCover rq)` | `(hp : plainReqL lm rq) (hex : plainCover rq ∨ leaseExactL s.2.2.ids rq s.2.1 oc)` (= `outcomeOn_of_kvOutLL`) |
| `apply_kv_entry_pre_on` (:2429) | conclusion `⌜plainCover rq ∧ …⌝`, `certPreVW true E x.chain rq x.log (kvOutL …)` | `⌜plainReqL γr.kv.lm rq ∧ …⌝`, `certPreVW true E x.chain rq x.log (kvOutLT E … (kvLeasesOn γr.kv st₀ A).ids)` |
| `apply_kv_after_on` (:2449) | `(hp : plainCover rq)` | `(hp : plainReqL lm rq)` and `hout` gains `plainCover rq ∨ leaseExactL lt.ids rq x.log o` |
| `server_apply_not_nospace_on` (:2493) | `(hp : plainCover rq)` | `(hp : plainReqL lm rq)` (`dispatchStep_start` at a leased put/txn: rejected by the backend or applied, as at lease `0`) |

## 5. Literal-mode uses (the follow-up; forms only)

S3a raised the etcdserver `lit-mode` baseline from 156 to 252. Most of the rise is `appliedTableM true`,
`srvRestM true` and `srvRestRpM true` in `RestOn.lean` (28), `EtcdServer__applyEntryNormal.lean` (27, the auth-on
arms) and `EtcdServer__apply.lean` (14). Plan: state `RestOn`'s lemmas and the `wp_proofOn` arms over
`srvRestT E γr (kvLeasesOn γr.kv srvAuthSt0 (γr.raft.pre ++ A)) A` (`srvRestT` is table-generic, `InvRest`) and the
model's table, without the literal. One bridge per name (`srvRestM_true_eq`, `srvRestRpM_true_eq`,
`appliedTableM_true_def`, `rfl`/`if_pos`) converts at each arm's entry and exit, and the specs stay at
`srvRestM E.authOn`/`C.isOn`. These are internal forms: no statement in `Spec/`, `interface/` or a closed theorem
changes. Target: etcdserver `lit-mode` ≤ 200, measured and ratcheted (`etc/mode-check.py --check --update`) at the
land stop. If a site cannot lose its literal, it is classified (`etc/mode-allow.txt`) and listed in the report.

## 6. Statements this changes (for the Freeze)

**Text changes:**
- `apply/Chain.lean`: the bodies of `putPre` and `txnPre` (§1). New: `certPreT`, `leasesLiveAt`, `mPreAt` and their
  laws.
- `apply/AuthApplyLatest.lean`: the bodies of `putPreW` and `txnPreW` (§3). New: `certPreW_innerT`, `certPreW_tie`.
- `apply/DispatchKVL.lean`: new `kvOutLT`. The certificate premise of `uberApplier.dispatch.kvSpecL`,
  `uberApplier.Apply.kvSpecL`, `apply.uberKVC` and `apply.Apply.kvSpecL` (§3), and through them
  `apply_dispatch_kv_latest`, `apply_uber_apply_kv_latest` and `apply_apply_kv_latest`.
- **`Spec/…/txn/Txn.lean`: `txn.Txn.specSole`'s write-wand premise gains `PathsLeaseOk (stateAfter log) L br`**
  (§2; frozen text, a strengthening).
- Server: the body of `plainReqL` (§4). `kv_outcome_on_latest`, `apply_kv_entry_pre_on`, `apply_kv_after_on`,
  `server_apply_not_nospace_on` (§4's table).

**Meaning only (text unchanged):**
- The ten class-track `Spec/` triples that name `putPre`/`txnPre`: `applierV3backend.{Put,Txn}`,
  `quotaApplierV3.{Put,Txn}`, `applierV3Capped.{Put,Txn}`, `applierV3Corrupt.{Put,Txn}`, `authApplierV3.{Put,Txn}`.
  They ask a certificate of fewer outcomes, with the same resources (`∃ T, mPreAt … T` ≡ `mPre`), so each triple
  is stronger and its callers' obligation weaker.
- Through them: `apply.applierTriples`/`applierSpec`, `apply/Results.lean`'s `chain_put` and `chain_txn`.
- `authApplierV3.{Put,Txn}.specL`, `applierKVL`, `apply_applier_kv_latest`, `auth_pass_kvPostFL_nil`.
- `plainEntryOn`/`plainLogOn` and therefore `kvInvOn`: they admit more at `revocable`, and at `none` they are
  unchanged by `plainReqL_none`. `kvInvOn` appears in `interface/…/etcdstart/Alloc3On.txt` by name only, so there is
  no interface diff.
- `txn.Txn.spec` (`specSole ∧ specRead`).

**Not changed:** `backendStep` (`Chain.lean:209`), `certPre`, `kvPostF`, `kvPostFL`, `leaseExactL`, `kvOwn`,
`kvOwnAt`, `dispatch.spec` (class), every auth-off statement, the snapshot path, `srvKVInvsOn`, `kvInvOn`'s body.

**Closed theorems: none change.** No file under `Proof/github_com/` mentions `putPre`, `txnPre`, `certPre*`,
`kvSpecL`, `uberKVC`, `kvOutL`, `plainReqL`, `plainEntryOn`, `plainLogOn` or `specSole` (grep, 2026-11-15), and
`examples/` holds Go only. The closed theorems are adequacy statements over the Go programs' executions. authkv,
auth3 and etcdstart run auth on at lease mode `none`, where `plainReqL_none` keeps the admission as it was, and
the auth-off examples go through `certPre`, which does not change. No `interface/` file mentions a changed name
(grep), and no `etc/api` list covers apply, txn or the server.

**Trust base:** no axiom, `sorry`, opaque or trusted text is added or changed.

## 7. Order of work (after the Freeze), estimate 3–5 agent-days

1. `Chain.lean`: `certPreT`, `leasesLiveAt`, `mPreAt` and their laws. `putPre`/`txnPre` bodies. The ten
   class-track proofs, class `dispatch`, `newQuotaApplierV3`, `newApplierV3Capped`, `apply/Results`.
2. `txn.Txn.specSole`'s wand: the spec, `txn/Txn.lean:256`, `applierV3backend.Txn`.
3. Latest: `putPreW`/`txnPreW`, `certPreW_innerT`, `AuthApplyLatestPut`/`Txn`. `kvOutLT` and the four triples
   (`DispatchKVL`, `ApplyKVL`, `ApplyFnKVL`, `UberKit`/`UberOn` instantiations).
4. Server: `plainReqL` widened. `kv_certPreW_on` and `kv_entry_pre_on` at `kvOutLT`. The KV arm of `wp_proofOn`.
   `Results`.
5. Literal-mode reduction (§5).
6. Land-stop checks: merge lean, a full build (flock, 64G), `tcb-report --check` (870/4 unchanged),
   `gen-interface --check` on every `etc/api` list, bounds and mode gates, `grep TRANSITIONAL` empty, closed
   statements unchanged. Then STATUS, the handoff and status-history.
