# M2 apply side, Draft: review round 1 (2026-10-30)

Reviewed: `m2-apply` at `fb2e73ab0f` (Draft `0a88a357f8`): `Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/M2ApplyDraft.lean`
("apply Draft"), `Proof/go_etcd_io/etcd/server/v3/etcdserver/M2ApplyDraft.lean` ("server Draft"),
`M2ApplyDraftSpecs.lean` ("specs Draft"), against `notes/m2-apply-plan.md` items 1-17, A1-A7, G1-G5 and
the user's Q1-Q4. Go read at `.lake/go-src/etcd` (`249d76bea7`). Nothing built; no Lean check needed.
Rubric: `notes/spec-first-plan.md`'s two tiers; `.claude/skills/spec/PRINCIPLES.md`; examples
`apply-uber-contract.md`, `apply-loop-merge.md`.

## The two questions the brief asks first

**A6 (does `Apply` ever skip or reject an in-scope compaction?)** No, the claim holds. `apply.Apply`
calls the uber-applier unless `!needResult && noSideEffect` (`apply/apply.go:45`); `compactPropOkD`
requires `noSideEffect rq = false`. The only early return on the chain is the auth layer's admin check
(`apply/auth.go:52-58`, under `needAdminPermission`); `compactPropOkD` requires it `false`. `dispatch`
returns `nil` before the KV switch only when `!shouldApplyV3` (`uber_applier.go`), which `dispatchCrev`
models through `v3`. The capped and quota wrappers do not override `Compaction` (`capped.go:33-44`,
`quota.go:36-54`); the corrupt applier answers `ErrCorrupt` without reaching the store (`corrupt.go:45`),
which `chainCompacts` models. That chain never occurs, since alarms are excluded (`rqOk`'s `.alarm => False`,
`Chain.lean:257`, and `γk.ch0 = alarmChain false false false`). So `kvCrevEntry` is exact for every entry
the invariant admits. The caveat is that the *apply loop* does not receive `compactPropOkD` for its entry
(finding S-3 below).

**A4 (does a compaction leave the clients' KV view unchanged?)** Yes, at every revision it keeps.
`updateCompactRev` leaves `currentRev` alone (`storage/mvcc/kvstore.go:197-222`); the job removes only
revisions below `rev` that are not live at `rev` (given `NoDelPutAt`, or the fork fix). So
`dispatchStep`'s non-store branch `o.logAfter log = log` (`InvUber.lean:68-71`) is true of the code. Reads
below the compaction revision fail with `ErrCompacted`, and the client specs already admit any
`applyErrIs` error (`EtcdServer.Range.spec`'s failure arm). Keeping `KVState.compacted = 0` is therefore
sound, with this margin: the code also guarantees that a read at a revision at or above the compaction
revision succeeds, and no spec says so. Watchers are excluded in compaction mode.

**No bug in the Go code was found.** The backend's `rr, _ := KV.Range(...)` followed by `rr.Rev`
(`apply/backend.go:78-79`) cannot see `rr = nil`: after `Compact(rev)`, `compactMainRev = rev ≤ currentRev`,
so a read at the latest revision is never compacted. Nothing goes to `issues/`.

## First-tier findings (wrong, unprovable, or unusable by a real caller)

### F-1. `cmpTriple` / `applierV3backend.Compaction.specD` cannot be proved over today's `store.Compact.spec` (items 9, 10)

- **Principle:** Complete (the callee spec must give what this proof needs).
- **Evidence.** `mvcc.store.Compact.spec`'s third disjunct, `ErrFutureRev`
  (`Spec/.../mvcc/store__Compact.lean:89-93`), gives only `∃ log, idxCert γ.idx log ∗ ⌜log.length ≤ rev⌝`.
  The caller's own certificate (`idxCert log₀`, `rev < log₀.length`) does not contradict that.
  `idxCert` is prefix-closed (a lower bound of the committed log, `InvIndex.lean:1136`), and
  `idxWriter_cert_prefix` only places the shorter log under the writer's log. So the backend's proof
  must handle `ErrFutureRev`. The drafted `cmpAnswerIs`, through a chain that compacts
  (`apply/M2ApplyDraft.lean:172-180`), admits an error only with `rev ≤ crev`, and the post gives back
  `cmpOwn E (cmpRevAfter crev rev)`. Neither holds after `ErrFutureRev` (where `crev < rev` and the right
  is unchanged). Today's Go never returns `ErrFutureRev` here (`rev < log₀.length ≤ currentRev + 1`), but
  the spec does not say so.
- **Callers affected:** every `applierSpec` producer (item 9), `uberApplier.dispatch/Apply.specD`
  (item 11), and through them `applyEntryNormal`.
- **Restatement.** Drop the `ErrFutureRev` disjunct from `store.Compact.spec` and
  `store.updateCompactRev.spec`: under their own precondition it is unreachable, because the store's
  proof knows the certificate is a prefix of its committed log. This changes an exported mvcc result
  (`mvcc_store_Compact`). It is a missing approval item; call it **G6**.
- The alternative of admitting `ErrFutureRev` in `cmpAnswerIs`, with the right unchanged, would weaken
  `dispatchCrev`/`crevOf` into a non-function of the log. Reject it.

### F-2. The compaction's result loses "no trace on an error", so `Compact` cannot go through `processInternalRaftRequestOnce.spec` (items 2 and 6's "`specCompact` goes")

- **Principle:** Complete; check the caller's Go body.
- **Evidence.** `EtcdServer.Compact` uses `result.Trace` (`GetStartTime`, `SetStartTime`, `InsertStep`)
  whenever it is non-nil, *before* it tests `result.Err` (`v3_server.go:393-401`). Today's
  `specCompact` supplies `compactResultIs`, which owns `traceRes v.Trace'` in every case
  (`CompactMode.lean:228`), and today's proof relies on it (`EtcdServer__Compact.lean:255`). The general
  spec's post gives only `apply.resTrace res`: `Err ≠ nil ∨ traceRes Trace` (`InvUber.lean`,
  `resTrace`). On an error, then, nothing says the trace is `nil`. `cmpAnswerIs` knows `trace = null` on
  an error, but `dispatchAnswerD` (`apply/M2ApplyDraft.lean:185-191`) is stated over `resp`/`err` only
  and drops that fact.
- **Callers affected:** `EtcdServer.Compact.wp_proof` once `specCompact` is gone. Through it, the
  compactor's `compactableOk_server` (`CompactEnv.lean`).
- **Restatement.** Have `dispatchResult`'s compaction case carry `v.Err' ≠ nil → v.Trace' = null`, or
  give `dispatchAnswerD` the result's trace. For example, the error arm becomes
  `⌜rp = null ∧ err ≠ nil ∧ tr = null⌝` with `dispatchAnswer … v.Resp' v.Err' v.Trace' o`. Keep
  `specCompact` until this lands.

### F-3. `EtcdServer.Compact.specD`'s `⌜E.cmp = true⌝` does not reach the KV invariant's mode (item 15)

- **Principle:** Sound/complete: the precondition must make the proof possible.
- **Evidence.** The proposal must satisfy `reqPropOkM false … = reqPropOkD ρ.kv ρ.kv.cmp …` (item 6). Its
  compaction form needs `ρ.kv.cmp = true`. `isServerReq s E ρ` contains `kvInv ρ.raft ρ.kv`
  (`InvProposer.lean:423`) and nothing relating `E.cmp` to `ρ.kv.cmp`. The specs Draft's own comment
  ("at the switch `ρ.kv.cmp = true`", `M2ApplyDraftSpecs.lean:197-199`) shows the text submitted for
  approval is not the one meant.
- **Callers affected:** v3rpc's `Compact` and the compactor's server environment.
- **Restatement.** Add the tie once, in the request path's view: `srvReqFieldsAt`'s `⌜ρ.kv.cmp = E.cmp⌝`,
  made by `NewServer` from its premise `ρ.rd.kv.cmp = E₀.cmp` and `envAgree`. Then `⌜E.cmp = true⌝`
  suffices. The apply loop needs the same tie (G1's `cmpLogOk ρ.kv E.cmp`, item 8). Without the field,
  write `⌜ρ.kv.cmp = true⌝`.

### F-4. `applyEntryNormal` has no source for `compactPropOkD` of its entry, so `x'.crev = crevOf (A ++ [m])` is unprovable (item 12)

- **Principle:** Complete.
- **Evidence.** `crevOf_step` needs
  `hok : dispatchKind rq = .compaction → compactPropOkD rq` (`M2ApplyDraft.lean:233`). Item 12 adds only
  `cmpEntryOk`, which gives `cmp = true`, `r < length` and `NoDelPutAt` (`M2ApplyDraft.lean:270-275`). It
  gives neither `noSideEffect = false` nor `needAdminPermission = false`. `entryOkM` and `logShape` do
  not give them either. Without them, a compaction that also carries `AuthStatus` would be skipped on a
  member with no waiter, and `crevOf` (which ignores skipping) would be wrong there.
- **Callers affected:** `applyEntries` and `applyAll` (A1 puts the claim in `kvApplied`, which they
  carry).
- **Restatement.** Put the scope into the claim:
  `cmpEntryOk γk cmp A m := … → cmp = true ∧ compactPropOkD rq ∧ ∀ r, …`. `reqPropOkD`'s compaction
  form already carries `compactPropOkD`, so `kvInvD`'s `cmpLogOk` (G4) can record it.

### F-5. Items 5 and 6 (and so the switch) cannot precede the fork fix (Q2 dependency)

- **Principle:** Sound/complete, at the switch.
- **Evidence.** Under `kvInvD`/`reqPropOkD`, every compaction-mode write form needs
  `cmp = true → irrNoDelPut rq`. `EtcdServer.Txn`'s proof cannot supply it for a general transaction
  (delete-then-put is exactly what `issues/etcd-compaction-delete-then-put.md` reproduces). Q2 rejected
  item 16, the premise that would have supplied it. So once items 5/6 switch, `EtcdServer.Txn.spec` is
  unprovable for a server whose `ρ.kv.cmp = true`. The plan says "the other items do not wait"; for 5
  and 6 it is wrong.
- **What depends on the fix.** Assuming it lands (etcd-io/etcd#22377 and #22395, the pin bump, and a
  re-proof of `keyIndex.doCompact` and the compaction job), these go:
  - `store.Compact.spec`'s and `updateCompactRev.spec`'s `NoDelPutAt`;
  - `cmpAdmit`'s, `cmpTriple`'s and `Compaction.specD`'s `NoDelPutAt` (items 3, 9, 10);
  - `cmpEntryOk`'s (item 12);
  - `kvInvD`'s `cmp = true → ∀ c, NoDelPutAt` (item 5);
  - `reqPropOkD`'s first disjunct, which becomes `reqPropOk` alone (item 6);
  - G3, item 16, and `irrNoDelPut`.

  The mvcc re-proof is on the critical path of the whole switch, not only of `Txn`.
- **Restatement.** Approve items 3, 5, 6, 9, 10 and 12 in their fix-assumed (`NoDelPutAt`-free) form, and
  order the switch after the fork fix and mvcc's re-proof. Otherwise items 5/6 would be approved twice.

### F-6. Item 14 is inconsistent with A2: after A2, `srvKVCloserM srv E (-1)` no longer carries the right that `start` is to split off

- **Principle:** Complete; the vocabulary is part of the spec.
- **Evidence.** A2 says `srvKVCloserM`'s on arm "loses" the right (plan, lines 53-59 and 199). Item 14's
  post hands out `srvKVCloserM srv E (-1)` (`M2ApplyDraftSpecs.lean:160`) as the source of
  `cmpRight E (-1)` for `start` (G5). Both cannot hold. If the predicate loses the right, `NewServer`'s
  post gives `start` nothing to split, `applyKV` lacks `cmpOwn`, and a compaction entry is unprovable.
- **Restatement.** Use two predicates. `NewServer`'s post carries the closer with the right
  (`srvKVCloserM srv E (-1)` as the storage side drafted it). `start`'s state carries a right-less closer
  (e.g. `srvKVCloserW srv E`), the one `restorePre_of_applyM` takes. Alternatively, `NewServer`'s post
  gives `srvKVCloserW srv E ∗ apply.cmpRight E (-1)` directly, so that `start` only moves the second
  conjunct. Under Q4 this also applies to `specCompact`'s post, which today hands out `srvKVCloser` and
  has no source for the right.

## Second-tier findings (cost, clarity, missing items)

- **S-1. Item 1's in-place redefinition of `dispatchOk` has a larger blast radius than listed.**
  `apply.Apply.specRec` (`ApplyRec.lean:64-75`, used by `applyEntryNormal`'s proof at lines 244 and 970)
  takes `rqOk ∧ dispatchOk` and calls the uber `Apply` through `applyKV`. After the switch it also needs
  `cmpAdmit` (else the compaction arm has no `store.Compact` precondition). It is unlisted.
  - `DispatchKVL.lean:722` and `DispatchAdmin.lean:469` close the compaction arm "by `dispatchOk`". Their
    statements still exclude compaction (`isKVKind`, `adminKindOk`), so only the proofs change.
  - The off-mode texts no longer get "not a compaction" from `dispatchOk`. That is why items 12/13 add a
    conjunct in *both* modes, so `applyEntryNormal/applyEntries/applyAll.spec` do not read as today when
    compaction is off (the brief's requirement).
  - Recommended: keep `dispatchOk` as is and use a mode-indexed `dispatchOkM cmp on rq` (`dispatchOk`
    at `false`, `dispatchOkD` at `true`, `rfl` off) where the mode is known (`entryOkM`, `rqShape` via
    `logShapeM`). This follows the `srvApplyKVM`/`logShapeM` convention of `apply-loop-merge.md`. If the
    in-place route stays, give the off corollaries that restore today's statements exactly, and list
    `specRec`.
- **S-2. G2 / Q3: the law as phrased, "every certified log is in the KV certificate map", cannot be
  proved from today's mvcc.** `idxCert` holds of every prefix of the committed log (`InvIndex.lean:1136`).
  `store.Restore.spec` certifies only the restored log itself, `certOk γ ([[], []] ++ R)`
  (`store__Restore.lean:125`), not its prefixes. `certMapOk` (`InvRequest.lean:394`) is not downward
  closed in length. It is true of the running system (lengths are certified in order) but not derivable.
  - **Closable form:** mvcc keeps "the store's current committed log is `certOk`" as an invariant. Every
    commit takes `certOkNext`, `Restore` takes `certOk` of the image, and `NewStore`'s log has length 2.
    A law then gives `idxCert γ log ⊢ ∃ l, certOk γ l ∗ ⌜log ⊑ l⌝` (with the store's invariant open), and
    `kvCertInv` excludes `certFree`. That gives `cmpReach γk r` from `srvRevLb E.γ r`. It is enough for
    A7: a *longer* certified log is all `cmpReach` needs.
  - Uncertain: whether mvcc's store invariant can expose that law to a caller holding only
    `storeReaderC`. Checking it is the Probe.
- **S-3. `crevOf_step`'s other hypotheses.** `hch : x.chain = γk.ch0` must come from `kvApplied` (today's
  `kvAppliedL` is "at the start's chain", likely available). `hv3` is the spec's own premise. Fine, but
  state where each comes from in the glue list.
- **S-4. Unlisted dependencies and items.**
  - The storage side's `srvEnvOkD` (`d.cm = E.cmp`; `srvEnvOk` on `lean` still has `d.cm = false`,
    `InvApplier.lean:482`) must switch first, since `cmpAdmit_of_entry` reads it.
  - `KVNames.cmp` and the tie `ρ.kv.cmp = E.cmp` (F-3).
  - Under Q4, the interim texts of `NewServer.spec` (`ρ.rd.kv.cmp = false`) and `specCompact`
    (`ρ.rd.kv.cmp = true`; today it takes the *off* `kvInv`, `NewServer.lean`'s `specCompact`) are not in
    the item list.
  - `compactableOk_server` (`CompactEnv.lean`) is restated over `isServerReq`.
  - The examples' allocation at the mode (`common/Alloc.lean:50` already has `cmp`).
  - A lemma `compactPropOkD (withHeader rq hm)`, since the header does not touch the fields read.
- **S-5. A1's `ApplyKV.crev : Int := -1` does not make `⟨log, chain⟩` elaborate.** Lean's anonymous
  constructor ignores defaults (checked: "Insufficient number of fields for `⟨...⟩`"). `bootKV` and
  `bootKVOf` (`InvBuild.lean:87, 91`) and any positional `ApplyKV` in proofs must name the field.
  Mechanical, but the plan's "texts do not mention it" holds only for the specs.
- **S-6. `NewServer.specD`'s off reading.** `srvKVCloserM srv E (-1)` is `srvKVCloser srv E` only given
  `¬ kbCmpM E.γ.kb`. Restoring today's off post needs a law from the post (`envAgree` gives
  `E.γ.cm = false`; `kbCmpM E.γ.kb ↔ E.γ.cm` must be exported, not unfolded from `srvBuilt`).
- **S-7. G1 (claims of the committed logs).** Closable as `clusterWorkloadOk_of` does for `logShape`
  (`kvModel_eqv` at each prefix). It needs F-3's tie, since `cmpLogOk ρ.kv E.cmp`.
- **S-8. Size and coupling.** `cmpTriple`, `Compaction.specD`, `dispatch.specD` and `Apply.specD` repeat
  `kbCmpM ∧ rev < length ∧ NoDelPutAt` instead of `cmpAdmit`. After F-5, write `cmpAdmit` once.
- **Vacuity check.** Nothing is vacuous. `cmpReach γk 1` holds trivially through `kvCert`'s
  `length ≤ 2` arm, and that is correct (revision 1 always exists, since `log0` has two revisions).
  `kbCmpM none = True` (`InvStore.lean:1721`) makes `cmpRight` demand the right for an assumed backend;
  the server never has one.

## Per target: what is good

- **Apply Draft.**
  - `chainCompacts`, `cmpRevAfter`, `dispatchCrev` and `applyCrev` model `updateCompactRev` and the corrupt
    applier exactly, and are mode-free.
  - `cmpAnswerIs` states what Go returns in both arms, including the nil response and nil trace on
    `ErrCompacted`/`ErrCorrupt` (`backend.go:73-75`, `corrupt.go:45`).
  - `cmp_store_pre` is a real glue proof (no unfolds of other packages beyond what the apply package owns).
  - A1/A3 put the right where the code's only user (the apply thread) is.
- **Server Draft.**
  - `crevOf` is the right abstraction for a revision that is logical across a restore. `crevOf_mono`,
    `crevOf_pos` and `crevOf_plain` are proved and are exactly what the snapshot track's `c ≤ c'` needs.
  - `kvInvD_off` and `reqPropOkD_off` are proved equalities/equivalences: one family, not two.
  - A7 (the revision reached at the model, not at the proposer's store) is the correct fix for a
    3-member cluster.
- **Specs Draft.** `NewServer.specD`'s configuration premise is no stricter than Go (retention 0 in any
  mode, or revision mode at a positive retention), and the scope limit is documented.

## Per-item verdicts

| Item | Verdict |
|---|---|
| 1 `dispatchOk` | blocked: S-1 (`specRec`; off texts); prefer `dispatchOkM` |
| 2 `dispatchAnswer` | blocked: F-2 (the trace on an error) |
| 3 apply vocabulary | approvable in the fix-assumed form (F-5); `cmpAnswerIs` after F-1 |
| 4 A1 record | approvable (S-5 cost noted) |
| 5 `kvInvD` | blocked on Q2's fix (F-5); then approvable without the `NoDelPutAt` conjunct; F-4's `compactPropOkD` in `cmpLogOk` |
| 6 `reqPropOkD` | blocked on Q2's fix (F-5); "`specCompact` goes" needs F-2 |
| 7 `crevOf` | approvable |
| 8 `clusterWorkloadOk` | approvable with F-3's tie |
| 9 `cmpTriple` | blocked: F-1 (G6, mvcc's `ErrFutureRev`) |
| 10 `Compaction.specD` | blocked: F-1 |
| 11 `dispatch`/`Apply.specD` | approvable once F-1 is fixed; add `Apply.specRec` (S-1) |
| 12 `applyEntryNormal` | blocked: F-4; off reading (S-1) |
| 13 `applyEntries`/`applyAll` | approvable with F-4's fix; off reading (S-1) |
| 14 `NewServer.specD` | deferred by Q4; blocked until F-6 is resolved; S-6 |
| 15 `Compact.specD` | blocked: F-3 (one-line fix) |
| 16 `Txn` premise | withdrawn by Q2 |
| 17 snapshot track | the collaborator's; F-6 bears on `restorePre_of_applyM`'s source of the right |
| `CompactMode.lean`'s family going | approvable once F-2 (for `specCompact`) and F-3 land |

**Gap list:** G1-G5 are incomplete. Add **G6**, mvcc's `ErrFutureRev` (F-1); **G7**, the compaction
result's trace (F-2); **G8**, the `ρ.kv.cmp = E.cmp` tie (F-3); and the `srvEnvOkD` dependency (S-4).
G2 is closable only in the reformulated form (S-2). G1, G3 (moot after the fix), G4 and G5 look closable.

## Ranking by need of revision

1. **Apply Draft:** F-1 (needs an mvcc spec change), F-2, S-1.
2. **Server Draft:** F-4, F-5 (scheduling: the fork fix gates the switch), S-2.
3. **Specs Draft:** F-3 (one line), F-6 (consistency with A2).
