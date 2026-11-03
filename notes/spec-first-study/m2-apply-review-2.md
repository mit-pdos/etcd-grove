# M2 apply side, Draft: review round 2 (2026-10-30)

Reviewed: `m2-apply` at `ce00aa140f`, the repair of round 1
(`notes/spec-first-study/m2-apply-review-1.md`). The files are
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/M2ApplyDraft.lean` ("apply Draft"),
`Proof/go_etcd_io/etcd/server/v3/etcdserver/M2ApplyDraft.lean` ("server Draft") and
`M2ApplyDraftSpecs.lean` ("specs Draft"). I checked them against `notes/m2-apply-plan.md` (items 1-21,
A1-A7, Q1-Q4, "Review round 1: the repair").

- **Go:** read at the pin `249d76bea7` (`/shared/etcd-grove/.lake/go-src/etcd`; the worktree has no
  `.lake/go-src`).
- **Not done:** nothing built, no Lean check run. Every claim below comes from reading the
  definitions; anything I could not check is marked *uncertain*.
- **Rubric:** `.claude/skills/spec/PRINCIPLES.md`, with examples `apply-uber-contract.md` and
  `apply-loop-merge.md`.

**No bug in the Go code was found.** Nothing goes to `issues/`. In particular:
- `applierV3backend.Compaction` reads `rr.Rev` only after `Compact` succeeded (`apply/backend.go:73-79`),
  and a read at the latest revision is never compacted.
- `updateCompactRev` tests `ErrCompacted` before `ErrFutureRev` (`storage/mvcc/kvstore.go:197-210`), as the
  drafted arms assume.
- `EtcdServer.Compact` overwrites the header's revision with `s.kv.Rev()` (`v3_server.go:422-429`).

## The brief's four questions

**(1) Is F-1's claim right that `updateCompactRev`'s `ErrFutureRev` branch contradicts the precondition?**
Yes. In the branch, the proof holds:
- `HcertC : idxCert γ.idx logc` and `HndC : sint.Z rev < logc.length` (the caller's;
  `store__updateCompactRev.lean:65`);
- the opened `revMuBody`'s `Hlog : idxLogAuth γ.idx (revQ γ q) log`, with `currentRev = W64(|log| - 1)`
  (`InvStore.lean:2941, 2951`);
- `Hif`, with `hl` turning the signed test into `sint.Z rev > |log| - 1` (`store__updateCompactRev.lean:207-212`).

`idxLogAuth_cert_prefix` (`InvIndex.lean:1162`) gives `logc <+: log`, so `rev < |logc| ≤ |log|`, which
contradicts `Hif`. `cmp_not_future` (apply Draft :336) is that argument and is correct.

Two cautions for the re-proof:
- `Hlog` is needed afterwards to close `revMuInv`. Use the `persistent_entails_right` pattern
  (`watchableStore__syncWatchers.lean:188`), or a `%`-destruct that keeps it, not
  `ihave … $$ Hlog HcertC`, which consumes it.
- The argument holds for every caller, `restore()`'s `compactLockfree` included, since `revMuBody` always
  holds `Hlog`.

Dropping a disjunct only strengthens the post, so the callers (`store__Compact.lean`,
`store__compactLockfree.lean`) lose a case and need no new fact. See S-3 for the texts item 18 should
also list.

**(2) Does `isServerReqD`'s second copy of the KV invariant cause a problem?** Opening it is not the
problem. Satisfying it is. See N-2: no caller can establish it with compaction on, so
`Compact.specD` as drafted is unusable.
- *Opening.* Both invariants are `inv kvN`, so a proof can open only one at a time. Opening either is
  sound, and no contradiction can be derived inside the proof.
- *Establishing.* Each copy owns half of the same raft mono-list (`srvRLog`, `SrvRaftLog.lean:380-381`),
  whose other half the server's log invariant owns (`SrvRaftLog.lean:10`). Each copy also owns half of
  `γk.st`. So with `E.cmp = true`, `NewServer`'s resources cannot make both copies, and no caller can
  supply `isServerReqD`.
- *Committing.* Even if both existed, the off copy (`kvInv`, `plainLog L`, `InvRequest.lean:237`)
  would forbid committing the compaction entry.

**(3) Does `srvKVCloserM_split` give `start` and the snapshot track what they need?** Yes:
- *`start`.* `→` at `c = -1` gives `cmpRight E (-1)`; with the pool's `kbWTSupplyM` that is
  `cmpOwn E (-1)`. Off, `srvKVCloserW` is today's `srvKVCloser`, so `start`'s off framing is unchanged.
- *The snapshot track.* `←` turns `srvKVCloserW ∗ cmpRight E c` (from `cmpOwn`) back into
  `srvKVCloserM s E c ∗ ⌜-1 ≤ c⌝`, which today's draft `restorePre_of_applyM`
  (`M2StorageDraftRestore.lean:329`) takes. After `Restore`, `snap_closer_after` gives
  `srvKVCloserM s E' c'`, and `→` at `E'` splits it again. That needs `-1 ≤ c'`, which comes from
  `crevOf_ge` once `x'.crev = crevOf γk A'` (item 17).

One cost: S-4, the mvcc internals spelled out in `srvKVCloserW`.

**(4) Do `dispatchOkM` and `Apply.specRecD` leave every compaction-off statement reading as today?**
For the apply package's internal statements (`dispatch.specD`, `Apply.specD`, `Apply.specRecD`),
nearly. `dispatchOkM false = dispatchOk` holds by `rfl`. What is left over:
- `cmpAdmit` (discharged by `cmpAdmit_nonCmp`);
- `cmpOwn E crev` at `-1` (off it is `⌜crev = -1⌝ ∗ True`, but only given `¬ kbCmpM E.γ.kb`: S-6's
  law);
- `applyResultIsD` (equal by `dispatchAnswerD_nonCmp`; at the switch the name is redefined in place).

For the server's trusted statements, no. See N-1:
- `applyEntryNormal`'s premise `entryOkM E.authOn x m` reads `entryOk`, which still reads `dispatchOk`
  (`InvApplier.lean:113-115`; `ApplyNormalOn.lean:47-56`). No mode is in scope there for `dispatchOkM`
  to take.
- Items 12 and 13 add `cmpEntryOk` in both modes.

## Round 1's findings at `HEAD`

| finding | status at `ce00aa140f` |
|---|---|
| F-1 (`ErrFutureRev`) | **fixed** (item 18, `cmp_not_future`); the argument checks against the proof (question 1). S-3: two more texts to list. |
| F-2 (trace on error) | **fixed**: `dispatchAnswerD`'s error arm has `tr = null` (apply Draft :224), `dispatchResultD` passes `v.Trace'` (:237). The request path carries it through `applyResultIs` inside `resPostM` (`ReqOn.lean:248-256`), redefined in place at the switch. |
| F-3 (mode tie) | **repaired with a new defect**: N-2. |
| F-4 (`compactPropOkD`) | **fixed**: `cmpEntryOk` carries it (server Draft :276), `compactPropOkD_of_entry`. |
| F-5 (fix-first ordering) | **fixed in form**: no `NoDelPutAt` in the Drafts. The plan now gates the switch on mvcc dropping it (Resume, item 3). `updateCompactRev.specD`'s post still names `compactJobPre`, which today has the premise: it is provable only after `compactJobPre` is redefined in place (listed in the plan). |
| F-6 (closer vs right) | **fixed**: `srvKVCloserW`, `srvKVCloserM_split` (question 3). |
| S-1 (`dispatchOk` in place) | **repaired with a new defect**: N-1. |
| S-2 (G2) | reformulated. A cheaper route is in S-2' below. |
| S-8 | fixed (`cmpAdmitRev`). |

## First-tier findings (new)

### N-1. The KV invariant and the entry premise still exclude compaction: S-1's repair left `dispatchOk` in the shape vocabulary (items 1, 5, 12, 13)

- **Principle:** Complete. The repair caused it: round 1's item 1 redefined `dispatchOk` in place, which
  made the shape chain admit a compaction "textually unchanged" (the plan's item 1 still says so). S-1's
  repair kept `dispatchOk` and added `dispatchOkM`, but nothing in the server's vocabulary reads
  `dispatchOkM`.
- **Evidence.**
  - `kvInvD` (server Draft :327-332) still holds `kvWork γ.raft γk L`.
  - The chain from there:
    - `kvWork` needs `logShape L` (`InvRequest.lean:216-217`);
    - `logShape` needs `entryShape` (`WorkloadDefs.lean:265-271`);
    - `entryShape` needs `rqShape` (`:259-260`);
    - `rqShape` needs `∀ on, dispatchOk on rq`;
    - `dispatchOk` needs `dispatchKind rq ≠ .compaction` (`InvUber.lean:63-65`).
  - So `kvInvD ρ.raft ρ.kv true` admits no compaction entry. `reqPropOkD`'s compaction form (:374,
    which carries `rqShapeD`) can never be committed (G4 is unprovable).
  - The same holds of `applyEntryNormal`'s premise. `entryOkM E.authOn x m` gives `entryOk x m` (off),
    which needs `dispatchOk x.chain.authOn rq` (`InvApplier.lean:113-115`). It gives `entryOkOn` (auth
    on), which needs the same (`ApplyNormalOn.lean:47-49`). And `logShapeOn`/`entryShapeOn` read
    `rqShape` (`KVAuthModel.lean:674-680`).
  - `x.chain` carries no compaction mode, so `dispatchOkM` has no argument to take there.
  - The family being removed had exactly this layer (`rqShapeC`, `entryShapeC`, `logShapeC`, `kvWorkC`,
    `CompactMode.lean:83-93, 161-163`). The Draft drops it without a replacement.
- **Callers affected:**
  - `kv_prop_au` (G4), and through it `EtcdServer.Compact`;
  - `applyEntryNormal` at a compaction entry (its premise is unsatisfiable), so `applyEntries` and
    `applyAll`;
  - `clusterWorkloadOk` (item 8, which transfers `logShape`).
- **Restatement.** Pick one of two:
  - **(a) The mode in the shape vocabulary**, following `apply-loop-merge.md`: `rqShapeM cmp rq :=
    (∀ on, dispatchOkM cmp on rq) ∧ …`, then `entryShapeM cmp`, `logShapeM' cmp` (and the `On` twins),
    `kvWorkM cmp`, and `entryOkM cmp on x m`. Each is the old one at `false` by `rfl`. `kvInvD` takes
    `kvWorkM cmp`. The cost: `applyEntryNormal.spec`'s premise gains the argument `E.cmp` (a text
    change, item 12), and so do `logShapeM`'s uses in `applyAll`/`run`.
  - **(b) Admit a compaction in `rqShape`/`entryOk` unconditionally** (`dispatchOkD`), and let
    `plainLogM cmp` and `cmpEntryOk γk cmp` carry the mode gate, which they already do: off,
    `cmpEntryOk` makes a compaction entry contradictory. The off texts keep their words but change
    meaning, through an `↔` law rather than `rfl`. This is round 1's original item 1, with `cmpEntryOk`
    now supplying the "not a compaction off".

  Either way, draft the chosen definitions (they are trusted vocabulary through `kvInv` and
  `applyEntryNormal`), and correct the plan's item 1 text, the apply Draft's `dispatchOkD` docstring
  (:62, "redefined in place at the switch", which contradicts :70) and `rqShapeD`'s docstring (server
  Draft :87-88, "`dispatchOk` being redefined in place").

### N-2. `isServerReqD` is unsatisfiable with compaction on, so `Compact.specD` is unusable as drafted, and `NewServer.specD`'s on arm unprovable (items 15, 19, 14)

- **Principle:** Complete (a caller must be able to establish the precondition); the text submitted
  for approval should be the switch text.
- **Evidence.**
  - `isServerReqD s E ρ := isServerReq s E ρ ∗ kvInvD ρ.raft ρ.kv E.cmp` (server Draft :397-398).
    `isServerReq` already contains today's `kvInv ρ.raft ρ.kv`, through `srvReqFieldsAt`
    (`InvProposer.lean:422`).
  - With `E.cmp = true`, the two are different invariants over the same names, each owning half of
    `srvRLog`'s mono-list and of `γk.st` (question 2). The server's log invariant holds the other half
    of the mono-list. No allocation can make all three.
  - The off copy's `plainLog` also forbids the compaction entry.
  - The same root cause hits `NewServer.specD`. Its pre gives only `kvInvD … E₀.cmp` (specs Draft :187),
    but its post's `srvBuilt` (today's text) contains `srvReqFieldsAt`'s `kvInv`, the off invariant,
    which the on-arm proof cannot produce.
  - Both drafts are meaningful only after `kvInv` is redefined in place (item 5) and `srvReqFieldsAt`
    gains the tie (item 19). `isServerReqD` is not that text.
- **Callers affected:**
  - `EtcdServer.Compact.specD`'s callers: `compactableOk_server` (`CompactEnv.lean:72-78`, restated
    over it) and, later, v3rpc's server-side `compactOk`;
  - the approval of items 14, 15 and 19.
- **Restatement.** Draft the switch text:

  ```lean
  srvReqFieldsAtD s E ρ v := … (today's, with) kvInvD ρ.raft ρ.kv E.cmp …
  isServerReqD s E ρ := (∃ v, srvReqFieldsAtD s E ρ v) ∗ ⌜E.authOn = false⌝
  ```

  `E.cmp` stands for `ρ.kv.cmp` until `KVNames.cmp` exists, and at the switch the conjunct
  `⌜ρ.kv.cmp = E.cmp⌝`. `isServerReqD_off` then follows by `kvInvD_off` and `rfl`.

  For `NewServer.specD`, say in its docstring that `srvBuilt`'s `kvInv` is the redefined one (item 5).
  The alternative is a `srvBuiltD` over `srvReqFieldsAtD`. Leave the statement unchanged.

## Second-tier findings

- **S-1'. Items 12 and 13 do not read as today when compaction is off.**
  - `cmpEntryOk γr.kv E.cmp A m` (and `cmpLogOk` for the batch) is added in both modes. Off callers must
    discharge it (`cmpLogOk_plain` from `plainLog`), so there are a few glue lines per caller.
  - With N-1 (a), the cheapest place for it is inside `entryOkM cmp` / `logShapeM' cmp`, not as a
    separate conjunct of the spec.
  - The plan's "every compaction-off statement reads as today" holds for `kvInvD`, `reqPropOkD` and
    `isServerReqD` (once N-2 is fixed). It does not hold for the apply-loop specs: say so in item 12.
- **S-2'. G2 has a cheaper route than an invariant law.**
  - `store.Read`'s spec already gives `mvcc.certOk γ log` of its read's log
    (`Spec/.../mvcc/store__Read.lean:50`). `readView.Rev` is `kv.Read(...)` then `tr.Rev()`
    (`mvcc/kv_view.go:32-36`). So `store.Rev.spec`'s post (today `idxCert` of the same log,
    `store__Rev.lean`) can also give `certOk γ log`, and `srvRevLb` can carry it.
  - `cmpReach γk r` then follows. `ρ.kv.cok = E.γ.cok` comes from `NewServer`'s premise and
    `envAgree`. `kvCertInv`'s `certMapOk` excludes the free `0 ↦ []`: every certified log is a model log
    of length at least 2 (`InvRequest.lean:394-404`).
  - This avoids exposing a law "under the store's invariant", which a client holding only
    `storeReaderC` may not reach, because `revMuBody` is a lock's resource, not an Iris invariant.
  - *Uncertain:* that `store.Rev`'s proof keeps `store.Read`'s `certOk` (it should: it is persistent);
    and, in the 3-member cluster, that every member's `E₀.γ.cok` is the cluster's `ρ.kv.cok`.
- **S-3. Item 18's list is incomplete.**
  - `store.compactLockfree.spec` keeps its own `ErrFutureRev` arm (`store__compactLockfree.lean:52-54`).
    It is true but now dead; drop it in the same step, or say why it stays.
  - `mvcc/Results.lean:476`'s docstring of `mvcc_store_Compact` names `ErrFutureRev`.
  - `store.Compact.spec`'s docstring (`store__Compact.lean:40-41, 49-50`) also needs editing.
- **S-4. `srvKVCloserW` spells out mvcc internals** (`watchableStore.stopc ↦□`, `stopCloser`,
  `wsWaiter`; specs Draft :51-55). It does so by unfolding the sealed `wsCloserR` through `wsCloserR_iff`.
  - This is coupling to mvcc's representation, already shared with the snapshot track's
    `restorePre_of_applyM`/`snap_closer_after` texts.
  - Better: mvcc exports a sealed `wsCloserW wsl` and the law `wsCloserR wsl st γ c ⊣⊢ wsCloserW wsl ∗
    compactRightR st γ c` (the existing `wsCloserR_split`/`_join` reshaped). `srvKVCloserW`'s on arm is
    then `∃ wsl, srvKVAddr s ↦□ … ∗ mvcc.wsCloserW wsl`. This is for the collaborator too, since their
    drafts carry the same four conjuncts.
- **S-5. Two sources of one mode.**
  - The uber specs gate the kind by `E.cmp` (`dispatchOkM E.cmp`) and the admission by `kbCmpM E.γ.kb`
    (`cmpAdmit`). `cmpOwn`/`cmpRight` and `srvKVCloserM/W` are gated by `kbCmpM E.γ.kb`.
  - Every off reading needs `kbCmpM E.γ.kb ↔ E.cmp`. That is S-6 of round 1, still to export: it should
    be a law of `AEnv`/`srvEnvOkD` the apply package can state, not something rederived per caller.
- **S-6. `Compact.specD`'s `⌜E.cmp = true⌝` is a scope restriction, not stated as one.**
  - Go serves a client's `Compact` RPC with the auto-compactor off (retention 0) as well. The model ties
    the store's compaction support to `retention ≠ 0` (`E₀.cmp = decide (retention ≠ 0)`), so a gRPC
    `Compact` on such a server is out of scope.
  - Say so in the docstring, and record it where M2's scope limits are kept (beside Q7 (a)'s `1 ≤ r`).
  - v3rpc's `compactOk` (`InvAuthAdmin.lean:154-163`) has none of `Compact.specD`'s premises (`1 ≤ r`,
    `srvRevLb`, non-physical, compaction mode). It cannot be built from `Compact.specD` for a general
    client request; that is a known gap, worth listing.
- **S-7. `cmpRespOk`'s header revision is information no caller reads.** `EtcdServer.Compact`
  overwrites it with `s.kv.Rev()` (`v3_server.go:429`). The fact is true and cheap: the Range is needed
  anyway, to show `rr ≠ nil`. Keep it, but say in the docstring that no caller uses it (the "know the
  margin" direction, not slack).
- **Vacuity check.** Nothing vacuous apart from N-2's unsatisfiable precondition. `cmpReach γk 1` holds
  by `kvCert`'s `length ≤ 2` arm, which is correct: revision 1 exists in `log0`.

## What is good

- **Apply Draft:**
  - `cmp_not_future` is the right lemma for item 18 (question 1).
  - `cmpAnswerIs` and `dispatchAnswerD` now say exactly what Go returns, the nil trace on every error
    included (`backend.go:73-75`, `corrupt.go:45`).
  - `dispatchAnswerD_nonCmp` keeps the other kinds unchanged.
  - `cmp_store_pre` is a real glue proof.
  - `dispatchOkM` is the right shape (N-1 is about where it is not used).
- **Server Draft:**
  - `crevOf` and its lemmas (`crevOf_step` with F-4's `hok`, `crevOf_mono`, `crevOf_pos`,
    `crevOf_plain`) are what the apply loop and the snapshot track need.
  - `cmpEntryOk` now carries the scope `Apply` needs.
  - `kvInvD_off` and `reqPropOkD_off` keep one family.
- **Specs Draft:** `srvKVCloserW`/`srvKVCloserM_split` resolve F-6 cleanly (question 3), and the
  configuration premise of `NewServer.specD` is no stricter than Go apart from the documented periodic
  mode.

## Per-item verdicts

| Item | Verdict |
|---|---|
| 1 `dispatchOkM` | blocked: N-1 (the shape vocabulary and `entryOk` do not read it); fix the stale docstrings |
| 2 `dispatchAnswer` with the trace | approvable |
| 3 apply vocabulary | approvable |
| 4 A1 record | approvable (round 1's S-5 cost) |
| 5 `kvInvD` | blocked: N-1 (`kvWork`'s `logShape` excludes compaction); then gated on mvcc dropping `NoDelPutAt` (F-5) |
| 6 `reqPropOkD` | approvable in text; its commit (G4) waits on N-1 |
| 7 `crevOf` | approvable |
| 8 `clusterWorkloadOk` | blocked with N-1 (it transfers `logShape`), and item 19's tie |
| 9 `cmpTriple` | approvable, over item 18 |
| 10 `Compaction.specD` | approvable, over item 18 |
| 11 `dispatch`/`Apply.specD` | approvable (S-5's law for the off reading) |
| 12 `applyEntryNormal` | blocked: N-1 (the premise excludes a compaction entry); S-1' |
| 13 `applyEntries`/`applyAll` | blocked with item 12; S-1' |
| 14 `NewServer.specD` | deferred by Q4; N-2 (the post's `srvBuilt` kvInv), S-6 of round 1 (S-5 here) |
| 15 `Compact.specD` | blocked: N-2; S-6 (scope); G2 (S-2') |
| 16 | withdrawn (Q2) |
| 17 snapshot track | the collaborator's; question 3: the split serves it; S-4 for them too |
| 18 mvcc specs without `ErrFutureRev` | approvable; S-3 (also `compactLockfree`, the two docstrings) |
| 19 the tie in `srvReqFieldsAt` | approvable as the switch text; the Draft's `isServerReqD` must become that text (N-2) |
| 20 `srvKVCloserW` | approvable; S-4 preferred |
| 21 `Apply.specRecD` | approvable |

## Ranking by need of revision

1. **Server Draft:** N-1 (a repair regression: the shape chain; decide between (a) and (b) and draft
   it), N-2's `isServerReqD`, S-1'.
2. **Specs Draft:** N-2 (`Compact.specD` over a satisfiable `isServerReqD`; `NewServer.specD`'s
   dependence on the redefined `kvInv` stated), S-6, S-4.
3. **Apply Draft:** stale docstrings (N-1), S-3, S-5. Its statements are otherwise ready.
