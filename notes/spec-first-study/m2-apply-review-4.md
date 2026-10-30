# M2 apply side, Draft: review round 4 (2026-10-30)

Reviewed: `m2-apply` at `6cafbc0b60` ("the switch stated in place", the user's Q6 (a)). Files: the
apply Draft (`etcdserver/apply/M2ApplyDraft.lean`), the server Draft (`etcdserver/M2ApplyDraft.lean`),
the specs Draft (`etcdserver/M2ApplyDraftSpecs.lean`), and the consolidated items 1-21 of
`notes/m2-apply-plan.md`, "The switch in place". I judged them under the in-place convention. I do
not re-raise "the off texts do not read as today by definition".

- **Checked:** `etc/lean-check.py -q -a` on the three Drafts: 0 errors.
- **Go:** at the pin `249d76bea7` (`/shared/etcd-grove/.lake/go-src/etcd`; the worktree has no
  `.lake/go-src`). I re-read `apply/backend.go:66-80`, `apply/corrupt.go:45-47`,
  `apply/uber_applier.go:143-145` and `v3_server.go:380-429`. The quota, capped and auth appliers do
  not override `Compaction`, so `chainCompacts` is right.
- **No Go bug found**, so nothing for `issues/`.

## Round 3's findings at `HEAD`

- **R3-1 (the middle of the chain read `logShape`): resolved for the shapes.**
  - Under item 1, `rqShape`/`entryShape`/`logShape` admit a compaction with their text unchanged.
    So `srvC` (`InvRun.lean:182-184`), `clusterWorkloadOk` (`InvBuild.lean:255-257`) and the
    apply-loop premises need no copy.
  - `kvInv` (item 5) gives `logShape` of the requested log, and `clusterWorkloadOk_of`
    (`BuildGap.lean:120-179`) transfers it to the committed log as it does today.
  - `run`'s proof (`EtcdServer__run.lean:59, 101`) reads `logShape (A ++ ce)` from `srvC`, which now
    admits the entry.
  - **The claims' half is still inconsistent:** `cmpLogOk`'s source for `run`. See S4-2.
- **R3-2 (`Compact.specD` held two KV invariants): resolved.**
  - With `kvInv γ γk := kvInvD γ γk γk.cmp`, there is one invariant per set of names.
  - `isServerReq`'s `kvInv ρ.raft ρ.kv` and `isServerRead`'s `kvInv γr.raft γr.kv`
    (`InvApplier.lean:333`) are the same persistent proposition when `γr = ρ.rd` (`ReqNames.kv` is
    `ρ.rd.kv`, `InvRequest.lean:772`).
  - Its mode is fixed by the names, so N-2's "two copies, each owning half of `srvRLog`" cannot
    arise.
- **S3-1 (the auth-on arm wider than the scope): resolved.**
  - `entryOkOnD` is gone, and `entryOkOn` keeps its text (`ApplyNormalOn.lean:47-49`).
  - The on arm still admits a compaction *textually*. Through item 1, `entryOkOn` reads
    `dispatchOk` and `entryShapeOn` reads `rqShape` (`KVAuthModel.lean:674-677`).
  - But `kvInvOn`'s `plainLogOn` excludes it (`plainEntryOn`: `plainReq` or `adminKindOk`,
    `KVAuthModel.lean:610-616`; `kvInvOn`, `:858-864`). The on proof reads that through
    `kv_log_plain_on` (`KVApplyOn.lean:405`).
- **S3-2 (stale plan texts): resolved** by the consolidated list, except as below (S4-1..S4-4).
- **S3-3 and S3-4: still open.** S3-3 is now the cheapest repair of S4-2.

## First tier

### R4-1. Item 19's tie has no producer: no `NewServer` statement that switches with items 5/19 relates `ρ.rd.kv.cmp` to `E₀.cmp`

- **Principle:** Sound/Complete (the postcondition must be provable from the precondition); the
  approved items are the switch's texts.
- **Evidence.**
  - Item 19 puts `⌜γr.kv.cmp = E.cmp⌝` into `srvKVInvs` (`InvApplier.lean:332-334`).
  - `srvKVInvs` is in `srvBuilt` (`#Hkvi`, `InvBuild.lean:328`, at `γr = ρ.rd`, `:339`). `srvBuilt`
    is the postcondition of:
    - `NewServer.spec` (`Spec/…/NewServer.lean:246`; the linked one, `Link.lean:2708`);
    - `NewServer.specCompact` (`:396`);
    - `NewServer.specM`'s off arm (`srvBuiltG false`, `:559`).
  - What these give:
    - `envAgree E E₀` gives `E.cmp = E₀.cmp`.
    - `NewServer.spec` and `specM` take `E₀.cmp = false` (`:152, :459`); `specCompact` takes
      `E₀.cmp = true` (`:302`).
    - None of the three constrains `ρ.rd.kv.cmp`. Their KV premise (`kvInv ρ.rd.raft ρ.rd.kv`,
      `:205, :355`; `kvInvM on …`, `:516`) is, under item 5, the invariant at whatever
      `ρ.rd.kv.cmp` is.
  - So after items 5/19 the postcondition's tie is unprovable at a `ρ` with
    `ρ.rd.kv.cmp ≠ E₀.cmp`.
  - Item 19 says "`NewServer` makes them from `ρ.rd.kv.cmp = E₀.cmp`". But no item adds that premise
    to these texts:
    - item 14 (`NewServer.specD`) is deferred by Q4, and its Draft encodes the tie as
      `kvInvD ρ.rd.raft ρ.rd.kv E₀.cmp` (specs Draft, `#Hkvinv`), a name the switch does not keep;
    - the interim `NewServer.spec`/`specCompact` texts under Q4 are not in the list. Round 1's S-4
      listed them; the consolidated list dropped them.
- **Callers affected:**
  - every example over `NewServer` (`examples/common/newServer.lean:42, :138`;
    `examples/common/Defs.lean:198`, the member's boot bundle `kvInv ρ.rd.raft ρ.rd.kv`;
    `Alloc3.lean:80-105`);
  - `start` (its `isServerReq`/`isServerRead` come from `srvBuilt`);
  - so `Compact.specD` (item 15), which needs `ρ.kv.cmp = true` from the tie.
- **Restatement.** Add one item, 19b, for the texts that switch with 5/19:
  - `NewServer.spec`, `NewServer.specM`: `ρ.rd.kv.cmp = E₀.cmp →`, beside `ρ.rd.kv.c0 = W64 0 →`.
    Equivalently `ρ.rd.kv.cmp = false`, given their `E₀.cmp = false`.
  - `NewServer.specCompact` (until item 14): the same, so `ρ.rd.kv.cmp = true`.
  - `newServer.spec`/`specCompact` and the examples' allocation: `kvInv` allocated at the chosen
    mode. This needs an allocation law at any `cmp`: a boot log is plain, so `plainLogM cmp` and
    `cmpLogOk_plain` hold.
  - In the specs Draft, write `NewServer.specD`'s `#Hkvinv` as `kvInv ρ.rd.raft ρ.rd.kv` with
    the premise `ρ.rd.kv.cmp = E₀.cmp`. That is the Draft's own convention ("texts name the
    definitions the switch keeps").
  - Mark the premise as the scope restriction it is (S4-5).

Nothing else is in the first tier.

## Second tier

### S4-1. Item 19 misses a carrier: `srvReqFieldsAtM` (the merged request path)

- `srvReqFieldsAtM on` (`ReqOn.lean:375-394`) is a text copy of `srvReqFieldsAt` with
  `kvInvM on ρ.raft ρ.kv srvAuthSt0`. At `on = false` that is `kvInv ρ.raft ρ.kv`, at names whose
  mode no tie relates to `E.cmp`.
- Today `srvReqFieldsAtM_false` and `isServerReqM_false` hold by `rfl` (`ReqOn.lean:400, 564`). The
  second is used 14 times (`ModeSpecs.lean:1128-1349`, `EtcdServer__Put.lean:152`,
  `__DeleteRange.lean:152`, `__Range.lean:729`, `__Start.lean:102-139`).
- The merged request-path specs are written over `isServerReqM E.authOn`: Put, Range, Txn,
  DeleteRange, `processInternalRaftRequestOnce`, `raftRequest`, `doSerialize`,
  `parseProposeCtxErr`, `monitorStorageVersion`, `start`/`Start`'s on arms, examples'
  `Serve.lean`.
- With the tie in `srvReqFieldsAt` only, both `rfl`s break. The direction the callers use today
  (plain → M, dropping the tie) still holds as an entailment, so nothing becomes unprovable.
- But the auth merge's convention (one spec, the mode the environment's) would put `Compact.spec`
  over `isServerReqM E.authOn` too, and there the tie would be missing.
- **Restatement:** item 19 adds `⌜ρ.kv.cmp = E.cmp⌝` to `srvReqFieldsAtM` as well. In both arms is
  simplest; with `kvInvOn` the on arm is vacuous. That keeps both `rfl` laws.

### S4-2. Items 8/13/12: the source of the committed claims is inconsistent; S3-3 removes the problem

- Item 13: "`run.spec` unchanged if `srvC` or `clusterWorkloadOk` carries `cmpLogOk` (item 8)". But
  item 8 changes only `clusterWorkloadOk(M)`, and `run` reads its per-batch facts from `srvC`
  (`EtcdServer__run.lean:50, 59`), which keeps its text. So the condition item 13 relies on is not
  what item 8 provides.
- `run` can still get the claims, which is why this is second tier:
  - `srvC` holds `srvRLogLb ρ.raft L` (`InvRun.lean:184`), and `isServerRun` holds `srvKVInvs` (the
    invariant and, with item 19, the tie).
  - A G1-type lemma `srvRLogLb γ L ∗ kvInv γ γk ⊢ |={⊤}=> ⌜cmpLogOk γk γk.cmp L⌝` gives them at any
    batch. In the on mode, `kv_log_plain_on` plus a one-line `cmpLogOk` of a `plainLogOn` log does
    the same.
- **Restatement (recommended), S3-3:**
  - State that lemma once and use it inside `applyEntryNormal`'s proof
    (`srvRLogLb γr.raft (A ++ [m])` is already in its precondition), which gives `cmpEntryOk`.
  - Drop item 8 entirely, item 12's `⌜cmpEntryOk …⌝`, and item 13's three `⌜cmpLogOk …⌝`. Four
    trusted texts then stay unchanged, and no caller writes glue.
  - Otherwise, rewrite item 13 to name the actual source (the lemma) and drop the conditional.

### S4-3. Item 5 omits what the in-place `kvInv` takes from its proofs (key question 1)

The lost fact is **`plainLog` of the committed log**, not anything about `dispatchOk`:
- `kv_log_plain` (`KVApply.lean:136-160`) concludes `plainLog B`. Under item 5 only
  `plainLogM γk.cmp B` holds, so its statement must change.
- Its three users:
  - `EtcdServer__applyEntryNormal.lean:272-276`: today `plainCover rq` for `srvRest_apply` at
    `:391, :593`;
  - `KVApply.lean:203` (`kv_applied_step`);
  - `SnapRecvFacts.lean:359`: the snapshot track's.
- The `plainLog` lemmas over the model, at their call sites:
  - `kvModelSt_plain` (`KVLemmas.lean:64`, used `:361, :424, :528`; `ReadOn.lean:372`);
  - `kv_fire_reads` (`KVLemmas.lean:470`, used `:492, :517, :610`);
  - the invariant's step (`KVLemmas.lean:198-201`);
  - `KVModelRestore.lean:193-240` (`plainLog A → LogNoLease`, `IdxWf`).
- Each needs a `plainLogM` version.
  - They are true: a compaction is neither a `storeKind` nor a `writeKind`, so `kvEntry` and the
    lease table leave it alone.
  - They are mechanical, but they are a new proof obligation in every mode-generic proof.
  - The off laws (`plainLogM_false`) cover them only at `γk.cmp = false`, which a caller reaches
    through the tie.
- Item 17 should list `SnapRecvFacts`/`KVModelRestore` for the collaborator.
- The image's "never compacted" claim rests on `dispatchOk` (`mvcc/Image.lean:6-9`); the storage
  side's `dbImageR` replaces it. Item 17 should say they switch together.
- **Cheap improvement:** put `cmpLogOk` **last** in `kvInvD`'s pure conjunction (server Draft,
  `kvInvD`), not second.
  - The positional proofs then keep their indices: `Hok.2.2.2.1` in `KVChainOff.lean:45` and
    `KVApply.lean:160`; `Hok'.2.2.1` in `KVApply.lean:290`; `Hok.2.2.2.1/2` in
    `KVLemmas.lean:347, :410`; `BuildAlloc.lean:137, :180`.
  - Today it shifts every index after the first.
- Also list the `CompactMode.lean` family's removal:
  - `kvInvC`, `srvReqFieldsAtC`, `isServerReqC`, `reqPropOkC`, `dispatchOkC`, `rqShapeC`,
    `logShapeC`, ...;
  - its users `CompactEnv.lean:74` (`compactableOk_server`, to restate over
    `isServerReq ∗ ⌜E.cmp = true⌝`, round 1's S-4), `StartCompactingServer.lean`,
    `putgetc/MainLinked.lean`, and `processInternalRaftRequestOnce.specCompact`.
  - The older item 5 text said this; the consolidated one does not.

**Key question 1, place by place.** The places that rely on `dispatchOk` excluding a compaction:

| place | relies on it for | after item 1 |
|---|---|---|
| `uberApplier__dispatch.lean:475-480` (compaction case) | `absurd hk Hok.2.1` | the new arm: `dispatch.specD` (item 11) states it |
| `DispatchKVL.lean:722-727`, `DispatchAdmin.lean:469-474` | nothing: closed by `isKVKind`/`adminKindOk` (their own premises) | unchanged |
| `ApplyKVL`, `ApplyFnKVL:78/118`, `ApplyAdmin(L)`, `ApplyFnAdmin(L)`, `AdminEntryOn.lean:72` | nothing (`isKVKind`/`adminKindOk`) | unchanged; A1's `applyKV` (`cmpOwn`) and `applyStep` (crev) are framed, by `dispatchCrev_nonCmp` |
| `default` panics: `uberApplier__dispatch.lean:694`, `DispatchKVL.lean:916` (`Hok.2.2.1`), `DispatchAdmin.lean:930` (`Hdok.2.1`); `InvMonitors.lean:65`, `WorkloadDefs.lean:288` (3-tuples) | positional `≠ .none` | mechanical (one index); better a law `dispatchOk_some : dispatchOk on rq → dispatchKind rq ≠ .none` |
| off apply loop (`applyEntryNormal`'s off arm) | the exclusion comes from `kv_log_plain`, not `dispatchOk` | lost in compaction mode; restored by `cmpEntryOk` at `E.cmp = false`, else the new arm (S4-3) |
| `KVChainOff.lean` | nothing (the start chain) | positional only |
| auth mode (`entryShapeOn`, `kvWorkOn`, `logShapeOn`, `entryOkOn`) | nothing: `kvInvOn`'s `plainLogOn` excludes it | unchanged; `cmpEntryOk`/`cmpLogOk` vacuous there |
| request path (`reqPropOk`'s forms, `InvRequest.lean:462-474`; `reqPropOkOn`, `ProposeOn.lean:340-356`) | nothing: every form has `plainReq` | a compaction can enter only through item 6's form |

### S4-4. Item 6's in-place form is not stated

- `reqPropOkD`'s first disjunct is `reqPropOk` itself (server Draft, `reqPropOkD`). An in-place
  redefinition would refer to itself, so the old body needs a name (`reqPropOkPlain`).
- The mode also has to be given. It must be `γk.cmp`:
  - G4's commit step keeps `plainLogM γk.cmp` from the form's `cmp = true`;
  - `reqPropOkM false` (`ReqOn.lean:582`) reads `reqPropOk γk rq Qr` with no mode argument.
- **Restatement:** "`reqPropOk γk rq Qr := reqPropOkPlain γk rq Qr ∨ (compaction form at
  γk.cmp)`".

### S4-5. The tie is a scope restriction: mark it

- Go lets members of one cluster run different compactor settings.
- A member with retention `0` still applies a committed `Compaction`:
  - `applierV3backend.Compaction` calls `KV.Compact` whatever the member's configuration
    (`backend.go:66-73`);
  - `uber_applier.go:143-145` dispatches it on every member.
- With one `KVNames` for the cluster (the plan's 3-member scope: "`kvInvD … cmp` once for the
  cluster") and the tie per member, every member must have `E.cmp = γk.cmp`. A mixed cluster is out
  of the model.
- The server Draft's header says "one for every member", but no docstring marks this as a scope
  restriction ("No unneeded premise": mark and file it).
- **Restatement:** say it in R4-1's premise (`NewServer`'s docstring) and in `notes/decisions.md`:
  every member in the cluster's mode, Go being more liberal.

### S4-6. Key question 4: `kvInvD_off` is the right evidence, not the right law for callers after the switch

- What it shows: `kvInvD γ γk false ⊣⊢ kvInv γ γk` (server Draft, proved; checked) is what shows
  the off texts mean today's.
- After the switch its right-hand side no longer exists (item 5 replaces `kvInv`), and its
  left-hand side is not `kvInv` (whose mode is `γk.cmp`).
- What an off server's callers need instead:
  - (a) `kv_log_plain_off : γk.cmp = false → … ⌜plainLog B⌝`, the fact the off proofs read (S4-3).
    Or the general `plainLogM γk.cmp B` with `plainLogM_false`.
  - (b) The tie, to get `γk.cmp = false` from `E.cmp = false` (`srvKVInvs`, item 19).
  - (c) An allocation law at any mode (R4-1).
- Clients never open `kvInv`: no `client/v3` or `v3rpc` file unfolds it. So a `⊣⊢` at the switch is
  needed only if the old body is kept under a name, as `γk.cmp = false → kvInv γ γk ⊣⊢
  kvInvPlain γ γk`.
- The same holds of `srvReqFieldsAtD_off`/`srvKVInvsD_off`: their switch forms are
  `ρ.kv.cmp = false`-guarded projections, not equations to a vanished text.
- **Restatement:** list (a)-(c) as item 5's off laws. Keep `kvInvD_off` in the Draft as the
  evidence.

### S4-7. Clients unfold `srvKVInvs` positionally; the tie breaks them

- These files destructure `srvKVInvs`'s four conjuncts:
  - `client/v3/InvServerKV.lean:275-276` (`⟨#HkI, #HcI, #HrI, %Hcok⟩`);
  - `api/v3rpc/HistoryModel.lean:339-340, 380, 535`;
  - also the server's `KVRead.lean:113`, `ReadOn.lean:318`, `SnapRecvFacts.lean:339, 430`,
    `KVApply.lean:199`, `EtcdServer__start.lean:508, 538`, `EtcdServer__apply.lean:172`,
    `EtcdServer__applyEntryNormal.lean:261, 270`, `AppliedOn.lean:330, 357`.
- A fifth conjunct breaks every one of them. Two are other packages ("a client does not unfold
  another package's definitions").
- **Restatement:** with item 19, export `srvKVInvs_kv`/`_cert`/`_raftLog`/`_cok`/`_cmp`
  projections, and move the two client packages onto them.

### S4-8. Round 3's leftovers, still open

- S-5: the `kbCmpM E.γ.kb ↔ E.cmp` law. It is needed by `cmpAdmit_of_entry`'s `hkb` and by
  `start`'s off `cmpOwn E (-1)`, which comes from `cmpOwn_off`'s mode. Until item 14 the
  compaction-mode `start` has no right to hand to the apply thread: `specCompact`'s post has
  `srvKVCloser`, F-6. That is Q4's deferral, but item 14 should say so.
- S-2': `cmpReach`'s docstring still gives the `idxCert ⊢ certOk` law as the closable form.
- S-4: `srvKVCloserW` unfolds `wsCloserR`.

## What is good

- **The in-place restatement is the right call.** It closes the class of finding rounds 1-3 kept
  producing:
  - one `kvInv` per set of names (R3-2 gone);
  - shapes that admit a compaction everywhere (R3-1's shapes gone);
  - the gate in one place (`plainLogM` by the names' mode, the entry's claim). That matches
    "one spec per function; a mode is part of the state".
- **The apply Draft is unchanged in substance and ready.**
  - `dispatchOkD_iff` is the right off law.
  - `cmpAnswerIs`/`dispatchAnswerD` match Go: the error arm `nil, ch, nil, err` and the corrupt
    applier's `nil, nil, nil, ErrCorrupt`.
  - `cmp_not_future` and `cmp_store_pre` stand.
- **The server Draft.**
  - `kvInvD_off` is now a real `⊣⊢` (through `inv_iff`). `logShapeD_plain`/`entryShapeD_plain` show
    the shapes are today's on plain logs.
  - `srvReqFieldsAtD`/`srvKVInvsD` are faithful one-conjunct edits, with off laws.
  - `crevOf` and its lemmas, `compactPropOkD`, `cmpEntryOk`/`cmpLogOk` and `cmpAdmit_of_entry` are
    as round 3 found them.
- **The specs Draft.** `Compact.specD` is over the kept names, with S-6's scope sentence, and
  `srvKVCloserM_split` stands.
- **Vacuity:**
  - `cmpEntryOk`'s `cmp = true` makes the off server's claim exclude a compaction, so it is not
    vacuous off;
  - `reqPropOkD`'s compaction form is reachable (`compactPropOkD_irrCompaction`, `cmpReach γk 1`
    through `kvCert`'s start arm);
  - `chainClass`/`reqClass` of a compaction is `True` (`AuthClass.lean:335`), so the uber's
    postcondition is provable for the new arm;
  - `certPre` of a compaction is either vacuous (`backendStep .compaction = False`,
    `Chain.lean:226`) or, through the corrupt chain, of the unchanged log.

## Per-item verdicts

| Item | Verdict |
|---|---|
| 1 `dispatchOk` in place | approvable. Proof cost: the positional `≠ .none` uses (S4-3 table); add `dispatchOk_some` |
| 2 `dispatchAnswer`/`dispatchResult`/`applyResultIs` with the trace | approvable (old body inlined in the `else`) |
| 3 apply vocabulary | approvable; matches the Draft |
| 4 A1 record | approvable; list the internal `Apply` triples (`ApplyFnKVL`, `ApplyFnAdmin(L)`) that frame `cmpOwn` |
| 5 `kvInv` in place | approvable in text. List the `kv_log_plain`/`plainLog` lemmas (S4-3), the `CompactMode` family's removal, the post-switch off laws (S4-6), and `cmpLogOk` last |
| 6 `reqPropOk`'s compaction form | approvable once restated in place (S4-4: the old body named, mode `γk.cmp`) |
| 7 `crevOf` | approvable |
| 8 `clusterWorkloadOk(M)` + `cmpLogOk` | **drop** (S4-2: `run` does not read it; S3-3's lemma instead) |
| 9 `cmpTriple` in `applierTriples` | approvable |
| 10 `Compaction.specD` | approvable |
| 11 `dispatch`/`Apply.specD` | approvable (S-5's law for the off reading) |
| 12 `applyEntryNormal`'s `cmpEntryOk` | approvable; cheaper without it (S4-2/S3-3) |
| 13 `applyEntries`/`applyAll`/`EtcdServer.apply` `cmpLogOk` | text inaccurate (`run`'s source, S4-2); approvable if restated or dropped by S3-3 |
| 14 `NewServer.specD` | deferred (Q4); its `#Hkvinv` in the switch's names (R4-1); note the compaction-mode right's absence until then (S4-8) |
| 15 `Compact.specD` | approvable (R3-2 resolved); its producer needs R4-1; `compactableOk_server`'s restatement to list |
| 16 | withdrawn |
| 17 snapshot track | the collaborator's; add `SnapRecvFacts`/`KVModelRestore`'s `plainLog` uses and the image's compaction keys (S4-3) |
| 18 mvcc without `ErrFutureRev` | approvable |
| 19 the ties | **R4-1** (no producer: a `NewServer` premise in spec/specM/specCompact and the examples' allocation); add `srvReqFieldsAtM` (S4-1); export projections (S4-7); mark the scope (S4-5) |
| 20 `srvKVCloserW` | approvable (S-4 at the switch) |
| 21 `Apply.specRecD` | approvable |

## Ranking by need of revision

1. **The plan's item list:**
   - R4-1 (item 19b: the `NewServer` premise and the examples' allocation at the mode);
   - S4-1 (`srvReqFieldsAtM`);
   - S4-2 (items 8/12/13: adopt S3-3, or fix item 13's source);
   - S4-3/S4-4 (item 5's proof list and the `CompactMode` removal; item 6's in-place form);
   - S4-5 (the scope).
2. **Specs Draft:** `NewServer.specD`'s `#Hkvinv` in the kept names with the premise (R4-1).
3. **Server Draft:** `cmpLogOk` last in `kvInvD` (S4-3); the post-switch off laws (S4-6).
4. **Apply Draft:** nothing in the first tier; `dispatchOk_some` (S4-3); S-5's law.

**The first tier is not empty, but it is small:** R4-1 only, one premise in three `NewServer`
texts and the matching allocation in the examples. I found nothing else wrong, unprovable, or
unusable under the in-place convention. Every other carrier of `kvInv` is either tied (through
`srvKVInvs` or `srvReqFieldsAt`), co-carried with `srvKVInvs` (`srvReqBuilt` in `srvBuilt`), or
in the auth-on family, which excludes compactions on its own (`kvInvOn`).
