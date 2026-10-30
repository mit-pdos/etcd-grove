# Plan: M2, the apply side (spec-first; branch `m2-apply`)

Status (2026-10-30): **review round 2 repaired** ("Review round 2: the repair", the last
section: N-1, the shapes by the mode; N-2, the request path's view drafted as the switch's text).
Before: review round 1 repaired ("Review round 1: the repair"). Nothing switched.

**Resume here.**
1. *Done so far.* Draft modules `etcdserver/apply/M2ApplyDraft.lean`, `etcdserver/M2ApplyDraft.lean`,
   `etcdserver/M2ApplyDraftSpecs.lean` (imported by nothing; no `axiom`/`sorry`), repaired for review
   round 1 (`notes/spec-first-study/m2-apply-review-1.md`); targeted build passes. The `NoDelPutAt`
   fork fix is on `lean` since 2026-10-28; the Drafts are now stated in its form (no `NoDelPutAt`),
   so dropping the premise from mvcc's specs gates the switch (F-5).
2. *Next step: review round 3* (a fresh `spec-reviewer`, against rounds 1-2's reports and the
   repair sections), then its repair; the rounds end when one has nothing in the first tier.
3. *Then* the user's approval batch: Q5 (items 1-16 as repaired, and the new items 18-21 below),
   dropping `NoDelPutAt` from mvcc/server specs (`store.Compact.spec`, `compactLockfree`,
   `updateCompactRev`, `crevSafe`/`delKey`/`compactJobPre`, `CompactMode`'s clause, `irrNoDelPut`;
   `check_gives_nodup`'s `noFromKeyDelL` needs a proof attempt), F-1's `ErrFutureRev` arm (item 18).
4. *Still blocked elsewhere:* `applyAll`/`run`'s merge (the auth-mode merge, after the snapshot
   track's SNAPSHOT-SORRYs #7/#8); the snapshot track's drafts (the collaborator switches them:
   `notes/m2-storage-plan.md`; item 17 now takes `srvKVCloserW`, F-6).

**Environment.** Worktree `/shared/etcd-grove-m2a` (branch `m2-apply`, local, unpushed; its
`.lake/build` is a fresh full build). Build with `lake build --packages=<manifest>` where the manifest
is `lean`'s `lake-manifest.json` with the `perennial` entry `{"type": "path", "dir":
"/shared/perennial-6da88b280", ...}` (the pin `6da88b280`; check `lake-manifest.json` first: if
`lean` moved the pin, use a checkout at the new one); `LAKE_OPTS=--packages=<manifest>` for
`etc/tcb-report.py`; `PERENNIAL_DIR=<that checkout>` for `etc/gen-init.py`. The paused branch `m2`
(worktree `/shared/etcd-grove-cp`) is reference only: superseded by `m2-apply`, delete it when this
branch lands.

M2's plan is `notes/m2-plan.md`; the storage side (merged) is `notes/m2-storage-plan.md`; the
paused `m2` branch's drafts were read for ideas only (it is 277+ commits behind: its `compactStep`,
its `cmpLogOk`, its "Compaction triple in `applierTriples`" are re-done here over today's specs).

## Scope (the brief, 2026-10-30)

The apply side's compaction, on the merged parts: the KV model and invariant admitting compaction
entries (the "one KV invariant" of M2's round-1 decision), the compaction revision of the committed
log modelled; `applierV3backend.Compaction`'s spec and the compaction arm of the apply package and
`applyEntryNormal`; `NewServer.spec` merged with `specCompact`; what `applyAll`/`run` need (stated,
not merged: the auth merge merges them after the snapshot proofs); the 3-member `putgetc` (scoped,
not built); `NoDelPutAt` (what the upstream fix would remove; not done).

## The user's decisions in force

One family (the mode in the state and the names: `AEnv.cmp`, `StoreNames.cm`; one spec per
function); a 3-member cluster, restore working in compaction mode (the storage side drafted it; the
snapshot track's statements are the collaborator's); watchers excluded in compaction mode,
client-side (`noCompactor`); the compaction revision logical across a restore (`c ≤ c'`, Q5 (a)),
the apply side modelling the compaction revision of the committed log; no compaction at revision 0
(Q7 (a): `EtcdServer.Compact.spec`'s `1 ≤ r`, `compactPropOk`, `plainLogC_compaction_pos`);
`store.Compact` takes the write-back supply (`kbWTSupplyM`, from one token stock per backend sharing
the pool's receipt counter, Q1 (a)/Q4 (a)); the auth merge's convention (one spec, the mode the
environment's).

## The Drafts (`0a88a357f8`)

- `Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/M2ApplyDraft.lean`: the apply package's arm.
- `Proof/go_etcd_io/etcd/server/v3/etcdserver/M2ApplyDraft.lean`: the KV model and invariant.
- `Proof/go_etcd_io/etcd/server/v3/etcdserver/M2ApplyDraftSpecs.lean`: `NewServer.specD`,
  `EtcdServer.Compact.specD`, generated from today's texts (every change marked `(M2, the apply
  side, Draft)`).

## Decided by the agent (options and reasons; for the user to reverse in a batch)

- **A1. The compaction revision is a field of the apply state's record.** At the switch
  `apply.ApplyKV` gains `crev : Int := -1`; `apply.applyKV E ua x` gains `cmpOwn E x.crev`;
  `apply.applyStep`'s dispatched case gains `x'.crev = applyCrev rq v3 x.chain x.crev out` (skipped
  and rejected: `x' = x`); the server's `kvApplied γ γk A x` gains `⌜x.crev = crevOf γk A⌝`. Then
  `entryStep`, `entriesStep`, `srvApplyKV(M)`, `kvApplied(M)` carry it by definition, and the texts
  of `applyEntryNormal.spec`, `applyEntries.spec`, `applyAll.spec`, `run.spec` do not mention it.
  The Drafts state the apply package's specs with the revision as an explicit `crev` (equivalent;
  `crevOf_step` is the step at `x.crev`). Rejected: a separate `cmpOwn E (crevOf γk A)` conjunct in
  each of the four apply-loop specs (four trusted texts change instead of four definitions).
- **A2. The right lives in the apply thread's state, not in the KV's closer.** `NewServer` hands
  out `srvKVCloserM srv E (-1)` (the storage side's draft: on, the watchable store's own parts and
  the inner store's restorable right); `start` splits it (`wsCloserR_iff`, public) into the
  watchable store's own parts (kept as the closer) and `cmpRight E (-1)` (into `applyKV`), and adds
  the supply from the pool it allocates (`kbWTSupplyM_of_poolR`, the storage side's draft). So
  `restorePre_of_applyM` (D22's draft) takes the right from `apply.cmpOwn` (with `kvOwn`, which it
  already takes) and `srvKVCloserM`'s on arm loses it: a change to two of the snapshot track's
  drafts, for the collaborator. Rejected: the right kept in `srvKVCloserM` and that predicate
  threaded through `run`/`applyAll`/`applyEntries`/`applyEntryNormal` (four more statement changes,
  and the closer would leave `NewServer`'s post for the apply loop anyway).
- **A3. The supply rides with the right** (`cmpOwn E c := cmpRight E c ∗ kbWTSupplyM E.γ.kb`,
  persistent part), made at `start` and, after an install, from the new backend's stock
  (`snap_supply_before`, D22's draft). Rejected: a per-call `srvWTPool` premise on
  `applyEntryNormal` (a statement change, and a later credit per compaction).
- **A4. A compaction is not a state change of the clients' KV.** `KVState` (`compacted := 0`,
  `kvModelSt`) and `dispatchStep` are unchanged: a compaction is not a `storeKind`, so its outcome
  leaves the log, and it changes no value at a revision it keeps; the compaction revision is visible
  to readers only through the store (`storeReader = storeReaderC`, `crevLb`), and to the apply
  thread through `crevOf`. Rejected: `KVState.compacted` raised (every client spec over `kvAu` would
  see compaction; no M2 result needs it).
- **A5. `NoDelPutAt` from the admitted writes, in compaction mode only, until the fork fix.**
  `kvInvD`'s `cmp = true → ∀ c, NoDelPutAt (kvModel γk L) c`, kept by `reqPropOkD`'s
  `cmp = true → irrNoDelPut rq` on every write form; a put or a delete meets it by its kind (to
  prove: `irrNoDelPut_put`/`_delete`), a transaction by its caller (a premise of `EtcdServer.Txn`
  in compaction mode: Q2 below). `putgetc` issues only puts and gets. Rejected for now: the fork
  fix first (the user's decision (b) of round 1, not this step's: listed below).
- **A6. A compaction in scope dispatches on every member** (`compactPropOkD`: `compactPropOk` and no
  side-effect-free or admin field beside it), so the model's `kvCrevEntry`, which ignores skipping
  as `kvEntry` does, is exact (`crevOf_step`). `Compact`'s request has nothing else set
  (`compactPropOkD_irrCompaction`).
- **A7. A compaction's revision is reached at the model, not at the proposer's store.** In a
  3-member cluster the proposer's store is not the applier's: `reqPropOkD`'s compaction form
  carries `cmpReach γk r` (a KV certificate `kvCert` of a longer log: by `kvCertInv` the model of a
  committed raft log, or one of the start's two revisions), and the KV invariant records it at the
  commit as a revision of the model before the entry (`cmpLogOk`). Rejected: today's `srvRevLb E.γ r`
  carried as is (a certificate of the proposer's own store, meaningless at another member).

## The drafted statements

Trusted/exported = the statement of a linked result exported in a `Results.lean`, or a definition
such a statement is written in. "Snapshot track" = the collaborator's (D22).

**Definitions (redefined in place at the switch).**
1. `apply.dispatchOk` → `dispatchOkD` (trusted vocabulary: `dispatch`/`Apply`'s premise,
   `entryOk`, `rqShape`, `logShape`):
   ```lean
   def dispatchOkD (on : Bool) (rq : IRRModel) : Prop :=
     dispatchKind rq ≠ .none ∧ (dispatchKind rq = .authEnable → on = true)
   ```
   `rqShape`, `entryShape`, `logShape`, `kvWork` then admit a compaction textually unchanged
   (`rqShapeD` in the Draft only because `dispatchOk` is not redefined there).
2. `apply.dispatchAnswer` gains the compaction case (`dispatchAnswerD`, trusted vocabulary of
   `dispatchResult`): `∃ rp, resp = mkOk (*CompactionResponse) rp ∗ ((err = nil ∗ cmpRespOk log rp)
   ∨ ⌜rp = null ∧ err ≠ nil⌝)`, `cmpRespOk` the owned response with its owned header at revision
   `log.length - 1`.
3. New apply vocabulary (`apply/M2ApplyDraft.lean`, exact texts there): `chainCompacts`,
   `cmpRevAfter`, `dispatchCrev`, `applyCrev`, `cmpAdmit kb log rq` (compaction → `kbCmpM kb` and
   `rev < log.length ∧ NoDelPutAt log rev`), `cmpRight`, `cmpOwn`, `cmpRespOk`, `cmpAnswerIs`.
4. A1's record changes: `ApplyKV.crev`, `applyKV`'s `cmpOwn E x.crev`, `applyStep`'s crev clause,
   `kvApplied`'s `x.crev = crevOf γk A` (and `kvAppliedOn`'s, the auth mode's).
5. `kvInv` → `kvInvD` with `KVNames.cmp` (trusted: `NewServer.spec`'s pre, the request path's
   `isServerReq`):
   ```lean
   def kvInvD (γ : ServerRaftNames) (γk : KVNames) (cmp : Bool) : IProp GF :=
     inv kvN iprop(∃ L : List EntryModel,
       srvRLog γ L ∗ ghostVar γk.st (1 : Qp).half (kvModelSt γk L) ∗
       ⌜plainLogM cmp L ∧ cmpLogOk γk cmp L ∧
         (cmp = true → ∀ c, mvcc.NoDelPutAt (kvModel γk L) c) ∧
         srvIdxOkW γ.ai0 L ∧ uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧
         γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ []⌝ ∗ kvWork γ.raft γk L)
   ```
   with `plainEntryM cmp m` (a plain request, or `cmp = true ∧ compactPropOkD rq`), `cmpLogOk`
   (every compaction entry at `i` claims at `kvModel γk (L.take i)`: `cmp = true`, `r < length`,
   `NoDelPutAt`). **At `cmp = false` it is today's `kvInv`** (`kvInvD_off`, an equation, proved).
   `CompactMode.lean`'s family (`kvInvC`, `kvWorkC`, `compactClaims`, `isServerReqC`,
   `srvReqFieldsAtC`, `reqPropOkC`, `dispatchOkC`, `rqShapeC`, `entryShapeC`, `logShapeC`,
   `plainEntryC`, `plainLogC`) goes; `compactPropOk`, `irrCompaction`, `irrNoDelPut`,
   `compactResultIs` stay.
6. `reqPropOk` → `reqPropOkD` (trusted: `processInternalRaftRequestOnce.spec` through
   `reqPropOkM`'s off arm; the on arm unchanged, auth-on servers keep `retention = 0`):
   ```lean
   def reqPropOkD (γk : KVNames) (cmp : Bool) (rq : apply.IRRModel)
       (Qr : List EntryModel → IProp GF) : IProp GF :=
     iprop((reqPropOk γk rq Qr ∗ ⌜cmp = true → irrNoDelPut rq⌝) ∨
       (⌜cmp = true ∧ compactPropOkD rq ∧ rqShapeD rq ∧ irrNoZeroEnd rq ∧
           Qr = fun _ => iprop(True)⌝ ∗
         ∃ r : w64, ⌜rq.compaction = some r⌝ ∗ cmpReach γk r))
   ```
   At `cmp = false` today's (`reqPropOkD_off`, proved). `processInternalRaftRequestOnce.specCompact`
   goes (its case is `spec`'s at `cmp = true`).
7. `crevOf γk A` (new, internal; the snapshot track reads it): `kvEntry`'s twin from `-1`.
8. `clusterWorkloadOk ρ E` (`InvBuild.lean`, internal) gains `⌜cmpLogOk ρ.kv E.cmp L⌝` for every
   committed `L` (the apply loop's source of the entries' claims; gap G1).

**Specs.**
9. **`apply.applierTriples`** (internal to the apply package; linked) gains the conjunct
   `cmpTriple E c ai` (exact text in the apply Draft): `Compaction(cr)` at `compactionIs cr rev`,
   `⌜kbCmpM E.γ.kb ∧ rev < log.length ∧ NoDelPutAt log rev⌝`, `mPre … log Pre Q Post`, `cmpOwn E
   crev`; post `kvOwn E log ∗ chainRes ∗ (Post ∨ Pre) ∗ cmpOwn E (if chainCompacts c then
   cmpRevAfter crev rev else crev) ∗ cmpAnswerIs c log crev rev resp ch trace err`. Every
   `applierSpec` producer (the backend, the four wrappers, `NewUberApplier`'s base) proves it: the
   wrappers by the inner triple (Go's promoted method), the corrupt applier by its own spec.
10. **`apply.applierV3backend.Compaction.specD`** (new: the method has no spec today; internal,
    linked): the chain-`.backend` instance of `cmpTriple` over `backendIs E p` (exact text in the
    apply Draft). Its proof over `store.Compact.spec` (via the watchable store's promoted method),
    `traceutil.EnsureTrace` on `context.TODO()`, and the KV's `Range` at the latest revision (via
    `readView`, `storeReader`): the resources by `cmp_store_pre` (proved).
11. **`apply.uberApplier.dispatch.specD`** and **`apply.uberApplier.Apply.specD`** (linked; `Apply`
    is the `uberApplier.Apply.spec` the server's `applyEntryNormal` and `ApplyRec` use): today's with
    `dispatchOkD`, `cmpAdmit E.γ.kb log rq` in the pure premise, `cmpOwn E crev` in and
    `cmpOwn E (dispatchCrev c rq v3 crev)` / `cmpOwn E (applyCrev rq v3 x.chain crev out)` out
    (exact texts in the apply Draft; at the switch the crev is `x.crev`, A1). `apply.Apply.spec`
    (the package's entry point) is parametric in its method's contract: unchanged.
12. **`EtcdServer.applyEntryNormal.spec`** (trusted: `request_delivered`): by A1 the record carries
    the revision; one pure conjunct added to the pre (the entry's claims at the applied log):
    ```lean
      ⌜cmpEntryOk γr.kv E.cmp A m⌝ ∗
    ```
    (with `kvApplied`'s `x.log = kvModel γr.kv A` and `srvEnvOk`'s `d.cm = E.cmp`, `cmpAdmit_of_entry`
    gives the uber's `cmpAdmit`; the post's `x'.crev = crevOf γr.kv (A ++ [m])` by `crevOf_step`).
    Its premise `entryOkM E.authOn x m` reads `dispatchOk` (redefined: a compaction admitted).
13. **`EtcdServer.applyEntries.spec`, `applyAll.spec`** (trusted through `run`, `start`, `Start`):
    one pure conjunct each, the batch's claims, `⌜cmpLogOk γr.kv E.cmp (A ++ unapplied ai ms)⌝`
    (`cmpLogOk_prefix`/`cmpLogOk_snoc_entry` give each entry's). **`run.spec`: no change** (it gets
    the claims from `clusterWorkloadOk`, item 8, at each committed batch, as it gets `logShape`).
    See "What `applyAll`/`run` need".
14. **`NewServer.specD`** (trusted: `wp_NewServer`; exact text generated in
    `M2ApplyDraftSpecs.lean`), `NewServer.spec` merged with `specCompact`; three changes:
    ```lean
      (cfg.AutoCompactionRetention' = 0 ∨
        (cfg.AutoCompactionMode' = go!"revision" ∧ 0 < sint.Z cfg.AutoCompactionRetention')) →
      E₀.cmp = decide (cfg.AutoCompactionRetention' ≠ 0) →
    ```
    in place of `cfg.AutoCompactionRetention' = 0 → E₀.cmp = false →`; `"#Hkvinv" ∷ kvInvD
    ρ.rd.raft ρ.rd.kv E₀.cmp` (at the switch `kvInv` with `ρ.rd.kv.cmp = E₀.cmp`); the post's
    `srvKVCloser srv E` → `srvKVCloserM srv E (-1)`. The store is built at `cm := retention ≠ 0`
    (`server_kv_watchable_ofD` in either mode, the storage side's), the mode a pure fact of the state
    (`envAgree`'s `E.γ.cm = E.cmp`). `NewServer.specCompact` and `newServer.specCompact` go
    (`newServer.spec` takes `0 ≤ retention`, its `memberBoot … (decide (retention ≠ 0))`);
    `NewServer.specM` (auth on) keeps `retention = 0`. **Not switchable before its proof**: the
    merged proof's on arm is today's `NewServer.wp_proofCompact` `sorry`, which would then reach
    every example over `NewServer` (the reason `specCompact` was kept apart, `notes/m2-plan.md`).
15. **`EtcdServer.Compact.specD`** (the `m2` collection's; exact text generated): `isServerReqC s E ρ`
    → `isServerReq s E ρ ∗ ⌜E.cmp = true⌝`; the rest as today (gap G2 on `srvRevLb`).
16. **`EtcdServer.Txn.spec`** in compaction mode (trusted: the request path's): a premise
    `E.cmp = true → txnNoDelPut t` (A5; not drafted in Lean: its form is Q2).
17. **Snapshot track (the collaborator's; drafts only, nothing edited):** `restorePre_of_applyM`
    takes the right from `apply.cmpOwn E c` instead of `srvKVCloserM`'s on arm (A2), which keeps only
    the watchable store's own parts; `applySnapshot.specSnap`'s post re-ties `x'.crev` to the
    image's records, `r.crev = crevOf γk A'` (a fact the image's certificate `dbImageR` must carry:
    the sender's scheduled record is the model's compaction revision of its applied log), and #8's
    `c ≤ c'` is `crevOf_mono` with `crevOf_pos`/`recsPos_crev` (no `Compact(0)` corner).

## Glue (proved, in the Drafts)

- `apply.cmp_store_pre`: the backend's `Compaction` meets `store.Compact.spec`'s precondition from
  its own (right and supply from `cmpOwn`; certificate and writer's fragment from `kvOwn`/
  `txn.kvWriter`; the reader's token lent by `writerOwn_rt`; `hookOk` from the options), and gives
  `kvOwn`/`cmpOwn` back at any revision `≥ -1`.
- `cmpAdmit_of_entry`: the server's entry claims give the uber's `cmpAdmit`.
- `crevOf_step`: `Apply`'s revision after a decoded entry is the model's (`compactPropOkD` excludes
  skipping and rejection); `crevOf_snoc`, `crevOf_mono`, `crevOf_ge`, `crevOf_plain` (a plain log
  stays at `-1`), `crevOf_pos` (`-1` or `≥ 1`: Q7 (a) at the model).
- `cmpLogOk_snoc_entry`, `cmpLogOk_prefix`, `cmpLogOk_plain`; `kvInvD_off`, `reqPropOkD_off`
  (every compaction-off statement reads as today); `compactPropOkD_irrCompaction`;
  `dispatchOkD_of`, `dispatchCrev_ge`, `dispatchCrev_nonCmp`, `cmpRevAfter_ge`, `cmpOwn_ge`,
  `cmpOwn_off`, `plainEntryM_false`/`plainLogM_false`, `plainReq_nonCmp`.

## Gaps (not cheap; for the Probe/Prove steps)

- **G1, the committed log's claims** (`clusterWorkloadOk` with `cmpLogOk`): `kvInvD` keeps
  `cmpLogOk` of the *requested* log; the apply loop needs it of the *committed* logs, as
  `clusterWorkloadOk_of` (`BuildGap.lean`) transfers `logShape` through `kvModel_eqv`. Per-entry
  shape transfers entry by entry; `cmpLogOk` refers to the model of the prefix, so the transfer is
  `kvModel_eqv` at each prefix. Expected mechanical.
- **G2, the proposer's reach** (`cmpReach` from `Compact.spec`'s `srvRevLb E.γ r`): `srvRevLb` is a
  certificate of the proposer's store (`idxCert`, which `store.Rev` gives), `cmpReach` a KV
  certificate (`kvCert`, the `certOk` map `store.Read` gives). No law turns an `idxCert` into a
  `certOk` today. Options: (a) an mvcc law that every certified log of the server's store is
  `certOk` (if the store's invariant keeps it: to check); (b) `Compact.spec`'s premise and the
  compactor's server `RevLb` restated over `cmpReach` (the compactor's frozen contract would then
  read `rg.Rev()` through a read view: a change to its environment's construction, not to the frozen
  `v3compactor` specs). Q3.
- **G3, `irrNoDelPut` of a put and a delete** (`irrNoDelPut_put`, `_delete`): from `chainStep`'s
  backend outcome (a put's revision has one `put` change, a delete's only `del`s). Mechanical.
- **G4, the commit step** (`kv_prop_au` over `kvInvD`/`reqPropOkD`): the compaction form keeps the
  state (`kvModelSt_snoc_nonwrite`), records `cmpLogOk` at the new entry from `cmpReach` (`kvCertInv`
  opened beside `kvInv`: `kvcN` and `kvN` disjoint) and the invariant's `NoDelPutAt`; the write
  forms keep `NoDelPutAt` of the extended model from `irrNoDelPut` (the model's last revision is
  the request's outcome's).
- **G5, `start`'s split** (A2) and the supply (`kbWTSupplyM_of_poolR`): `start`'s proof, which
  today frames the closer; with D22's `srvWTPoolR` (the storage side's draft, not switched).

## What `applyAll`/`run` need

Under A1: **`run.spec` no textual change**; `applyAll.spec` and `applyEntries.spec` one pure
conjunct each (item 13: the batch's compaction claims, which they pass to `applyEntryNormal`), and
`applyEntryNormal.spec` one (item 12). The revision itself rides in `x` (`srvApplyKV(M)`,
`kvApplied(M)`, `entriesStep`): their two-copy proofs (`applyAll`'s, `run`'s, with SNAPSHOT-SORRY
#7/#8) only pass it through, except at the install (`applySnapshot.specSnap`, the snapshot track's:
item 17). `run` gets the claims from `clusterWorkloadOk` (item 8) where it gets `logShape` today.
Nothing here merges them (the auth merge does, after the snapshot proofs).

## The 3-member `putgetc` (scoped, not built)

`examples/common` already runs multi-member programs (`NewMember`, `StartMember`; `putget3`,
`linkv3p`; `Alloc3.lean` allocates three members' cluster resources), but only with the compactor
off (`newServer(…, 0, …)`), and `kvreconf` is a membership-change example of its own. The work:
- **Go**: `common.NewMember`/`StartMember` take the retention (one function each, `0` from
  `putget3` and `linkv3p`, as `newServer` already does); `StartCompactingServer` goes (one-member
  `putgetc` was its only caller); `examples/putgetc` starts three members as `putget3` does, each
  with `retention = 1`, and puts and gets through the first. Its Go test; `etc/goose.py --project`
  for the examples; `etc/gen-init.py`.
- **Lean**: `NewMember.spec`/`StartMember.spec` with the retention (`memberBoot … (decide (retention
  ≠ 0))`, `newServer.spec`'s); `Alloc3`'s allocation at the cluster's mode (`kvInvD … cmp` once for
  the cluster, every member's `E₀.cmp = cmp`: the cluster-wide mode, `KVNames.cmp`); `putgetc`'s
  `Main.spec`, `MainLinked`, `Adequacy`, `Results` re-done over three members (`putget3`'s, with
  the compacting start); `putgetc_safe`'s statement keeps its shape (no panic, no stuck thread),
  over the changed program.
- **What it rests on**: what `putget3_safe` rests on (the snapshot track's `applyAll`/`run`
  `sorry`s: a follower may install a snapshot, so restore in compaction mode is reachable), plus
  M2's own `sorry`s until proved. `etc/tcb-collections/m2.txt` follows.

## `NoDelPutAt`: what the upstream fix would remove (not done)

The fix: etcd-io/etcd#22377 (`keyIndex.doCompact`) and #22395 (the gRPC path) in the fork
(`upamanyus/etcd`, branch `goose-lean`), the etcd pin bumped in `etc/goose.py` and the examples'
`go.mod` together, `etc/goose.py` regenerating. It would remove:
- mvcc: `store.Compact.spec`'s (export `mvcc_store_Compact`) `mvcc.NoDelPutAt log (sint.Z rev)`;
  internally `compactJobPre`'s, `crevSafe`, `delKey`'s use, `kiGet_avail`/`named_not_del`/
  `rangeAnswers_not_del`'s premise (a re-proof of `keyIndex.doCompact` and of the compaction job
  against the fixed code);
- apply (this Draft): `cmpAdmit`'s, `cmpTriple`'s and `applierV3backend.Compaction.specD`'s
  `NoDelPutAt`;
- server (this Draft): `cmpEntryOk`'s `NoDelPutAt`, `kvInvD`'s `cmp = true → ∀ c, NoDelPutAt …`,
  `reqPropOkD`'s `cmp = true → irrNoDelPut rq`, G3, and `EtcdServer.Txn.spec`'s compaction-mode
  premise (item 16) with what it reaches above (v3rpc's `Txn`, the client's `Txn` in compaction
  mode); `CompactMode.lean`'s `irrNoDelPut`;
- `issues/etcd-compaction-delete-then-put.md`'s "How the proof handles it".

## Questions for the user (one batch)

- **Q1, the record (A1) and the right's home (A2)**: the compaction revision as `ApplyKV.crev`
  with the right in the apply state (four apply-loop texts unchanged but three pure conjuncts;
  two of the snapshot track's drafts change: `restorePre_of_applyM`, `srvKVCloserM`), or the right
  kept in the closer and threaded (four more statement changes). Recommended: A1/A2.
- **Q2, `NoDelPutAt` before the fork fix (A5)**: accept the interim (a compaction-mode premise on
  `EtcdServer.Txn`, carried above it only in compaction mode; `putgetc` has no transaction), or do
  the fork fix (#22377, #22395, the pin bump) before the switch, so no interim premise exists
  (the user's round-1 decision (b) said the fix; the brief deferred it). Recommended: the fix
  before the switch of item 16 only; the rest of the Draft does not depend on it.
- **Q3, the proposer's reach (G2)**: (a) an mvcc law `idxCert ⊢ certOk` for the server's store, if
  true, or (b) `EtcdServer.Compact.spec`'s premise as `cmpReach ρ.kv r` (the compactor's server
  environment's `RevLb` restated through a read; the frozen `v3compactor` specs unchanged).
  Recommended: check (a) first.
- **Q4, the switch order of `NewServer.specD` (item 14)**: it can be switched only with its on
  arm proved (else the `sorry` reaches every example); until then `specCompact` stays apart.
  Confirm, or accept the `sorry` under the examples for the time of M2.
- **Q5, approve the drafted statements** 1-16 (17 is the collaborator's).

## Checked

- Full `lake build` of the branch base `b7f83e121a` (`--packages` at Perennial `6da88b280`):
  passed, 11247 jobs, no error.
- `etc/lean-check.py -a` on the three Drafts; targeted `lake build` of the three (3816 jobs, no
  error). No `axiom`, no `sorry`, no Perennial change, no generated file edited; nothing switched,
  so `etc/tcb-report.py --check` is not needed (no axiom or `sorry` changed).

## The user's answers on the Draft (2026-10-30)

- **Q1:** A1/A2 kept: the compaction revision is a field of the apply state (`ApplyKV.crev`), and the
  compaction right (with the write-back supply) lives with the apply thread, split out of the closer by
  `start`.
- **Q2:** the fork fix first for the `Txn` item: upstream's fix (etcd-io/etcd#22377, #22395) in the
  fork and the etcd pin bumped before the `Txn` item switches; no `Txn` premise. The user pushes the
  fork. The other items do not wait.
- **Q3 (G2):** try an mvcc law first: every log the store certifies is in the KV certificate map, so
  `srvRevLb` gives the model-level "revision reached"; `Compact.spec`'s text stays.
- **Q4:** `NewServer.spec` and `specCompact` stay separate until the compaction-on case is proved,
  then merge in one step.
- **Q5** (approve items 1-16) waits for the review round.

## Review round 1: the repair (2026-10-30)

The report: `notes/spec-first-study/m2-apply-review-1.md`. All in the three Drafts; checked
(`etc/lean-check.py -a` on each) and built (`lake build` of the three, 3817 jobs, no error, no
warning in them); no `axiom`, no `sorry`, nothing switched.

| finding | repair |
|---|---|
| **F-1** `cmpTriple` unprovable over `store.Compact.spec`'s `ErrFutureRev` arm | **item 18** (new, mvcc, exported `mvcc_store_Compact`): `mvcc.store.updateCompactRev.specD` and `mvcc.store.Compact.specD` without the `ErrFutureRev` arm (and without `NoDelPutAt`, F-5). Why it is provable: in that branch the store holds its committed log's authority (`revMuBody`'s `idxLogAuth γ.idx (revQ γ q) log`), which extends the caller's certificate (`idxLogAuth_cert_prefix`), so the caller's `rev < |log₀|` gives `rev ≤ currentRev`: `cmp_not_future` (proved) is the step; the re-proof of `updateCompactRev` replaces its `ErrFutureRev` branch by that contradiction (gap **G6**, cheap). `cmpTriple`'s and `Compaction.specD`'s backend proof then rests on `specD`. |
| **F-2** the compaction's result loses "no trace on an error" | `dispatchAnswerD` takes the result's trace: the compaction's error arm `rp = null ∧ err ≠ nil ∧ tr = null`; `dispatchResultD` passes `v.Trace'`, `applyResultIsD` over it; `dispatch.specD`, `Apply.specD` (and `specRecD`) use them; `dispatchAnswerD_nonCmp` (proved: another kind reads as today). Gap **G7** closed in the text; `specCompact` stays until the switch. |
| **F-3** `Compact.specD`'s `E.cmp = true` does not reach the KV invariant's mode | `isServerReqD s E ρ := isServerReq s E ρ ∗ kvInvD ρ.raft ρ.kv E.cmp` (**item 19**: at the switch a conjunct `⌜ρ.kv.cmp = E.cmp⌝` of `srvReqFieldsAt`, made by `NewServer` from `ρ.rd.kv.cmp = E₀.cmp` and `envAgree`); `isServerReqD_off` (proved: off, `isServerReq` itself). `Compact.specD` takes `isServerReqD s E ρ ∗ ⌜E.cmp = true⌝`. Gap **G8**: `NewServer`'s proof makes the tie. |
| **F-4** `applyEntryNormal` has no source for `compactPropOkD` | `cmpEntryOk`'s compaction case carries `compactPropOkD rq`; `compactPropOkD_of_entry` (proved) is `crevOf_step`'s `hok`. `reqPropOkD`'s compaction form already has it, so G4 records it at the commit. |
| **F-5** items 5/6 cannot precede the fork fix | the items in the fix's form: `cmpAdmit` (and the new `cmpAdmitRev`), `cmpTriple`, `Compaction.specD`, `cmpEntryOk`, `kvInvD` (its `NoDelPutAt` conjunct gone), `reqPropOkD` (its first disjunct `reqPropOk` alone) have no `NoDelPutAt`; G3 and item 16 are moot. **The plan's Q2 note was wrong**: dropping `NoDelPutAt` from mvcc's specs (STATUS, "The delete-then-put fix in the fork: what is left") gates the whole switch, not only `Txn`'s item. |
| **F-6** item 14 inconsistent with A2 | two predicates: `NewServer`'s post keeps `srvKVCloserM srv E (-1)` (with the right, the storage side's draft); **item 20**, `srvKVCloserW s E` (off `srvKVCloser`; on the watchable store's own parts, no right), what `start` keeps and the snapshot track's `restorePre_of_applyM` takes; `srvKVCloserM_split` (proved): `srvKVCloserM s E c ∗ ⌜-1 ≤ c⌝ ⊣⊢ srvKVCloserW s E ∗ apply.cmpRight E c`, `start`'s step (G5). Under Q4, `specCompact`'s post must hand out `srvKVCloserM` too (today `srvKVCloser`): part of item 14's merge. |
| S-1 `dispatchOk` redefined in place | `dispatchOk` stays; **item 1 is now `dispatchOkM cmp on rq`** (`dispatchOk` off, `dispatchOkD` on; `dispatchOkM_false` by `rfl`, `dispatchOkM_of`), at `E.cmp` in the uber's specs, at the mode in `entryOkM`/`rqShape` (through `logShapeM`) at the switch. **Item 21**: `apply.Apply.specRecD` (drafted, the compaction arm threaded as in `Apply.specD`). The off texts of items 12/13 read as today through `dispatchOkM_false`. |
| S-2 G2's law, as phrased, unprovable | reformulated in `cmpReach`'s docstring: the store's current committed log is `certOk` (**`revMuBody` already holds `certOk γ log` beside the log's authority**, so the invariant exists), and the law `idxCert γ l ⊢ ∃ l', certOk γ l' ∗ ⌜l <+: l'⌝` under the store's invariant; whether a caller holding only `storeReaderC` can reach it is the Probe's. |
| S-3 `crevOf_step`'s hypotheses | `hch` from `kvApplied` (the start's chain), `hv3` the spec's premise, `hok` from `compactPropOkD_of_entry` (F-4). |
| S-4 unlisted dependencies | listed: `srvEnvOkD` (the storage side's draft) switches first; `KVNames.cmp` and the tie (item 19); the interim texts under Q4 (`NewServer.spec` at `ρ.rd.kv.cmp = false`, `specCompact` at `true` with `srvKVCloserM`); `compactableOk_server` restated over `isServerReqD`; the examples' allocation at the mode; a lemma `compactPropOkD (withHeader rq hm)` (for the glue). |
| S-5 `ApplyKV.crev`'s default and `⟨log, chain⟩` | noted for the switch: `bootKV`/`bootKVOf` and positional `ApplyKV`s name the field. |
| S-6 `NewServer.specD`'s off reading | needs an exported `kbCmpM E.γ.kb ↔ E.γ.cm` (`srvEnvOkD_mode_step`'s second half, at the start); for item 14's merge. |
| S-7 G1 | unchanged (needs item 19's tie). |
| S-8 the repeated admission | `cmpAdmitRev kb log rev := kbCmpM kb ∧ rev < |log|`, used by `cmpAdmit`, `cmpTriple`, `Compaction.specD`. |

New items for Q5: **18** (`store.updateCompactRev`/`store.Compact` without `ErrFutureRev`),
**19** (`srvReqFieldsAt`'s `ρ.kv.cmp = E.cmp`), **20** (`srvKVCloserW`), **21** (`Apply.specRec`'s
compaction arm). Items 1 (now `dispatchOkM`), 2 (the trace), 3 (no `NoDelPutAt`, `cmpAdmitRev`), 5,
6, 9, 10, 12 (F-4's claim) changed as above; 16 withdrawn (Q2).

## Review round 2: the repair (2026-10-30)

The report: `notes/spec-first-study/m2-apply-review-2.md` (two first-tier findings, both caused by
round 1's repairs; F-1, F-2, F-4, F-6, S-8 confirmed fixed; no Go bug). Checked (`lean-check -a`)
and built (3825 jobs, no error); no `axiom`, no `sorry`, nothing switched.

| finding | repair |
|---|---|
| **N-1** (from S-1's repair) the shape chain still excludes compaction: `kvWork` → `logShape` → `entryShape` → `rqShape` → `dispatchOk`, and `applyEntryNormal`'s `entryOk`/`entryOkOn` read `dispatchOk` | the mode in the shape vocabulary: `rqShapeD cmp` (over `dispatchOkM cmp`), `entryShapeD cmp`, `logShapeD cmp`, `kvWorkD cmp`, and the apply thread's `entryOkD cmp`/`entryOkOnD cmp`/`entryOkMD on cmp`; each today's at `cmp = false` by definition (`rqShapeD_false`, `entryShapeD_false`, `logShapeD_false`, `kvWorkD_false`: `rfl`; `entryOkMD_false`). `kvInvD` takes `kvWorkD cmp`; `reqPropOkD`'s compaction form `rqShapeD true`. **Item 1 grows** (the shapes, `kvWork`); **item 12**'s premise is `entryOkMD E.authOn E.cmp x m`. Glue still to write: `entryOkD` from `entryShapeD` (as `entryOk_of_shape`), and G1's transfer of `logShapeD` (as `clusterWorkloadOk_of`'s of `logShape`). |
| **N-2** `isServerReqD`'s second copy of the KV invariant cannot be allocated (each copy owns half of `srvRLog`), and the off copy's `plainLog` forbids the entry | the switch's text drafted: `srvReqFieldsAtD` (today's with `kvInvD ρ.raft ρ.kv E.cmp` in place of `kvInv`), `isServerReqD` over it, `srvReqFieldsAtD_off`/`isServerReqD_off` (equations), `isServerReqD_kvInv`. `NewServer.specD`'s post (`srvBuilt`, which holds the off `kvInv` through `srvReqBuilt`/`srvKVInvs`) is to be read with item 5's in-place redefinition; the Draft says so (item 14 is deferred by Q4 anyway). |
| S-1' items 12/13 do not read as today off | true of `cmpEntryOk`'s conjunct: off it holds of every plain log (`cmpLogOk_plain`), so a caller discharges it, but the text changes; item 12/13 state it. |
| S-2' a cheaper G2: `store.Read` gives `certOk` of its log | recorded for the Probe (to check against `store.Rev`'s proof and the 3-member names). |
| S-3 item 18 misses `compactLockfree`'s `ErrFutureRev` arm | item 18 covers `compactLockfree` and the two docstrings naming the arm. |
| S-4 `srvKVCloserW` spells out mvcc internals | for the switch: mvcc exports a sealed `wsCloserW` (no right) with `wsCloserR_split`; the server's predicate over it. |
| S-5 the mode in two places (`E.cmp`, `kbCmpM E.γ.kb`) | the tying law (`srvEnvOkD_mode_step`'s second half at the start) to export with item 14 (as S-6 of round 1). |
| S-6 `Compact.specD`'s `E.cmp = true` undocumented | documented in the spec: a client `Compact` at a server with the auto-compactor off stays outside the model. |
| S-7 the header's revision fact unread | kept (the gRPC caller's `compactOk` needs a header; true of Go). |

