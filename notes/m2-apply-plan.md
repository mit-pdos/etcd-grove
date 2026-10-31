# Plan: M2, the apply side (spec-first; branch `m2-apply`)

Status (2026-10-31): **approved** (the user's Q5: the consolidated items of "The switch in place");
**the Probe**: item 18, G2, the commit step's compaction arm and S3-3's transfer lemma done ("The
Probe", the last section); next G1. Before: review rounds done (round 7: nothing in the first tier); the switch restated in place
(the user's Q6 (a)). Nothing switched but item 18 (mvcc).

**Resume here.**
1. *Done so far.* Draft modules `etcdserver/apply/M2ApplyDraft.lean`, `etcdserver/M2ApplyDraft.lean`,
   `etcdserver/M2ApplyDraftSpecs.lean` (imported by nothing; no `axiom`/`sorry`), repaired for review
   round 1 (`notes/spec-first-study/m2-apply-review-1.md`); targeted build passes. The `NoDelPutAt`
   fork fix is on `lean` since 2026-10-28; the Drafts are now stated in its form (no `NoDelPutAt`),
   so dropping the premise from mvcc's specs gates the switch (F-5).
2. *Approved* (2026-10-31, the user: "approve the items; start the Probe with item 18").
3. *The Probe*: item 18, G2 (the user's (a')), the commit step's compaction arm
   (`kv_prop_au_cmp`) and S3-3's transfer lemma (`kv_entry_claim`), both in `M2ApplyProbe.lean`,
   done ("The Probe", below). **Next: G1.**
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
  state (`kvModelSt_snoc_nonwrite`) and records `cmpLogOk` at the new entry from `cmpReach`, read
  before the atomic update (item 6's route, rounds 5-6: `kv_cert_read`, `srvReqLogLb_of_rlogLb`,
  inside `srvReqLogLb_prefix`). (Superseded: "`kvCertInv` opened beside `kvInv`", and the
  `NoDelPutAt` clauses, gone with F-5.)
- **G5, `start`'s split** (A2) and the supply (`kbWTSupplyM_of_poolR`): `start`'s proof, which
  today frames the closer; with D22's `srvWTPoolR` (the storage side's draft, not switched).

## What `applyAll`/`run` need

(Superseded by "The switch in place", items 8, 12, 13: no apply-loop spec changes in text; the
entry's claim is derived inside `applyEntryNormal`'s proof.) Under A1 the revision itself rides in `x` (`srvApplyKV(M)`,
`kvApplied(M)`, `entriesStep`): their two-copy proofs (`applyAll`'s, `run`'s, with SNAPSHOT-SORRY
#7/#8) only pass it through, except at the install (`applySnapshot.specSnap`, the snapshot track's:
item 17). Nothing here merges them (the auth merge does, after the snapshot proofs).

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

## `NoDelPutAt`: what the upstream fix would remove (mvcc's part done by item 18, 2026-10-31)

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

## Review round 3 (2026-10-30): stopped for a design question

The report: `notes/spec-first-study/m2-apply-review-3.md`. Two first-tier findings, the same
pattern as rounds 1-2 (a drafted copy of a definition, with another carrier of the off version
left): **R3-1**, the committed-log clauses between the invariant and `applyEntryNormal` still read
the mode-free `logShape`/`logShapeM` (`srvC`, `srvCM`, `clusterWorkloadOk(M)`, the premises of
`applyAll`, `applyEntries`, `EtcdServer.apply`; item 13 is wrong, and `EtcdServer.apply.spec` is
missing from the list); **R3-2**, `Compact.specD` still holds the off `kvInv` through
`isServerRead` → `srvKVInvs` (also `isServer(M)`, `srvBuilt`). Repaired: S3-1 (`entryOkMD`'s
auth-on arm is today's `entryOkOn`). Open: S3-2 (the plan's item texts 1, 8, 12, 13 describe
superseded designs), S3-3 (a cheaper source of `cmpEntryOk` inside `applyEntryNormal`'s proof),
S3-4 (round 2's S-5, S-4, S-2').

**The question (Q6, for the user).** Drafting a mode-indexed copy of each definition does not
converge: every carrier of `kvInv` or `logShape` needs its copy, and three rounds each found more.
Two ways to state the switch:
- **(a) In place.** `KVNames.cmp` added; `kvInv γ γk` redefined as `kvInvD γ γk γk.cmp` (every
  carrier, `srvKVInvs`, `isServerRead`, `srvBuilt`, ..., unchanged in text), with the tie
  `ρ.kv.cmp = E.cmp` in `srvKVInvs`; `dispatchOk`/`rqShape` redefined to admit a compaction (round
  1's design), so `logShape`, `srvC`, `clusterWorkloadOk`, `applyAll`... are unchanged in text, and
  the gate is `plainLogM γk.cmp`/`cmpEntryOk` (compactions only in compaction mode). Cost: the
  compaction-off texts no longer read as today *by definition* (round 1's S-1): they admit a
  compaction in the shapes, excluded by the invariant's `plainLogM` and the entry's claim instead;
  off laws (`kvInvD_off`, `cmpLogOk_plain`) show the off servers are unchanged in meaning.
- **(b) Copies, completed.** Keep the mode-indexed vocabulary and draft every carrier (`srvC`,
  `srvCM`, `clusterWorkloadOk(M)`, `srvKVInvs`, `isServerRead`, `isServer(M)`, `srvBuilt`, and the
  apply-loop specs), each today's at `cmp = false` by `rfl`. Cost: about a dozen more drafted
  definitions and four spec texts, and more review rounds of the same kind.
Recommended: (a) for `kvInv` (the plan already said "redefined in place" for it) and (a) for the
shapes, with the off laws as the evidence that compaction-off servers mean what they meant.

## The switch in place (the user's Q6 (a), 2026-10-30)

**The answer.** The switch is stated in place: a redefined definition's new text is drafted as
`…D`; a definition that only carries one (`rqShape`, `entryShape`, `logShape`, `kvWork`,
`entryOk(M)`, `srvC(M)`, `clusterWorkloadOk(M)`, `isServerReq`, `isServerRead`, `isServer(M)`,
`srvBuilt`, `srvReqBuilt`, the premises of `applyAll`/`applyEntries`/`EtcdServer.apply`/
`applyEntryNormal`) keeps its text and is read under the redefinitions. The gate of a compaction
is the KV invariant's `plainLogM` (by the cluster's mode, `KVNames.cmp`) and the entry's claim
(`cmpEntryOk`, compaction mode only), not the shapes. The cost the user accepted: the
compaction-off texts mean today's by proved off laws, not by `rfl` (round 1's S-1).

**What changed in the Drafts** (checked: `lean-check -a`; built, 3825 jobs; no `axiom`/`sorry`):
- apply Draft: `dispatchOkM` gone; `dispatchOkD` is item 1's text; the uber's specs and
  `specRecD` take it; the off law `dispatchOkD_iff` (a request that is no compaction: today's).
- server Draft: the shapes mode-free (`rqShapeD`, `entryShapeD`, `logShapeD`, `kvWorkD`: the texts
  of `rqShape`, ..., `kvWork` read under item 1, copied only because the Draft cannot redefine);
  off laws `rqShapeD_iff`, `entryShapeD_plain`, `logShapeD_plain`; `kvInvD_off` now an
  equivalence (`⊣⊢`, through `inv_iff`: a plain log's shapes are today's); `entryOkD`/`OnD`/`MD`
  gone (`entryOkM`'s text is kept); `isServerReqD` gone; the ties `srvReqFieldsAtD` and the new
  `srvKVInvsD` (R3-2: the apply side's and the readers' carrier), each with its off law.
- specs Draft: `Compact.specD` over `isServerReq`/`isServerRead` (read under the ties).

**R3-1 and R3-2 under the restatement.** R3-1: `srvC`, `clusterWorkloadOk(M)` and the apply-loop
premises read `logShape`, which admits a compaction under item 1: no copy needed. What they still
need is item 13's `cmpLogOk` (the claims of the committed logs), unless S3-3's derivation inside
`applyEntryNormal`'s proof works. R3-2: `srvKVInvs`' `kvInv` is the mode's under item 5, tied to
`E.cmp` by item 19's `srvKVInvsD`.

**The consolidated item list** (for Q5; supersedes the texts of "The drafted statements" where
they differ; "in place" = the unsuffixed name redefined to the drafted text):
1. `dispatchOk` := `dispatchOkD` in place (admits a compaction). Carriers unchanged.
2. `dispatchAnswer`/`dispatchResult`/`applyResultIs` in place: the result's trace passed, the
   compaction's case (`dispatchAnswerD`; error arm with no trace, F-2).
3. The apply vocabulary (new): `chainCompacts`, `cmpRevAfter`, `dispatchCrev`, `applyCrev`,
   `cmpAdmitRev`, `cmpAdmit`, `cmpRight`, `cmpOwn`, `cmpRespOk`, `cmpAnswerIs`; no `NoDelPutAt`.
4. A1's record: `ApplyKV.crev`, `applyKV`'s `cmpOwn E x.crev`, `applyStep`'s crev clause,
   `kvApplied(On)`'s `x.crev = crevOf γk A` (S-5: positional `ApplyKV`s name the field).
5. `KVNames.cmp` (new field); `kvInv γ γk` := `kvInvD γ γk γk.cmp` in place (`plainLogM`, the
   claims `cmpLogOk` last, no `NoDelPutAt`); `CompactMode.lean`'s family goes (`kvInvC`, `kvWorkC`,
   `compactClaims`, `isServerReqC`, `srvReqFieldsAtC`, `reqPropOkC`, `dispatchOkC`, `rqShapeC`,
   `entryShapeC`, `logShapeC`, `plainEntryC`, `plainLogC`). **The fact lost** (round 4): `plainLog`
   of the committed log; `kv_log_plain` gives `plainLogM γk.cmp`, and its users
   (`applyEntryNormal`, `KVApply`, `SnapRecvFacts`) and the model lemmas over `plainLog`
   (`kvModelSt_plain`, `kv_fire_reads`, the invariant's step, `KVModelRestore`) get `plainLogM`
   versions (true: a compaction leaves the model; mechanical). **The laws callers need after the
   switch** (in place of `kvInvD_off`, whose right side then no longer exists): `kv_log_plain_off`
   (`γk.cmp = false` gives `plainLog`), the ties (item 19) giving `γk.cmp = false` from
   `E.cmp = false`, and the allocation of `kvInv` at any mode.
6. `reqPropOk` in place: its body today renamed (`reqPropOkW`, the write forms), and `reqPropOk γk
   rq Qr := reqPropOkW γk rq Qr ∨ (compaction form at `γk.cmp = true`)` (`reqPropOkD` with `cmp :=
   γk.cmp`); `processInternalRaftRequestOnce.specCompact` goes at the switch (its case is `spec`'s
   at `γk.cmp = true`; `NewServer.specCompact` is item 14's). Users of the compaction family to
   move: `EtcdServer.Compact`'s proof, `compactableOk_server`, `processInternalRaftRequestOnce`'s
   `specCompact` proof. `reqPropOk_wire` needs lemmas that the compaction fields ignore the header.
   **The commit step (G4, rounds 5-6):** `kv_prop_au` runs at the caller's `⊤`; the atomic update
   it builds runs at `⊤ \ srvRaftN`. So its leading step reads the compaction form's `cmpReach`
   through `kvCertInv` (item 19; `kv_cert_read`) and turns it into a lower bound of the server's
   log with `srvRaftLogInv` (from `raftPropose`) by `srvReqLogLb_of_rlogLb` (`SrvRaftLog.lean`),
   without opening `kvInv`; inside the update `srvReqLogLb_prefix` (no mask) places it below the
   committed log, where the invariant records `cmpLogOk`. So `kv_prop_au` and `kv_prop_au_M`
   gain `kvCertInv(M)` and `srvRaftLogInv` arguments, and their mask premise grows to `kvN`,
   `kvcN` and `srvRaftN` (round 7's S7-2).
7. `crevOf` (new, internal).
8. **Dropped** (S3-3, rounds 4-5's recommendation): `applyEntryNormal`'s proof derives the
   entry's claim from what it holds (`srvRLogLb (A ++ [m])`, `srvKVInvs` with the tie, the KV
   invariant opened at `⊤`, its `cmpLogOk`), by one new lemma moving a compaction's claim from
   the invariant's log to the committed log (`srv_eqv_prefix`/`kvModel_eqv` at the prefix before
   the entry; today's `srv_entry_transfer` is per entry). No spec carries `cmpLogOk`. (The `srvC`
   fallback rests on the same lemma, so it is not kept.) Needs S-5's `kbCmpM ↔ E.cmp` law.
9. `applierTriples` gains `cmpTriple` (over `cmpAdmitRev`, `store.Compact.specD`).
10. `applierV3backend.Compaction.specD` (new).
11. `uberApplier.dispatch.specD`, `uberApplier.Apply.specD` (`cmpAdmit`, `cmpOwn` in and out).
12. `applyEntryNormal.spec`: **unchanged in text** (item 8); its premise `entryOkM` read under
    item 1.
13. `applyEntries.spec`, `applyAll.spec`, `EtcdServer.apply.spec`, `run.spec`: **unchanged in
    text** (item 8).
14. `NewServer.specD` (deferred by Q4): the merged statement; its post read under items 5/19; its
    `#Hkvinv` is `kvInv` with the premise `ρ.rd.kv.cmp = E₀.cmp`. **14' (round 4's R4-1, not
    deferred): the interim texts** `NewServer.spec` (`ρ.rd.kv.cmp = false`), `specCompact`
    (`ρ.rd.kv.cmp = true`, and its post's closer `srvKVCloserM`) and `specM` (`ρ.rd.kv.cmp = false`)
    take the premise, since their posts' `srvKVInvs` carries item 19's tie; the examples allocate
    `kvInv` at the chosen mode (`common/Alloc.lean`). The producers to move (round 5's S5-3):
    `srvClusterBoot_alloc` (its positional `KVNames` literal names the field) and
    `srvClusterBootOn_alloc`, `kvInv_alloc_boot` (at any mode), `srvMemberBoot(On)_alloc`, the
    examples' member boot bundle (`common/Defs.lean`).
15. `EtcdServer.Compact.specD`: over `isServerReq s E ρ`/`isServerRead s E ρ.rd` (round 5's F5-2:
    the readers' names the request path's, as `start`'s `isServer` gives them; the same in
    `compactableOk_server`) with `⌜E.cmp = true⌝` (S-6: a client compaction at a compaction-off
    server stays outside the model). Its `srvRevLb` premise stays if G2 (a) holds (Q3).
16. withdrawn (Q2).
17. the snapshot track's (the collaborator's): `restorePre_of_applyM` over `srvKVCloserW` and
    `apply.cmpOwn`; the install's `x'.crev` re-tie; its uses of `plainLog` (`SnapRecvFacts`,
    `KVModelRestore`) over `plainLogM` (item 5).
18. mvcc: `store.updateCompactRev`, `store.Compact`, `store.compactLockfree` without the
    `ErrFutureRev` arm (and the docstrings naming it), with the `NoDelPutAt` removal.
19. The ties: `srvReqFieldsAt`, **`srvReqFieldsAtM`** (the merged request path's, round 4: Put,
    Range, Txn are written over it; the conjunct at the same place in both texts keeps their two
    `rfl` laws) and `srvKVInvs` gain `⌜…kv.cmp = E.cmp⌝` beside their `kvInv`; the request path's
    view also gains `kvCertInv` (`kvCertInvM` in the M copy; round 5's F5-1: the commit step needs
    it; produced by `start` from `srvKVInvs`, on from `srvKVInvsOn`'s `kvCertInvOn`). **In the M
    copy the tie is `kvTieM on γk.cmp E`** (round 6's R6-1: `⌜γk.cmp = E.cmp⌝` off, `True` on;
    `start.specOn` has no producer for an on tie, and no auth-on consumer reads one).
    `NewServer.specM`'s premise `ρ.rd.kv.cmp = false` produces the tie in `srvBuiltG false`'s
    `srvKVInvs` (which `NewServer.spec` inherits); the caller allocates `kvInvM` at the mode
    (round 7's S7-1). The on family's positional destructurings of `srvReqFieldsAtM` move too
    (S7-3); a drafted `srvReqFieldsAtMD` would let Lean check the `rfl` claim (at the switch). Positional
    consumers to move (round 6's S6-4): the `#Hclog, %Hcfgnn` pattern of
    `processInternalRaftRequestOnce`, and `client/v3/ServeFromStart.lean`, `v3rpc/ServerKV.lean`
    (outside the package: projection laws for `srvReqFieldsAt`)
    (`srvReqFieldsAtD`, `srvKVInvsD`); `NewServer` makes them from `ρ.rd.kv.cmp = E₀.cmp` (14').
    `srvKVInvs` gets projection laws (`client/v3` and `v3rpc` unfold it by position). **Scope**:
    the tie puts every member of a cluster in one compaction mode (`KVNames.cmp` is the
    cluster's); Go allows members with different settings, which stay outside the model.
20. `srvKVCloserW` and `srvKVCloserM_split` (S-4: over a sealed mvcc `wsCloserW` at the switch).
21. `apply.Apply.specRec`: the compaction arm (`specRecD`).
Review round 4 (`notes/spec-first-study/m2-apply-review-4.md`): R3-1/R3-2/S3-1 resolved; one
first-tier finding, R4-1 (the tie unestablished: item 14'), repaired in the list and in
`NewServer.specD`'s comment; second tier: `cmpLogOk` moved last in `kvInvD` (done), item texts
5, 6, 8, 12, 13, 17, 19 restated above. Nothing in the apply Draft.

Review round 5 (`notes/spec-first-study/m2-apply-review-5.md`): R4-1 resolved, round 4's repairs
introduced nothing; two first-tier findings at the compaction's proposal, F5-1 (the commit step:
`kvCertInv` in the request path's view, the comparison before the atomic update) and F5-2
(`Compact.specD`'s readers' names, `ρ.rd`), repaired (items 6, 15, 19; the spec Draft); items
8, 12, 13 committed to S3-3 (unchanged texts).

Review round 6 (`notes/spec-first-study/m2-apply-review-6.md`): round 5's repairs sound (the commit
step's route, `kvCertInv`'s producers in both modes, F5-2, S3-3); one first-tier finding, R6-1
(item 19's tie had no producer in `srvReqFieldsAtM`'s on arm), repaired by `kvTieM` (drafted);
S6-1 (`srvReqFieldsAtD` with `kvCertInv`, its off law `⊣⊢ srvReqFieldsAt ∗ kvCertInv`; `cmpReach`'s
docstring), S6-3, S6-4 in the items; S6-2 below. Uncertain, the storage side's S4:
`compactableOk_server` needs views only `start` makes (its user `NewServer.wp_proofCompact` runs
before `start`).

Still open, second tier: S-5/round 1's S-6 (the `kbCmpM E.γ.kb ↔ E.cmp` law to export), S-2'
(G2 through `store.Read`'s `certOk`). (S3-3 adopted: items 8, 12, 13.)

**Review round 7** (`notes/spec-first-study/m2-apply-review-7.md`, narrow): R6-1's repair sound,
**nothing in the first tier: the review rounds end.** Its second tier repaired in the text (S7-1,
S7-2, S7-4; S7-3's `kvTieM` docstring). First-tier findings per round: 6, 2, 2, 1, 2, 1, 0; of the
14 after round 1, 9 were caused by the previous round's repair, and three rounds (1-3) found the
same kind (a drafted copy missing a carrier) until the user's Q6 (a).

**Next: the user's approval batch** (Q5): the consolidated items above (1-15, 17-21, 14'), with
item 18 and the `NoDelPutAt` removal from mvcc's specs; Q3 (G2's route) still open; then the
Probe (the first proofs: item 18's re-proof, the commit step, S3-3's transfer lemma).


## The Probe (2026-10-31)

**Item 18, done.** mvcc's `store.updateCompactRev.spec`, `store.compactLockfree.spec` and
`store.Compact.spec` (exported `mvcc_store_Compact`) are now the approved drafts:
- *No `ErrFutureRev` arm* (`78024e8cd9`): `updateCompactRev`'s `rev > currentRev` branch is
  contradictory: `revMuBody`'s `idxLogAuth` of the committed log extends the caller's certificate
  (`idxLogAuth_cert_prefix`), and `rev < |logc|`. The callers lose their third case.
- *No `NoDelPutAt`*: `kiGet_avail`'s one use (a tombstone at main `c` in generation `j'`, the read's
  revision at `c` in a later one) is now the fixed loop's step: generation `j'+1`'s first revision is
  above the tombstone and at or below the read's, so at main `c` (`genRecreatedAt`), and `genAdv`
  steps past `j'`. Then `named_not_del`, `rangeAnswers_not_del`, `delKey`/`delKeyI`, `compactJobPre`
  lose the premise and `crevSafe` keeps only the certificate (`crevSafe_cert` gone); the proofs of
  `scheduleCompaction`, `updateCompactRev`, `compactLockfree`, `Compact`, `rangeKeys` follow.
- The Draft's `specD`s were checked `rfl`-equal to the new statements, then retired (the apply Draft
  now cites the real specs).
- Kept: `NoDelPutAt` and its laws (`M2StorageDraftRestore`'s Draft names it; not ours to edit);
  `CompactMode.lean`'s interim `irrNoDelPut` (the switch replaces that family: items 15, 19);
  v3rpc's `check_gives_nodup`'s `noFromKeyDelL` (no longer needed by compaction; a separate cleanup).
- Cost: as estimated (G6 cheap; the model's case about 30 lines).

**G2 by Q3's (a), checked (2026-10-31).** (a) as stated (an invariant law `idxCert γ.idx l ⊢ ∃ l',
certOk γ l' ∗ ⌜l <+: l'⌝`) is not available: the only `certOk` of the committed log outside a
transaction is `revMuBody`'s, under the `revMu` lock, and no invariant ties the index's log
(`monoListLbOwn γ.log`) to the `γ.cok` map. **A variant (a') closes it cheaply**: `store.Rev`'s proof
already holds `certOk γ log` of the log it read (`store.Read`'s post, `#Hrok` in
`store__Rev.lean`), so (1) `store.Rev.spec`'s post gains `mvcc.certOk γ log` (a strengthening; one
`iframe`; its reader corollary `specR` follows), and (2) `srvRevLb γ n` gains `certOk γ log` beside the
`idxCert` (its definition, `CompactMode.lean`; `EtcdServer.Compact.spec`'s text unchanged, the frozen
`v3compactor` specs unchanged: `RevLb` is their parameter). The server's step is then the existing
`kv_cert_read` (`KVLemmas.lean`, `hγ : γs.cok = γk.cok`), which is the commit route's (item 6)
already: `cmpReach` could be `srvRevLb`'s form directly. **The user approved (a') (2026-10-31); done:**
`store.Rev.spec`'s post `idxCert ∗ certOk ∗ ⌜…⌝` (proof: `iframe Hrok`; `spec_R` drops it, `specR`
unchanged), `srvRevLb`'s definition with `certOk` (`srvRevLb_mono`), `EtcdServer.Compact`'s proof's
pattern; the law `cmpReach_of_srvRevLb` (server Draft, proved: `kvCertInv γ γk -∗ srvRevLb γs (sint.Z r)
={E}=∗ cmpReach γk r`, the free certificate excluded as in `kv_cert_read`). G2 closed.

**The commit step (G4), the compaction arm: done (2026-10-31).** `etcdserver/M2ApplyProbe.lean`
(imported by nothing, as the Drafts; no `axiom`/`sorry`): `kv_prop_au_cmp` (a compaction proposal's
`srvPropAu1` over `kvInvD γ γk cmp`, from `reqPropOkD`'s compaction form, `kvCertInv` and
`srvRaftLogInv`, at a mask with `kvcN` and `srvRaftN`), by the route of item 6: the leading step
`cmpReach_reqLb` (at the caller's mask, `kvCertInv` opened: a start revision gives the empty
prefix, the start log having two revisions; a map element gives a committed raft log `A`, turned
into a lower bound `L₀` of the requested entries by `srvReqLogLb_of_rlogLb`, `kvModel_eqv` relating
their models); inside the update `srvReqLogLb_prefix` puts `L₀` below the invariant's log, and
`kvRaftOf_prefix` gives the claim. Helpers: `cmpLogOk_snoc`, `compactPropOkD_nonwrite` (a
compaction leaves the model: `kvModelSt_snoc_nonwrite`), `kvWorkD_snoc`; the Draft gained
`kvWorkD_timeless`. As predicted, no surprise. Left for the switch (mechanical, not the risk):
today's three arms re-run over `kvInvD` (a plain entry keeps `cmpLogOk` by `cmpLogOk_snoc` with a
vacuous claim), assembled as `kv_prop_au` over `reqPropOk` in place, and the auth-on twin
`kv_prop_au_M`. Next in the Probe: S3-3's transfer lemma (item 8).

**S3-3's transfer lemma (item 8): done (2026-10-31).** `M2ApplyProbe.lean`: `kv_entry_claim` (`⊢
kvInvD γ γk cmp -∗ srvRaftLogInv γ -∗ srvRLogLb γ (A ++ [m]) ={⊤}=∗ ⌜cmpEntryOk γk cmp A m⌝`), at
`kv_log_plain`'s shape: `applyEntryNormal`'s proof calls `kv_log_plain γr.raft γr.kv (A ++ [m]) $$
HkI HrI HAm` (`EtcdServer__applyEntryNormal.lean:272`) and has the same three hypotheses, so at the
switch (`kvInv γ γk = kvInvD γ γk γk.cmp`) the call beside it is `kv_entry_claim … γr.kv.cmp A m`. Its
pure core `cmpEntryOk_transfer`: a compaction entry is no filler or empty `ConfChangeV2`, so
`opsOf` keeps it; by `srv_eqv_prefix` the prefix `A'` of the invariant's log `L` with `A`'s requested
entries has length `|opsOf A|`, `L`'s next entry has `m`'s type and data, `cmpLogOk L` at that index
gives the claim at `A'`, and `kvModel_eqv` moves it to `A` (under the invariant's `c0 ≤ ai0`). No
surprise. What the switch still needs there: the mode `γr.kv.cmp` read as `E.cmp` (S-5's law, by
item 19's tie), for `cmpAdmit_of_entry`.
