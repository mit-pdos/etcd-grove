# M2 apply side, Draft: review round 3 (2026-10-30)

Reviewed: `m2-apply` at `16b287b96a` (the repair of round 2, `m2-apply-review-2.md`). Files: the
apply Draft (`etcdserver/apply/M2ApplyDraft.lean`), the server Draft (`etcdserver/M2ApplyDraft.lean`),
the specs Draft (`etcdserver/M2ApplyDraftSpecs.lean`), against `notes/m2-apply-plan.md` (items 1-21,
"Review round 1/2: the repair").

- **Checked:** `etc/lean-check.py -a` on the three Drafts: 0 errors (working tree clean).
- **Go:** at the pin `249d76bea7` (`/shared/etcd-grove/.lake/go-src/etcd`; the worktree has no
  `.lake/go-src`).
- **No Go bug found**, so nothing for `issues/`. Re-checked: `backend.go:66-80`. `Compaction`
  returns `nil, ch, nil, err` on an error, which `cmpAnswerIs`'s error arm matches: it leaves `ch`
  free and sets trace = null. `Range` at the latest revision cannot fail after a successful compact,
  so `rr` is not nil. `v3_server.go:393-429` reads `result.Trace` before `result.Err` and overwrites
  the header.

## Round 2's findings at `HEAD`

### N-2 (the second copy of the KV invariant): fixed where it was found, not everywhere

`srvReqFieldsAtD` (server Draft :453-471) is `srvReqFieldsAt` (`InvProposer.lean:405-423`) with only
`kvInv ρ.raft ρ.kv` replaced by `kvInvD ρ.raft ρ.kv E.cmp`. `isServerReqD` has today's shape, and
`isServerReqD_off`/`isServerReqD_kvInv` check. **But the same defect is still in the next conjunct
of the same precondition** (R3-2 below): `isServerRead` carries today's off `kvInv` through
`srvKVInvs`.

### N-1 (the shape chain excluding compaction): half fixed

- **What is drafted:** the two ends.
  - The invariant's side: `rqShapeD`, `entryShapeD`, `logShapeD`, `kvWorkD`, and `kvInvD` over
    `kvWorkD cmp`. `reqPropOkD`'s compaction form uses `rqShapeD true`.
  - The apply thread's premise: `entryOkD`, `entryOkOnD`, `entryOkMD`.
  - Each is today's at `cmp = false` by `rfl`. I checked that `rqOk` of a compaction is `True`
    (`apply/Chain.lean:285`), so `entryOkD` is satisfiable for one.
- **What is not drafted:** every link in between (R3-1). This is the place round 2 warned about:
  the repair again stopped at the vocabulary.

## First-tier findings

### R3-1. The middle of the chain is not mode-indexed: the raft environment, the workload clause and three trusted apply-loop texts still read `logShape`/`logShapeM` (items 1, 8, 12, 13, 14; a repair regression of N-1)

- **Principle:** Complete; the texts submitted for approval are the switch's texts.
- **Evidence.** The path from a committed compaction entry to `applyEntryNormal`'s call of `Apply`,
  with what each link reads at `HEAD`:

  | link | reads | drafted? |
  |---|---|---|
  | `kvInv` → `kvWork` | `logShape` | yes (`kvInvD`/`kvWorkD`) |
  | `clusterWorkloadOk` (`InvBuild.lean:255-257`), the auth twin `clusterWorkloadOkM` (`ServerOn.lean:276-277`) | `⌜logShape L⌝`, `logShapeM on L` | **no**; item 8 adds only `cmpLogOk` |
  | `clusterWorkloadOk_of` (`BuildGap.lean:120-179`), `batchWaitOk_of_work` (`BuildGap.lean:43-44`) | `logShape` (proof) | no (G1 names the transfer only) |
  | raft's `E.C`: `srvC` (`InvRun.lean:182-184`), `srvCM`/`logShapeM` (`ServerOn.lean:59-62, 252-254`) | `⌜srvIdxOk ai₀ L ∧ logShape L⌝` | **no** |
  | `srvBuilt`'s `⌜Er.C = srvC ρ E ai₀ c₀ x₀ …⌝` (`InvBuild.lean:334`), so `NewServer.specD`'s post `srvBuilt … (srvEr ρ E₀ …)` (specs Draft :237) and `run.spec`'s `isServerRun` | `srvC` | no |
  | `run`'s proof (`EtcdServer__run.lean:59, 101`) | `logShape (A ++ ce)` → `logShape (unapplied ai ce)` | — |
  | **`EtcdServer.applyAll.spec`** (`Spec/…/EtcdServer__applyAll.lean:60`; `:128` `logShapeOn`) | `logShape (unapplied ai ms)` | **no; text** |
  | **`EtcdServer.applyEntries.spec`** (`…__applyEntries.lean:46`) | `logShapeM E.authOn (unapplied ai ms)` | **no; text** |
  | **`EtcdServer.apply.spec`** (`…__apply.lean:44`) | `logShapeM E.authOn ms` | **no; and not in item 13 at all** |
  | `entryOk_of_shape` (`InvApplier.lean:120`) | `entryShape` → `entryOk` | no (plan: "glue still to write") |
  | `applyEntryNormal.spec` | `entryOkM` → `entryOkMD E.authOn E.cmp` | yes |

- **What follows:**
  - **`NewServer.specD`'s on arm is unprovable.** Its post makes the raft node's environment
    `srvC`, which promises `logShape L` of every committed log. Once a compaction is committed that
    promise is false, and `kvInvD … true` gives only `logShapeD true L`. The specs Draft's header
    (:6-9) says to read the post with item 5's redefinition of `kvInv`. But `srvC` reads
    `logShape`, which item 5 does not touch.
  - **No real caller reaches `applyEntryNormal`'s compaction arm.** `run → applyAll → applyEntries →
    apply → applyEntryNormal` each take the batch's `logShape`/`logShapeM` as a premise, and a batch
    holding a compaction has none.
  - **The plan's item 13 is wrong.** It says `applyEntries.spec`/`applyAll.spec` change by "one
    pure conjunct each" and `run.spec` not at all. In fact each of the three texts must change its
    shape premise, `EtcdServer.apply.spec` (between `applyEntries` and `applyEntryNormal`) must
    change too, with the shape premise and the batch's `cmpLogOk`, and `run`'s "no change" holds
    only if `srvC` is redefined.
  - **Item 13's own source of `cmpLogOk` is also missing.** `run` gets its per-batch facts from
    raft's `E.C` (`srvC`), not from `clusterWorkloadOk`. So `srvC` must carry `cmpLogOk` too, not
    only `clusterWorkloadOk` (item 8).
- **Callers affected:**
  - `NewServer` (the post's raft environment), so every example over it once item 14 merges;
  - `run`/`applyAll`/`applyEntries`/`apply` (no compaction batch is admitted);
  - `request_delivered` through `applyEntryNormal`.
- **Restatement.** Finish option (a) through the middle, with the mode from `E` (in scope in all of
  them):
  - `logShapeM on cmp L := match on with | false => logShapeD cmp L | true => logShapeOn L` (see
    S3-1 for the on arm).
  - `srvCM on ρ E … L := ⌜srvIdxOk ai₀ L ∧ logShapeM on E.cmp L ∧ cmpLogOk ρ.kv E.cmp L⌝ ∗ …`;
    `srvC` is its off case.
  - `clusterWorkloadOk(M)` likewise (item 8 then covers both the shape and the claims).
  - The three spec premises become `logShapeD E.cmp (unapplied ai ms)` (applyAll) and
    `logShapeM E.authOn E.cmp …` (applyEntries, apply), each with `⌜cmpLogOk γr.kv E.cmp (A ++ …)⌝`.
  - Draft these definitions and texts in the server Draft (they are trusted vocabulary through
    `srvBuilt`/`isServerRun` and three trusted premises), list `EtcdServer.apply.spec` in item 13,
    and correct items 8/13/14 and the specs Draft's header.
  - Glue to list (mechanical): `entryOkD_of_shape`, `batchWaitOk_of_work`'s `logShapeD`,
    `logShapeD_append`, `KVApply.lean:62` (`hok : entryOk`), `KVApply.lean:139` (`plainLog B` of
    the applied log), `KVLemmas.lean:244` (`rqShape → entryShape` at the commit), `ModeSpecs.lean`'s
    `specOff`/`specOn` texts (`:378, :421, :483, :527`).
  - *Cheaper alternative for the claims only* (S3-3): derive `cmpEntryOk` inside
    `applyEntryNormal`'s proof, which removes `cmpLogOk` from the specs and from `srvC`. The shape
    premise still has to change.

### R3-2. `Compact.specD` still carries today's off `kvInv`, through `isServerRead`'s `srvKVInvs`: N-2's repair covered one carrier of `kvInv` out of several (items 15, 19, 14)

- **Principle:** Complete (a caller can establish the precondition); one convention per Draft.
- **Evidence.**
  - Compact.specD's pre (specs Draft :278) is `isServerReqD s E ρ ∗ ⌜E.cmp = true⌝ ∗ isServerRead
    s E γr ∗ …`.
  - `isServerRead s E γr` is `∃ v, srvReadFieldsAt s E γr v` (`InvRead.lean:148`), which holds
    `srvKVInvs E γr` (`InvRead.lean:135`), which is `kvInv γr.raft γr.kv ∗ kvCertInv …`
    (`InvApplier.lean:332-334`).
  - A real server meets `isServerRead` only at its own read names, `γr = ρ.rd`, and `ρ.kv` is
    `ρ.rd.kv` (`InvRequest.lean:772`). So the pre holds both `kvInvD ρ.raft ρ.kv true` and
    today's off `kvInv ρ.raft ρ.kv`: round 2's N-2 exactly (two `inv kvN`s, each owning half of
    `srvRLog`; the off one's `plainLog` forbids the entry).
  - Today's `Compact.spec` has the same pairing (`isServerReqC` beside `isServerRead`,
    `EtcdServer__Compact.lean:69`), so the defect predates M2. The Draft keeps it.
  - The same holds of every apply-loop spec over `isServer`/`isServerM` (both hold the off
    `kvInv` through `srvFieldsAt`), and of `NewServer.specD`'s `srvBuilt` (`#Hkvi ∷ srvKVInvs E γr`,
    `InvBuild.lean:328`, besides `srvReqBuilt`).
  - The Draft mixes two conventions:
    - `isServerReqD` is the switch's text, written out;
    - `NewServer.specD` is "read with item 5's redefinition";
    - `Compact.specD` follows neither for its `isServerRead`.
  - *The tie is missing on the apply side.* Item 19 puts `ρ.kv.cmp = E.cmp` in `srvReqFieldsAt`
    only. The apply side's `cmpEntryOk γr.kv E.cmp` (item 12) and the batch's `cmpLogOk γr.kv E.cmp`
    come from the invariant at `γr.kv.cmp`. Without the tie in `srvKVInvs` (or `srvEnvOk`), the
    apply thread's `E.cmp` and the invariant's mode are unrelated.
- **Callers affected:**
  - `compactableOk_server` (`CompactEnv.lean:71-74`, which takes `isServerReqC ∗ isServerRead`);
  - v3rpc's later `compactOk`;
  - the apply loop's caller once the tie is needed (item 12).
- **Restatement.** Pick one convention and state it once.
  - **Recommended: item 5 in place everywhere.** `kvInv γ γk := kvInvD γ γk γk.cmp`. Item 19
    becomes the tie `⌜ρ.kv.cmp = E.cmp⌝`, put once where both sides see it: `srvKVInvs` (`⌜γr.kv.cmp
    = E.cmp⌝` beside today's `⌜E.γ.cok = γr.kv.cok⌝`, which already has this shape), and through
    it `isServerRead`, `isServer(M)` and `srvBuilt`.
  - Then `isServerReqD` is not needed (`isServerReq` holds the redefined `kvInv`). The specs Draft
    says, for both `NewServer.specD` and `Compact.specD`: "every `kvInv` here, through
    `srvReqFieldsAt`, `srvKVInvs`, `srvReqBuilt`, is item 5's".
  - If instead the Draft keeps writing out switch texts, it must also draft `srvKVInvsD` and use it
    in `isServerRead` for `Compact.specD`.
  - Either way: one sentence or one definition, but as drafted the precondition is unsatisfiable
    at `E.cmp = true`.

## Second-tier findings

- **S3-1. The auth-on arm is wider than the plan's scope** (the brief's question).
  - The plan keeps retention 0 for auth-on servers: `NewServer.specM`'s `E₀.cmp = false`
    (`Spec/…/NewServer.lean:456-459`), and through `envAgree` `E.cmp = false`. The auth mode's own
    vocabulary agrees: `entryShapeOn` reads today's `rqShape` (`KVAuthModel.lean:674-676`), and
    `logShapeOn`, `kvWorkOn` (`:766-767`), `kvInvOn` (`:864`) and `srvCM true` all exclude a
    compaction.
  - But `entryOkOnD cmp` (server Draft :125-127) and `entryOkMD true E.cmp` admit one when
    `E.cmp = true`. `applyEntryNormal.spec` has no `E.authOn = true → E.cmp = false`.
  - So its proof's auth arm (`EtcdServer__applyEntryNormal.lean:1626` on) must handle a compaction
    under the auth chain and `kvAppliedOn`, a case no caller produces. This is consistent (no
    falsehood), but it is a cost.
  - Restate `entryOkMD on cmp := match on with | false => entryOkD cmp | true => entryOkOn` (the on
    arm today's), and say in its docstring that auth on means compaction off (`NewServer.specM`).
  - Do the same in R3-1's `logShapeM` (on arm `logShapeOn`). The `cmp` argument then means
    something only off. If auth on with compaction is ever wanted, the whole on family moves
    together.
- **S3-2. The plan's item texts the user will approve (Q5) are stale.**
  - Item 1 still shows `dispatchOk` redefined in place and "`rqShape`, `entryShape`, `logShape`,
    `kvWork` then admit a compaction textually unchanged". That is the design S-1 and N-1 replaced.
  - Item 12 still says "`entryOkM E.authOn x m` reads `dispatchOk` (redefined)".
  - Item 13 has the R3-1 errors.
  - Item 8 does not mention the shape.
  - The repair sections describe the changes, but Q5 asks for "items 1-16 as repaired". Rewrite
    the items themselves to state what is approved.
- **S3-3. A cheaper source of `cmpEntryOk`.** `applyEntryNormal.spec` already holds
  `srvRLogLb γr.raft (A ++ [m])` (`…__applyEntryNormal.lean:62`) and, through `isServerM`,
  `srvKVInvs`'s `kvInv` (with R3-2's redefinition and tie, the mode's).
  - A lemma `srvRLogLb γr.raft (A ++ [m]) ∗ kvInv … ⊢ |={⊤}=> ⌜cmpEntryOk γr.kv E.cmp A m⌝` (G1's
    transfer, done once, at the entry) would remove the conjunct from item 12, the batch's from
    item 13 and `apply.spec`, and `cmpLogOk` from `srvC`/`clusterWorkloadOk`. That is fewer trusted
    texts and no glue per caller (round 2's S-1').
  - *Uncertain:* that the transfer through `srv_entry_src` (the committed entry is a copy of a
    requested one, `BuildGap.lean:149`) yields the claim at `kvModel γk A` and not at the requested
    prefix's model. G1 must show the same either way.
- **S3-4. Round 2's open items, still open (not regressions).**
  - S-5 (`kbCmpM E.γ.kb ↔ E.cmp`, needed by `cmpAdmit_of_entry`'s `hkb` and every off reading of
    `cmpOwn`) is not exported.
  - S-4 (`srvKVCloserW` unfolds `wsCloserR`, specs Draft :53-59) is deferred to the switch.
  - S-2' (G2 by `store.Read`'s `certOk`) is recorded but not reflected in `cmpReach`'s docstring
    (:409-416), which still gives the `idxCert ⊢ certOk` law as the closable form.
- **Vacuity / consistency checks that pass.**
  - `dispatchOkM_false`, `rqShapeD_false`, `entryShapeD_false`, `logShapeD_false`, `kvWorkD_false`
    hold by `rfl`.
  - `entryOkMD_false` holds by cases.
  - `kvInvD_off` and `reqPropOkD_off` are equations or bi-entailments.
  - `crevOf_step`'s skipped/rejected cases are closed by `compactPropOkD`'s `noSideEffect`/
    `needAdminPermission`.
  - `cmpReach γk 1` holds through `kvCert`'s `length ≤ 2` arm (`InvRequest.lean:410-411`).
  - `cmpTriple`'s post revision agrees with `dispatchCrev` (`v3 ∧ compaction ∧ chainCompacts`).

## What is good

- **Apply Draft:** unchanged since round 2 apart from the docstrings (`dispatchOkD`'s now says
  `dispatchOk` stays). `cmp_not_future`, `cmp_store_pre`, `cmpAnswerIs`/`dispatchAnswerD` (the nil
  trace on errors), `dispatchOkM` and the three uber specs are ready.
- **Server Draft:**
  - The shape family is the right design. Each piece is `rfl` off, it follows
    `apply-loop-merge.md`'s mode-as-argument pattern, and `rqShapeD_of` makes today's proposals
    reusable.
  - `srvReqFieldsAtD` is a faithful one-conjunct edit.
  - `crevOf` and its lemmas are as round 2 found them.
- **Specs Draft:** `Compact.specD` now documents its scope restriction (round 2's S-6), and
  `srvKVCloserM_split` stands.

## Per-item verdicts

| Item | Verdict |
|---|---|
| 1 `dispatchOkM` and the shapes | vocabulary approvable; **blocked by R3-1** (the middle links: `logShapeM`, `srvC(M)`); plan text stale (S3-2) |
| 2 `dispatchAnswer` with the trace | approvable |
| 3 apply vocabulary | approvable |
| 4 A1 record | approvable |
| 5 `kvInvD` | approvable in text; **R3-2**: state it as the in-place redefinition everywhere (`srvKVInvs` included) |
| 6 `reqPropOkD` | approvable |
| 7 `crevOf` | approvable |
| 8 `clusterWorkloadOk` | **blocked by R3-1** (also `logShapeD`, and its twin `clusterWorkloadOkM`; `srvC` too) |
| 9 `cmpTriple` | approvable |
| 10 `Compaction.specD` | approvable |
| 11 `dispatch`/`Apply.specD` | approvable (S-5's law for the off reading) |
| 12 `applyEntryNormal` | premise approvable; S3-1 (on arm), S3-3 (conjunct droppable); the tie (R3-2) |
| 13 `applyEntries`/`applyAll` | **blocked by R3-1** (shape premises; `EtcdServer.apply.spec` missing; `run`'s "no change" needs `srvC`) |
| 14 `NewServer.specD` | deferred by Q4; **R3-1** (post's `srvC`), **R3-2** (`srvKVInvs`'s `kvInv`) |
| 15 `Compact.specD` | **blocked by R3-2** (`isServerRead`'s off `kvInv`); G2 |
| 16 | withdrawn |
| 17 snapshot track | the collaborator's; unchanged |
| 18 mvcc without `ErrFutureRev` | approvable |
| 19 the tie | **R3-2**: in `srvKVInvs` too (the apply side's `E.cmp`), not only `srvReqFieldsAt` |
| 20 `srvKVCloserW` | approvable (S-4 at the switch) |
| 21 `Apply.specRecD` | approvable |

## Ranking by need of revision

1. **Server Draft:** R3-1 (draft `logShapeM`/`srvC(M)`/`clusterWorkloadOk(M)` by the mode and the
   three apply-loop premises, `EtcdServer.apply.spec` included), R3-2 (the convention, the tie in
   `srvKVInvs`), S3-1, S3-3.
2. **Specs Draft:** R3-2 (`Compact.specD`'s `isServerRead`; the header's convention), R3-1 (the
   header's claim about `srvBuilt`).
3. **Plan:** rewrite items 1, 8, 12, 13 (S3-2).
4. **Apply Draft:** nothing left in the first tier; S-5's law.

**The first tier is not empty:** R3-1 and R3-2. Both come from round 2's repairs stopping short:
the vocabulary and the endpoints were drafted, the links between them were not. The cost of each
is below a round's: R3-1 is about six definitions and three or four spec lines, R3-2 one convention
and one tie.
