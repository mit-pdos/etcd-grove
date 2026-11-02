# M2 apply side, Draft: review round 5 (2026-10-30)

Reviewed: `m2-apply` at `1f47d97679` ("round 4 and its repair": item 14', items 5, 6, 8, 12, 13,
17, 19 restated, `cmpLogOk` last in `kvInvD`). Targets: the three Drafts and the consolidated item
list of `notes/m2-apply-plan.md`, "The switch in place". Judged under the in-place convention (the
user's Q6 (a)); "the off texts mean today's by laws, not `rfl`" is not re-raised.

- **Checked:** `etc/lean-check.py -q -a` on the three Drafts: 0 errors.
- **Go:** nothing new read beyond round 4's; no Go bug found, nothing for `issues/`.

## Round 4's R4-1: resolved in the list

- Item 14' puts `ρ.rd.kv.cmp = E₀.cmp` on the three interim texts. They are the only `NewServer`
  statements that build `srvBuilt` and its `srvKVInvs`: `NewServer.spec` (`Spec/…/NewServer.lean:125`),
  `specCompact` (`:277`) and `specM` (`:432`).
- `specM`'s premise `ρ.rd.kv.cmp = false` serves both arms, since `E₀.cmp = false` there.
- In the specs Draft, `NewServer.specD`'s `#Hkvinv` stays `kvInvD … E₀.cmp`, with a comment
  giving the switch's form (`M2ApplyDraftSpecs.lean:192-195`). That is acceptable: the Draft cannot
  add the field.
- The *producers* of the premise are named only loosely (S5-3).
- `k8sdaemonset/apimodel`'s `NewServer` is a different function, not a caller.

## First tier

### F5-1. Item 6 / G4: the compaction form's `cmpReach` cannot be used at the commit step

- **Principle:** Complete. The form's consumer must be able to get what it needs from what it
  holds.
- **Where the form is consumed.** `reqPropOk`'s compaction form carries `cmpReach γk r := ∃ l,
  kvCert γk l ∗ ⌜r < l.length⌝` (server Draft, `cmpReach`). It is consumed at the commit:
  - `kv_prop_au` (`KVLemmas.lean:235-240`) runs inside `processInternalRaftRequestOnce`'s proof,
    through `kv_prop_au_M` (`EtcdServer__processInternalRaftRequestOnce.lean:225-228`, mask `⊤`);
  - there, G4 must record `cmpEntryOk γk γk.cmp L e`, i.e. `r < (kvModel γk L).length`, where `L`
    is the invariant's log at the commit.
- **What that proof holds.** It has only what `processInternalRaftRequestOnce.spec` gives it:
  - `isServerReqM`, i.e. `srvReqFieldsAt(M)` (`InvProposer.lean:401-423`, `ReqOn.lean:375-394`);
  - from that, `kvInv ρ.raft ρ.kv` and `srvMintInv`;
  - `srvRaftLogInv`, through `raftPropose` (`InvRequest.lean:1071-1072`).
- **What it lacks: `kvCertInv`.** `waitInv` and `srvIndexInvs` do not carry it either
  (`InvRequest.lean:1024, 1474`). Without it, `kvCert γk l` is only a ghost-map fragment
  (`InvRequest.lean:412-413`) and says nothing about the model. `kv_cert_read` needs `kvCertInv`
  (`KVLemmas.lean:766-769`).
- **Even with `kvCertInv`, G4's plan is not enough.** The plan says "`kvCertInv` opened beside
  `kvInv`" (plan, Gaps, G4), but that does not close the comparison:
  - `kv_cert_read` yields `srvRLogLb γ A` of a committed log;
  - relating `A` to the invariant's `L` needs `srvRLog_lb`, which needs `srvRaftN` in the mask
    (`SrvRaftLog.lean:778-779`);
  - `srvPropAu1`'s atomic update runs at `⊤ \ ↑srvRaftN` (`SrvRaftLog.lean:569`);
  - so the comparison cannot happen inside the update.
- **Caller affected:** `EtcdServer.Compact` (item 15), the only proposer of the form. The write
  forms do not read it.
- **Restatement** (cheap; the same kind of edit as item 19):
  - **(i) The certificates' invariant on the request path.** Item 19 adds `kvCertInv ρ.raft ρ.kv`
    beside the tie in `srvReqFieldsAt`, and `kvCertInvM on …` (`ServerOn.lean:241`) in
    `srvReqFieldsAtM` at the same place. That keeps both `rfl` laws.
    - `NewServer` already has it: `srvBuilt`'s `srvKVInvs` at `γr = ρ.rd` (`InvBuild.lean:328, 339`).
    - `kv_prop_au` takes `kvCertInv` and `srvRaftLogInv`, at a mask holding `kvN`, `kvcN` and
      `srvRaftN`. Its caller already passes `⊤`.
  - **(ii) G4 restated.** Before the update is built, at the outer `⊤`:
    - turn `cmpReach` into a bound on the invariant's current log `L₀`, as `kv_cert_floor` does
      (`KVApply.lean`: `kv_cert_read`, `srvRLog_lb`, `srv_eqv_prefix`, `kvModel_eqv`);
    - keep `monoListLbOwn γ.raft.log L₀`, taken from the invariant's half (`monoListLbOwn_get`,
      Perennial `Ghost/MonoList.lean:147`).
  - **Inside the update:** `mono_list_auth_lb_valid` (`:107`) gives `L₀ <+: L`, and
    `kvRaftOf_prefix` gives the length bound.
  - **Rejected alternative:** state `cmpReach` over a committed raft log. That needs
    `ServerRaftNames` in `reqPropOk γk rq Qr`, a signature change for every carrier.

### F5-2. Item 15: `Compact.specD` does not tie the reader's names to the proposer's, so the proposal's `cmpReach ρ.kv r` has no source

- **Principle:** Complete. The function's own proof must be able to establish its callee's
  precondition from its own.
- **What the proof must produce.** `Compact.specD` (`M2ApplyDraftSpecs.lean:~262-272`) takes
  `isServerReq s E ρ` and `isServerRead s E γr`, with no relation between `γr` and `ρ.rd`. Its proof
  must hand `processInternalRaftRequestOnce.spec` the compaction form at `ρ.kv`, i.e.
  `cmpReach ρ.kv r`, a `kvCert` in the map `ρ.kv.cok`.
- **What it can get.** Its premise is `srvRevLb E.γ r`. The closable source the plan names (G2 (a),
  `cmpReach`'s docstring) is an `idxCert` → `certOk` law, which gives a certificate at `E.γ.cok`.
- **Where that lands:**
  - the only fact relating `E.γ.cok` to the KV names is `srvKVInvs E γr`'s `E.γ.cok = γr.kv.cok`
    (`InvApplier.lean:332-334`), reached through `isServerRead`;
  - `isServerReq` relates neither: `srvIndexInvs` hides its own read names
    (`InvRequest.lean:1474`), and no field of `srvReqFieldsAt` mentions `cok`;
  - so the certificate lands at `γr.kv`, not at `ρ.kv`.
- Today's `Compact.spec` has the same untied pair, but it passes `srvRevLb` unchanged to
  `processInternalRaftRequestOnce.specCompact`, so the question never arose.
- **Callers affected:**
  - `compactableOk_server` (`CompactEnv.lean:69-75`; untied too);
  - `kvServer.Compact`;
  - the compactor's environment in `NewServer.lean:2033`.
  All get the server's views from `start`, whose `isServer` has `⌜ρ.rd = γr⌝`
  (`InvApplier.lean:528`), so they can supply the tie.
- **Restatement:**
  - Under G2 (a), write `isServerRead s E ρ.rd` (drop `γr`), or add `⌜γr = ρ.rd⌝`. Do the same in
    `compactableOk_server`.
  - Under G2 (b), the premise becomes `cmpReach ρ.kv r` in place of `srvRevLb E.γ r`.
  - Either way, item 15's text as listed is not the one that switches. Q3 should be decided with
    this.

Nothing else is in the first tier.

## Second tier

### S5-1. Items 8/12/13: S3-3 is plausible, and the "fallback" is not an independent one

**What `applyEntryNormal`'s proof holds** (`EtcdServer__applyEntryNormal.lean:248-276`):
- `#HAm : srvRLogLb γr.raft (A ++ [m])`;
- `#Hkvi : srvKVInvs E γr`, which gives `kvInv`, `srvRaftLogInv` and, with item 19, the tie;
- it already opens the KV invariant at `⊤` (`kv_log_plain`, `:272`).

So deriving `cmpEntryOk γr.kv γr.kv.cmp A m` there needs no new resource. It does need a lemma that
is not today's per-entry transfer:
- `srv_entry_transfer` (`SrvRaftLog.lean:305`) works entry by entry, but `cmpEntryOk` reads the
  model of the prefix before the entry.
- The proof:
  - a decoded compaction is no filler, so `opsOf (A ++ [m]) = opsOf A ++ [m.toLE]`;
  - `srv_eqv_prefix` (`:357`) then gives `L.take (k+1)`, whose last entry has `m`'s type and data,
    and `L.take k` equivalent to `A`;
  - `kvModel_eqv` (`KVLemmas.lean:162`) makes their models equal;
  - `cmpLogOk_prefix` and `cmpLogOk_snoc_entry` finish.
- `cmpAdmit_of_entry`'s `hkb` then needs `γr.kv.cmp = E.cmp` (the tie) and S-5's
  `E.cmp → kbCmpM E.γ.kb` law (still open, S5-6).

**The fallback.** It puts `cmpLogOk` in `srvC(M)`, which `run` reads at `A ++ ce`
(`EtcdServer__run.lean:59`). That is sufficient for `run`. But:
- `srvC` is raft's `E.C`, produced by `rnEnvOk_of_cluster` from `clusterWorkloadOk`
  (`BuildGap.lean:226-237`, `InvBuild.lean:219`);
- `clusterWorkloadOk_of` (`BuildGap.lean:120`) would need the very same transfer (G1).
- So the fallback rests on the lemma S3-3 rests on, and adds costs: `srvC`, `clusterWorkloadOk(M)`,
  and three spec texts.

**Restatement:**
- Commit to S3-3 in the list: items 8, 12 and 13 become "unchanged".
- State the lemma as the gap, for example `kv_cmp_entry : kvInv γ γk -∗ srvRaftLogInv γ -∗
  srvRLogLb γ (A ++ [m]) ={⊤}=∗ ⌜cmpEntryOk γk γk.cmp A m⌝`.
- Keep the fallback as a note, not as an item to approve. A conditional text is hard to approve.

### S5-2. Item 6's other consumers of `reqPropOk`: nothing breaks

Besides `kv_prop_au` (F5-1), these consume it:

- **`reqPropOk_wire`** (`KVLemmas.lean:656-680`): the compaction form must carry to the wire
  request.
  - It has `irrNoZeroEnd`, so `rq' = withHeader rq hm`.
  - It needs `compactPropOkD`, `rqShapeD` and `.compaction` to ignore the header. These are
    mechanical lemmas like `dispatchKind_withHeader`.
- **`reqPropOk_shape` and `reqPropOk_qinv`** (`:446-465`): fine, since `Qr` is trivial.
- **Positional `icases` and introductions**, which gain one level (mechanical):
  - `KVLemmas.lean:255, 450, 661`;
  - `InvProposer.lean:224, 251, 277`;
  - `InvMonitors.lean:92`;
  - `MonitorsOn.lean:76`.
- **`reqPropOkM false`** (`ReqOn.lean:582`): unchanged in text.
- **`reqPropOkOn`**: separate, and has no compaction form (the auth-on mode is outside the scope).

Item 6 should list `reqPropOk_wire`'s header lemmas.

### S5-3. Item 14': the premise's producers

The `KVNames` record is not built in `examples/common/Alloc.lean`. These places build or carry it:

- **The cluster allocations:**
  - `srvClusterBoot_alloc` (`NewServerAlloc.lean:250-252`): a positional `⟨…⟩` literal of
    `KVNames`, which breaks when a field is added;
  - `srvClusterBootOn_alloc` (`NewServerAllocOn.lean:166`; exported, `Results.lean:2116-2143`).
- **`kvInv_alloc_boot`** (`BuildAlloc.lean:107`): its `hok` builds `plainLog`; at any mode it
  needs `plainLogM cmp` and `cmpLogOk_plain`.
- **The member allocations:** `srvMemberBoot(On)_alloc`, whose facts list `ρ.rd.kv.cok`
  (`NewServerAllocOn.lean:227`). They gain `ρ.rd.kv.cmp`.
- **The examples:**
  - the member bundle's pure facts (`examples/common/Defs.lean:186`) take the mode, `true` for
    `putgetc`'s member;
  - `Alloc3.lean` (one `KVNames` for the three members);
  - `authkv/startServer.lean` (`specM true`, at `false`).

**Restatement:** the cluster allocations take `cmp` and state `γk.cmp = cmp`. All three `NewServer`
texts are covered. Only the producer list is missing.

### S5-4. Item 19's text contradicts round 4's S4-1

Item 19 says the tie "breaks two `rfl` laws used 14 times". That is not so: with the conjunct
added at the same place in `srvReqFieldsAt` and in `srvReqFieldsAtM`, both
`srvReqFieldsAtM_false` (`ReqOn.lean:400`) and `isServerReqM_false` (`:564`) stay `rfl`.

**Restatement:** "in both texts at the same place; the `rfl` laws kept". Also mention F5-1's
`kvCertInv(M)` conjunct.

### S5-5. Item 5/6: name the users of the `CompactMode` family

Items 5 and 6 drop the `CompactMode` family. Its users need restating, and the list does not name
them:

- `compactableOk_server` (`CompactEnv.lean:69`, over `isServerReqC`);
- `processInternalRaftRequestOnce.specCompact` (`Spec/…:84`);
- `StartCompactingServer`;
- `putgetc/MainLinked`.

Item 6's "`specCompact` goes" is also ambiguous. There are two:
- `processInternalRaftRequestOnce.specCompact` goes;
- `NewServer.specCompact` stays until item 14 (14').

### S5-6. Still open (carried)

- S-5: the `kbCmpM E.γ.kb ↔ E.cmp` law. S3-3's in-proof derivation now needs it too (S5-1).
- S-2'/G2: decide it with F5-2.

## What is good

- **R4-1's repair is right and minimal:** one premise on each of three texts, and every
  `srvBuilt` producer is covered.
- **Moving `cmpLogOk` last in `kvInvD`** keeps the positional indices, with `kvInvD_off_pure`
  generalised.
- **The S3-3 route is sound in design.** `applyEntryNormal`'s proof has every resource it needs.
  Only the transfer lemma is new work.
- **The in-place convention holds up.** The carriers listed in round 4 still need no copy. This
  round's findings are about resources a consumer lacks, not about copies.
- **The apply Draft is unchanged and still approvable.**

## Per-item verdicts

| Item | Verdict |
|---|---|
| 1 `dispatchOk` in place | approvable |
| 2 `dispatchAnswer`/`dispatchResult`/`applyResultIs` | approvable |
| 3 apply vocabulary | approvable |
| 4 A1 record | approvable |
| 5 `kvInv` in place | approvable. Name the `CompactMode` users (S5-5) |
| 6 `reqPropOk` in place | text approvable. Its compaction form is unusable at the commit without F5-1 (i)/(ii). List `reqPropOk_wire`'s header lemmas (S5-2) |
| 7 `crevOf` | approvable |
| 8 dropped if S3-3 works | commit to "dropped" (S5-1) |
| 9 `cmpTriple` | approvable |
| 10 `Compaction.specD` | approvable |
| 11 `dispatch`/`Apply.specD` | approvable (S-5's law open) |
| 12 `applyEntryNormal.spec` | "unchanged" (S5-1). Drop the conditional |
| 13 `applyEntries`/`applyAll`/`EtcdServer.apply`/`run` | "unchanged" (S5-1). Drop the conditional |
| 14 `NewServer.specD` | deferred (Q4); its comment is accurate |
| 14' interim `NewServer` texts | resolves R4-1. List the producers (S5-3) |
| 15 `Compact.specD` | **F5-2**: tie `γr` to `ρ.rd` (or G2 (b)'s premise) |
| 16 | withdrawn |
| 17 snapshot track | the collaborator's; as listed |
| 18 mvcc without `ErrFutureRev` | approvable |
| 19 the ties | approvable once `kvCertInv(M)` is added beside the tie (F5-1 (i)) and the `rfl` sentence is corrected (S5-4) |
| 20 `srvKVCloserW` | approvable |
| 21 `Apply.specRecD` | approvable |

## Ranking by need of revision

1. **The plan's item list:**
   - F5-1: item 19 gains `kvCertInv(M)`; G4 restated (the proposal-time bound and the mono-list
     lower bound);
   - F5-2: item 15's tie, decided with Q3;
   - S5-1: items 8/12/13 committed to S3-3;
   - S5-3, S5-4, S5-5.
2. **Specs Draft:** `Compact.specD`'s `isServerRead s E ρ.rd` (F5-2).
3. **Server Draft:** `cmpReach`'s docstring and G4's description of where the bound is taken
   (F5-1 (ii)).
4. **Apply Draft:** nothing.

**The first tier is not empty:** F5-1 and F5-2. Both are missing-resource defects in the request
path's compaction proposal, the one place a compaction enters the log, and each is cheap to repair:
- F5-1: one conjunct in each of the two request-path texts, and G4's proof plan;
- F5-2: one premise.

Like round 4's R4-1, they are in what the previous rounds took as given (G4's "opened beside
`kvInv`", round 4's "the same proposition when `γr = ρ.rd`"), not in round 4's repairs. Those
repairs (items 5, 6, 8, 12, 13, 17, 19, 14') introduce no new defect beyond S5-3/S5-4's
wording.
