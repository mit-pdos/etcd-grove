# Lease-grant server chain, design review round 4: the unimplemented steps against the code

Reviewed: `notes/lease-grant-plan.md` at `13eaea2202` ("Design of the server chain", Freeze (A)/(B),
"Plumbing"), with amendment (C). The code is branch `lease-grant-3b`. During the review HEAD moved
from `13eaea2202` to `4400408fad` ("srvRest gated (srvGrantable, srvRestAt, laws, srvRest_applyG);
ids law; ApplyRec"). I read that commit as well, and I mark as **stale** any finding it already
fixes. No builds were run.

I checked these statements on the branch: `dispatch.spec` and `Apply.spec` with (C)
(`Spec/.../apply/uberApplier__{dispatch,Apply}.lean`, `grantOutOk` at `apply/Chain.lean:492`,
`grantOutOkA` at `apply/GrantRest.lean:37`); `grantPre`/`grantPost` (`Chain.lean:1561-1579`);
`grantRes`/`grantResA` (`InvUber.lean:367,422`); `grantIds`/`grantRest` with `v3`
(`Chain.lean:406,415`); `ltHalf`/`leasesLive` (`Chain.lean:559,600`); `grantPermRq`
(`Chain.lean:1532`); `dispatchStep`/`dispatchTable`/`chainTable`/`kvTable`
(`InvUber.lean:70`, `KVModelDefs.lean:379-436`). At `4400408fad` I also read `srvRest`,
`srvRestAt`, `srvRestAt_open`/`_map`, `srvGrantable`, `srvRest_applyG` (`InvRest.lean:550-720`),
the ids law (`AppliedTable.lean`) and `apply.Apply.specRec` (`apply/ApplyRec.lean:64-95`).

## Verdict first

- **(C) closes the outcome gap. The apply-thread chain for a grant entry now goes through.**
  - `dispatchTableA_ids` (`AppliedTable.lean@4400408fad`) proves the ids law from
    `grantOutOkA`, `applyStep` and `grantKindOk`. It rules out `.skipped` and `.rejected` through
    `noSideEffect`/`needAdminPermission`.
  - `chainTable_grant` matches `grantGoes`, because `cappedRejects .leaseGrant = true` and
    `corruptRejects .leaseGrant = true` (`Chain.lean:137-145`).
  - `leaseGrantOk lt ↔ grantIdsOk lt.ids` holds by `Iff.rfl`.
  - `srvRest_applyG` takes `x.chain = γr.kv.ch0` (which `kvApplied`/`kvAppliedOn` give) and
    `hv3`, and is generic in `E.lg`.
  - I found no other fact of this kind that is held only inside a callee.
- **Safe to implement as designed:**
  - §2.9's `srvRest_applyG` (done at HEAD) and the refutation inside `applySnapshot`.
  - §2.8's shapes.
  - `applyEntryNormal`'s auth-off arm.
  - Commit 4: the `reqPropOk` grant disjunct, `kv_prop_au_grant`, `kvInv` (C), and
    `appliedOkM`/`grantArM` with `raftRequest`/`processInternalRaftRequestOnce` text unchanged.
  - Commit 5's three leaves.
  - Each of these has minor glue listed below.
- **Need a decision or a design-text change before implementing:**
  - **§2.14's gate on `imageAt` (B1, blocker).** It breaks the congruence the receive side uses to
    move the network's image certificate to the receiving member.
  - **§2.13 together with commit order (S1).** `NewServer` cannot build `srvRest`'s leased arm at
    `on = true` until m4's `ρ.rd.kv.lg = false` premise is in place. m4 is scheduled for commit 4
    but is needed in 3b.
  - **The conf-change arm of `EtcdServer.apply` (S2).** `srvRestAt_map` hides the image, but
    `applyConfChange.spec` needs pure facts about it.

## Findings

### B1 (blocker, §2.14): gating `imageAt` on `γk.lg` breaks `dbImage_kv_congr`, so the receive side's image is unprovable

- **The (A) pattern.** A definition change blocks a congruence that a caller relies on.
- **Evidence.** The image certificate on the network is
  `srvImage γ i D := ∃ γk, ⌜γk.c0 = 0 ∧ γk.ch0 = alarmChain false false false ∧ γk.log0 = [[],[]]⌝ ∗ dbImage ⟨γ,[],0⟩ γk i D`
  (`InvImage.lean:121-123`).
  - The `γk` there is the sender's, and `srvImage` pins its start values but not its `lg`.
  - A receiver moves the certificate to its own names with `dbImage_of_srvImage`
    (`InvImage.lean:160-170`), which goes through `dbImage_kv_congr` (`:129-146`). That lemma is
    true only because `imageAt` reads `γk` solely through `c0`/`ch0`/`log0`.
  - §2.14 makes `imageAt` read `γk.lg`
    (`if γk.lg then bkRestAtL … else bkRestAt …`). `dbImage_kv_congr` would then need
    `γk.lg = γk'.lg`, and the receiver has no way to know the sender's `lg`.
  - Nothing cluster-wide carries `lg`: `SrvRaft` has no such field, and `KVNames` is per member.
- **Caller affected.** `snapRecv_image` (`SnapRecvFacts.lean:341-342`, then `:396-397`, which
  destructures `imageAt`'s 4th conjunct as `bkRestAt` for `image_bootBuckets` and for `hlease`).
  `EtcdServer.applyAll.wp_proofSnap` calls it at `ApplyAllSnap.lean:125`. §2.14's sentence
  "`bkRestAt`, `bkRestAt_boot`, `SnapRecvFacts`, `KVModelRestore` keep their text and proofs" is
  therefore false.
- **Proposed fix.** Do not gate `imageAt`.
  - State its rest conjunct as `bkRestAtL γk bootLog L D` at every `lg`. This is already defined:
    ∃ `f` over `(kvLeases γk L).ids`, where `kvLeases γk = kvTableOf γk.c0 γk.ch0 []`. That reads
    only `c0`/`ch0`, so `dbImage_kv_congr` keeps its premises.
  - Add one law: `bkRestAt_of_L : (kvLeases γk L).ids = [] → bkRestAtL γk bootLog L D → bkRestAt γk.c0 bootLog L D`
    (via `restLeasesWith_nil`).
  - `snapRecv_image` applies it with its own `kv_log_plain` (`Hpl0`, `plainLogM γk.cmp γk.lg A'`).
    Here `γk.lg = false` comes from `specSnap`'s premise (`EtcdServer__applyAll.lean` spec, `:282`),
    and `kvTableOf_plainM` (`KVModelDefs.lean:791`) then gives empty ids. That is two lines.
  - Keep `mergedObs` gated on `E.lg` (S-1's reason still holds for the window at `on = true`).
  - `merged_image` (the S2 `sorry`) converts both arms to the ungated image; at `lg = false` it uses
    the same plain-log fact. It stays true.
  - `bkRestAt_boot` gives `bkRestAtL` at boot via m3, since the boot prefix grants nothing.
  - The alternative is to pin `γk.lg` inside `srvImage`. That needs a cluster-wide `lg` that does
    not exist, so it is a larger change.

### S1 (should fix, §2.13 and §3's commit order): `NewServer` at `on = true` cannot give `srvGrantable`

- **Evidence.**
  - `NewServer` creates the lessor with guard `srvGrantGuard ρ.rd.kv.lg on`
    (`NewServer.lean:585`), which is `⌜leasesNoExpiry ∧ lg = true ∧ on = false⌝`
    (`InvApplier.lean:481-482`).
  - It sets `E.lg := ρ.rd.kv.lg` in both modes (the `AEnv` literal, `NewServer.lean:1170` and the
    others).
  - The proof is one theorem generic in `on` (`NewServer.wp_proofG (on cmp)`, `:212`).
  - `srvRest`'s leased arm (HEAD `InvRest.lean:561-565`) contains `srvGrantable E`, whose
    `∀ id, leaseGranted E.γ.leases id` needs `□ GA id` of that guard. At `on = true ∧ lg = true`
    that is `False`.
  - m4 (`NewServer.specM true`/`specG` at `on = true` take `ρ.rd.kv.lg = false`) is listed under
    commit 4 (§3, item 4). The plan's 3b list puts "`NewServer`'s allocations / `srvRest` half" in
    3b.
- **Caller affected.** 3b's `NewServer.wp_proofG`. It does not build without m4.
- **Proposed fix.** Move m4's two frozen-text rows (already approved) into 3b. The law case-splits
  on `on`: at `on = true`, `lg = false`, so `srvRest_false` applies. No new statement is needed.

### S2 (should fix, §2.9 and §2.0, the conf-change arm of `EtcdServer.apply`): the image hidden by `srvRestAt_map`

- **The (C) pattern.** A law existentially hides the image, but the callee needs facts about it.
- **Evidence.**
  - `srvRestAt_map` (HEAD `InvRest.lean:612-627`) gives `∃ r', E.RO r' ∗ (E.RO (g r') -∗ …)` with
    nothing known about `r'`.
  - The conf-change arm passes `E.RO rs` to `applyConfChange.spec`, whose premises are pure facts
    about `rs` (`Spec/.../EtcdServer__applyConfChange.lean:79-86`):
    - `srvCCPre … (membership.ccRaftEff rs.bk m)`;
    - `GMap.size (insert … rs.mem) ≤ 2^62`;
    - `(rs.bk.lookup "members").isSome` and `(rs.bk.lookup "members_removed").isSome`;
    - `membersDecode rs.bk`.
  - Today these are established at `rs := restModel …`: `membersDecode_restModel` and
    `restModel_members` (`EtcdServer__apply.lean:584, 614-616`). The post's `ccPeersAfter v3 m rs.bk`
    and the boot case's `hbk : (restModel …).bk = restBootBk` with `ccValidOn_boot` (`:661-668`)
    also read `rs`.
  - The design names only "`restEntry` commutes with `restGrantT`".
- **Proposed fix.**
  - In this arm, use `srvRestAt_open` (which gives `r' = restLeasesWith f (srvIds E T) r`), not
    `srvRestAt_map`.
  - Add transfer lemmas: `restLeasesWith` leaves the `members` and `members_removed` buckets and
    `mem` (from `restGrantT_putIn`-style lookups and `restLeasesWith_mem`). With (A), `ccValidOn`,
    `ccRaftEff`, `ccPeersAfter` and `membersDecode` are then equal at `r'` and `r`. All of them are
    bucket-local after (A); I checked `InvRest.lean:93,125,199` and `InvApRes.lean:58`.
  - Close the arm with `ccRest_restGrantT` lifted by `restLeasesWith_comm` (as `srvRestAt_map` does)
    and `appliedTable_cc`.
  - This is mechanical, but name it in §2.9 so that the arm does not try `srvRestAt_map`.

### S3 (should fix, small): the auth-on arm's admin rewrite assumes the old `srvRest`

- **Evidence.** `srvRest_admin` (`ApplyNormalOn.lean:412-418`) proves
  `srvRest E γr (A ++ [m]) = srvRest E γr A` through the old `srvRest_snoc`. Its three uses do
  `rw [srvRest_admin …]; iunfold srvRest; iexact HRS` (`EtcdServer__applyEntryNormal.lean:1190, 1531, 1610`).
  The auth-on arm has no `E.lg = false` fact (m5), so the unfold produces the `if`.
- **Proposed fix.** Restate `srvRest_admin` through HEAD's `srvRest_snoc` (premise
  `appliedTable_nonLease`) and `restAfter_other`. Its users then rewrite and pass `HRS` whole,
  without unfolding. List it beside m5's laws.
- **The same pattern elsewhere.** The `iunfold srvRest at HRS` before every `Apply` call
  (`:398` and the corresponding sites in the other arms) becomes `srvRestAt_open`, which gives `T`,
  the half and `srvGrantIf` for `grantPermRq` (`srvGrantIf_perm`).

### S4 (minor, §2.9's receive account): the first unfold is in `applyAll`, before `applySnapshot`

- **Evidence.**
  - §2.9 says the receive side is handled by refuting the leased arm on entry to
    `applySnapshot.wp_proof`.
  - However, `EtcdServer.applyAll.wp_proofSnap` calls `snapRecv_image` first
    (`ApplyAllSnap.lean:125`), and `snapRecv_image` unfolds `srvRest` (`SnapRecvFacts.lean:362, 387`).
  - It has `E.lg = false` from `specSnap`'s premise `γr.kv.lg = false` and `srvKVInvs`'s tie
    `γr.kv.lg = E.lg` (`InvApplier.lean:342`), and it already takes `srvKVInvs`. So the step is
    provable.
- **Proposed fix.** Add one sentence to §2.9 saying `snapRecv_image` (and `snapRecv_kv_jump`) take
  `E.lg = false` from `applyAll`'s premise, not from the refutation.

### M1 (minor, commit 4): the grant disjunct also reaches `applyEntryNormal`'s pure entry lemmas

- **Evidence.** Today `plainOrCmp_of_entryM`, `kv_certPre_M`, `cmpPermRq_of_entry` and
  `batchStep_plainM` (`EtcdServer__applyEntryNormal.lean:285-286, 389-391, 410`) take `plainOrCmp`
  from `plainEntryM … false`. Once `kvInv` is at `plainLogM γk.cmp γk.lg` (commit 4), each needs a
  grant case:
  - `certPreV` for a grant certifies the unchanged log (`chainStep_grant_logAfter`,
    `DispatchLemmas.lean`);
  - `kvEntry` of a grant leaves the log (`dispatchLog`: not a `storeKind`);
  - `hg : kind = grant → grantPropOk E.lg rq` comes from `plainEntryM`'s third disjunct and
    `srvKVInvs`'s tie.
- **Proposed fix.** List these lemmas in commit 4. In 3b they are vacuous, because `kvInv` is still
  at `false`.

### M2 (minor): apply-package files outside `apply.Link` that the server build reaches

- **Evidence.** These files are imported only from the server side, so `apply.Link` building says
  nothing about them:
  - `ApplyKVL`, `ApplyFnKVL`, `ApplyAdminL`, `ApplyFnAdminL`, `DispatchKVL`, `UberKVLBase`,
    `UberAdmLBase`;
  - `ApplyRec`, which was fixed at `4400408fad`.
- **Status.** Their statements are right as they are: `rqOk false`, no half, and the server frames
  `ltHalf`/`srvGrantIf` around them at `on = true`. But their proofs destructure
  `applierTriples` (which gained a 6th conjunct) and `leasesLive` (which gained `ltHalf`). I did not
  check that they still build. **Uncertain.**
- **Proposed fix.** Add them to 3b's list.

### M3 (minor, §2.9's text is stale against the code)

- §2.9 states `srvRest_applyG`'s premise as `plainCover rq ∨ grantPropOk E.lg rq`. It still uses
  `grantRest t rq o`/`grantIds rq o` without `v3`, and its glue names the "`o ↔`" fact of the
  internal triple.
- HEAD's `srvRest_applyG` takes instead:
  - `hrev` (not a revocation);
  - `hg : kind = grant → grantPropOk E.lg rq`;
  - `hr : restOut = restAfter`;
  - `hch : x.chain = γr.kv.ch0`;
  - `grantOutOkA` at `srvIds E T`.
- This is broader and correct: compactions are covered, which the old `plainCover` premise would
  have excluded. Rewrite §2.9 and the ids law of §2.0 to match.

### Stale (addressed at `4400408fad`)

- `apply.Apply.specRec`, the triple that `applyEntryNormal` actually calls
  (`have hA := apply.Apply.spec_rec hA0 hUb`, `EtcdServer__applyEntryNormal.lean:249`). At
  `13eaea2202` it still had `rqOk false`, had no `T`/`ltHalf`/`grantPermRq`, and its post did not
  forward (C)'s conjunct. That was the (C) pattern one level up. At `4400408fad` it carries all of
  them (`ApplyRec.lean:64-95`), including `grantOutOkA` and `grantResA`. Resolved.

## Per target

### §2.9: the gated `srvRest`, `srvGrantable`, `srvRest_applyG`, the snapshot-receive refutation

- **Good:**
  - `srvGrantable`'s placement gives the refutation directly: its `lessorModeIs … true` against
    `applySnapshot`'s `lessorRevocable = lessorModeIs … false` (`InvLessor.lean:449`), by
    `lessorPinR_agree` (`:972`).
  - `srvRestAt_open`/`srvIds`/`srvGrantIf` give the auth-on arm one generic path.
  - The (C)-based ids law is complete. I checked the `.skipped` and `.rejected` cases,
    `v3 = false`, and `rq.leaseGrant = none`.
- **Findings:** S2, S3, S4, M3.
- **Post provable?** Yes, with S2's lemmas.

### §2.13: `NewServer`

- **Good:**
  - Both halves are allocated at `[]` (`NewServer.lean:597-598`).
  - `appliedTable γr [] = kvLeases γr.kv pre` with `pre = []` (`kvLeases_pre`).
  - `restLeasesWith f [] r = r`.
  - The mode comes from `NewLessor`'s `lessorModeIs γl ρ.rd.kv.lg`.
  - `leasesNoExpiry` comes from `%Hslg`.
- **Finding:** S1. The post is not provable at `on = true` until m4 is in place.

### §2.14: `imageAt`/`mergedObs`, `mergedCreate_window`, the send branch

- **Good:**
  - `mergedObs` gated on `E.lg` (S-1) matches `srvRest`'s gate.
  - In the window, the leased arm's `restLeasesWith f T R` feeds `srvBeSnapOk_window`'s `rb`
    unchanged (`SnapSendBranch.lean:660`).
  - `bkRestAtL_of_rb` and `restLeasesWith_mem` cover `%Hmi`.
  - `(kvLeases γr.kv (pre ++ A)).ids` is `appliedTable`'s by definition.
  - The window lemma's restatement is sound.
- **Finding:** B1, about `imageAt`'s gate only.

### `entryOk`/`logShape`/`applyEntryNormal`/`applyEntries`/`apply`/`applyAll`

- **Good:**
  - `rqOk false → rqOk E.lg` carries the auth-on arm.
  - The shapes come from `kvInv` at `γk.lg` and the tie (at `on = false`).
  - `logShapeOn` is lg-free.
  - Before commit 4, `rqShape_mono` covers the gap.
- **Findings:** S2 (`apply`'s conf-change arm), S3, M1, M2.

### Commit 4 (§2.6-2.8)

- **Gates are tied correctly:**
  - `srvGrantsLeases = ρ.rd.kv.lg ∧ E.authOn = false` (`LeaseGrant.lean:43`).
  - `ρ.kv = ρ.rd.kv` (`InvRequest.lean:1049`).
  - `isServerReq` gives `E.authOn = false` (`InvProposer.lean:462`).
- **The answer reaches the proposer:**
  - `grantResA` reaches the waiter at `ar ≠ null`, which `resultIsW` already states
    (`InvRequest.lean:1267`).
  - `grantHdr` gives `srvRevLb` (`CompactMode.lean:57`: `idxCert`, `certOk`, `n < |log|`) and
    `rv ≠ 0` from `2 ≤ |log|`.
  - `authnAnsM` (`ReqOn.lean:280`) is a precedent for an owned answer (`respHdrOwn`) in the
    waiter's result.
- **Error arm:** `srvErrIs_of_applyErrIs` exists (`ServerKV.lean:71`, needs `err ≠ nil`, which the
  error arm has).
- **Finding:** M1 only.

### Commit 5's leaves

- `lessorGrantOkL_of_server`'s request split matches `LeaseGrant.spec`:
  `leaseGrantReqIs` + `leaseGrantReqIdOwn` = `leaseGrantReqOwn`
  (`InvLease.lean:72,77`, `LeaseGrant.lean:48`).
- `kv_lease_served` at `lg = true` gets `E.authOn = false` from `isServerReq`.
- No finding.

## Uncertain (not verified)

- **`lessorOk`'s `Promote` clause.** It is used on an empty entry when the member is leader
  (`EtcdServer__applyEntryNormal.lean:324, 362`). I did not re-check it at a non-empty monotone
  lessor; it is D1's, marked done.
- **`runSnapLgOkBody` (`srvGrantOpen`, `InvRun.lean:450`).** Its truth with the gated `srvRest`
  inside `applyRes` is plausible: `srvGrantable` is persistent and carried, and `∃ f` absorbs the
  TTLs. It cannot be checked here.
- **M2's files.** I did not check whether they still build.

## Ranked by need of revision

1. **§2.14 (B1).** Decide on an ungated `imageAt` (`bkRestAtL`) with a conversion lemma on the
   receive side.
2. **§2.13 and §3 (S1).** Move m4 into 3b.
3. **§2.9 and `EtcdServer.apply`'s conf-change arm (S2, S3, S4, M3).** Name the transfer lemmas
   and the generic admin law, and update the text.
4. **`applyEntryNormal` and commit 4's entry lemmas (M1, M2).** Lists only.
5. **Commit 4 (§2.6-2.8), commit 5.** As designed.

No bug in the Go code was found in this round.
