# auth-lease handoff (`etcd_authlease_safe`)

## START HERE (S4, 2026-11-16, items 5-6 done; item 7 next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (gitignored; last entries,
  "Item 5", "Item 6": the forms decided, for the checkpoint report).
- **Done:** raft L-r0..L-r6, server, drivers (`f1540674ea` .. `782fc63bd3`); merge of lean 523c2a5495 (`2835564e9d`);
  **Freeze FROZEN** (`209e3c68e6`, tag `auth-lease-s4-frozen`; texts `notes/auth-lease-s4-frozen.lean.txt`; a change
  beyond them is a thaw: STOP); **item 5** (`ef5f154062`): Freeze §1 + K1; **item 6** (this commit): §2 (Md lessor/retry/
  stub specs, `lessorRemoteAtC`, `LessorPlain.lean` for plain callers), §3 C1 (`opGrantT` lease rows), C3/D-i
  (`clientTokAt` + Lease; `newClient` proves it), D-h (registrations, `client_lease_grant_on`/`_revoke_on` in
  `ResultsOn.lean`), H1 chain (`authedFrom` + `authedFrom_ctx` in `AuthWhy`, `leaseCheckFrom_of_authedFrom` in
  `LeaseCheck`, `requireAuthInfo.specC`, server `LeaseGrant`/`LeaseRevoke.spec`, v3rpc contracts + handler specs).
  Frozen texts compared equal to the tree's (script in the item-6 entry of `questions.md`: all but `opGrantT`/
  `clientGrant`, equal in meaning). Built: every library leaf importing files changed since `ef5f154062`.
- **Next, in order (Draft §7):**
  7. read handlers (§4: `EtcdServer.LeaseTimeToLive/LeaseLeases.specN` (T1, F4), v3rpc `leaseTTLOut`/`leaseLeasesOut`,
     `etcdLeaseTTLSpecMd`/`etcdLeaseLeasesSpecMd`, `etcd_lease_read_served`; `requireAuthInfo.specC` already carries
     `authedFrom`) and the per-member law (§5, §10 S1/S4, `leaseKeptIn`, `lsHolds`, `lessorLawMask`,
     `lessor_keys_of_read`; the tie per §5.4 / R4-5: the big one, est. 4-6 days).
  8. goose `authlease`, gen-init. 9. driver (STOP: D-k's exact texts; STOP: `Main.wp_proof` proved). 10. linking, gates,
     then the land stop (merge lean first: it is 61053b1f3c or later).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build …`; affected leaves:
  `$(python3 etc/importers.py --git <base> --leaves | grep '^\(Proof\|Spec\|RaftWitness\|PorcupineDag\|Robustness\)\.')`
  (Scratch/notes targets are unknown to lake). Logs `/shared/tmp/auth-lease-s4/i{5,6}-*.log`.
- **Pitfalls:** an `iprop` hypothesis is not a Lean one (`unfold … at H` fails: state an entailment lemma, as
  `kvOpAuOn_leaseGrant`). `opGrantT`'s match does not reduce under `iexact`. `attemptPre_md` did not `iapply` in
  `LessorPlain` (unfold `attemptPre` by hand). In a `wp_apply (wp_X … (by …))` argument, a `by` naming a local can fail
  or time out: `have` first. Don't Monitor the build log for `error` (axiom lists name `errors` packages): wait on exit.
  Build logs are huge (~1M lines of `#print axioms`): grep `^error`.

# History

## Previous START HERE (S4, 2026-11-16, item 5 done; item 6 next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (gitignored; last entries).
- **Done:** raft L-r0..L-r6, server, drivers (`f1540674ea` .. `782fc63bd3`); merge of lean 523c2a5495 (`2835564e9d`);
  **Freeze FROZEN** (`209e3c68e6`, tag `auth-lease-s4-frozen`; texts `notes/auth-lease-s4-frozen.lean.txt`, hashes in
  the Freeze header; a change beyond them is a thaw: STOP); **item 5** (this commit): Freeze §1 + K1 under the old names
  (texts checked equal to the frozen ones), `client_put_on` over `gs` (at today's `clientOpAuOn`; item 6 widens it);
  forms in `questions.md` ("Item 5"). Built: every library leaf importing the changed files (`etc/importers.py --git
  c8e05b5db9 --leaves`, minus `Scratch`/`notes`): passes. Not yet run: tcb/interfaces/bounds (at the land stop).
- **Next, in order (Draft §7):**
  6. F3 lease contract (client): §2 (`lessorRemoteAtC` in `InvLease.lean`, the four `lessor.*`/`retryLeaseClient.*`
     specs at `GrpcSpecMd` + `□ ▷ attemptPre`; the `leaseClient.*` stub specs need the same Md form (a form: kVClient.Put's;
     `etcdConn_InvokeMd`, `reqPre_box`)), §3 (C1 `opGrantT` lease rows, C3/D-i `clientTokAt` + `New`'s post, D-h
     registrations), the v3rpc H1 chain (§7 Round 3/4 tables; `requireAuthInfo.specC` + `authedFrom` (`AuthWhy.lean`,
     instance) + `leaseCheckFrom_of_authedFrom` (`LeaseCheck.lean`); `EtcdServer.LeaseGrant` uses `requireAuthInfo.spec`
     on the span ctx `ctx1`: needs an `authedFrom_ctx` (as `authedOutB_ctx`, `LeaseReqOn.lean:279`)).
  7. read handlers (§4, §10 T1) and the per-member law (§5, §10 S1, `lessorLawMask`; the tie per §5.4 / R4-5).
  8. goose `authlease`, gen-init. 9. driver (STOP: D-k's exact texts; STOP: `Main.wp_proof` proved). 10. linking, gates,
     then the land stop (merge lean first: it is 61053b1f3c or later).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build …`; affected leaves:
  `$(python3 etc/importers.py --git <base> --leaves | grep '^\(Proof\|Spec\|RaftWitness\|PorcupineDag\|Robustness\)\.')`
  (Scratch/notes targets are unknown to lake). Logs `/shared/tmp/auth-lease-s4/i5-*.log`.
- **Pitfalls:** in a `wp_apply (wp_X … (by …))` argument, a `by` naming a local can fail or time out: `have` first.
  `receiptBound` is a `Nat`. Don't Monitor the build log for `error` (axiom lists name `errors` packages): wait on exit.
  `v3rpc.LeaseServer.ty` must be written `go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty` outside its namespace.
  Build logs are huge (~1M lines of `#print axioms`): grep `^error`.


## Previous START HERE (S4, 2026-11-16, Freeze FROZEN; items 5-10 next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (gitignored; last entries).
- **Done:** raft L-r0..L-r6, server, drivers (`f1540674ea` .. `782fc63bd3`); merge of lean 523c2a5495 (`2835564e9d`,
  all checks at baseline: tcb 877/4, 65 collections, interfaces, bounds 390, mode 448); Freeze rev 3 + rounds 2-4
  (`fcc8b0985e`, `c30c95e91e`); **Freeze FROZEN** (`209e3c68e6`, tag `auth-lease-s4-frozen`): the frozen texts are
  `notes/auth-lease-s4-frozen.lean.txt` with per-text hashes in the Freeze header. A change beyond them is a thaw: STOP.
- **Next, in order (Draft §7):**
  5. leased KV at auth on (client): Freeze §1 + §9 K1 (`etcdPutSpecOn`/`M`, `etcdTxnSpecOn`/`M` filters, `txnUpdAtOn`'s write
     branch, `client_put_on` over options `gs`; server side `putPermitM_of_dep`, `ServerKVOn.lean:369-397`). Files naming them:
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth/Run.lean
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth/WorkEnv.lean
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth/ClientOn.lean
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth/WorkCalls.lean
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/authN/run.lean
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth3/run.lean
    - Proof/go_etcd_io/etcd/client/v3/ResultsOn.lean
    - Proof/go_etcd_io/etcd/client/v3/Results.lean
    - Proof/go_etcd_io/etcd/client/v3/AuthnServedOn.lean
    - Proof/go_etcd_io/etcd/client/v3/LeaseGrantServed.lean
    - Proof/go_etcd_io/etcd/client/v3/KVServiceOn.lean
    - Spec/github_com/mit_pdos/etcd_grove/examples/etcd/auth/SetUp.lean
  6. F3 lease contract (client): §2, §3 (C1/C3/D-h/D-i), the v3rpc H1 chain (§7 Round 3/4 tables: `LeaseServer.{LeaseGrant,
     LeaseRevoke}.spec`, `lessorGrantOkGM`/`lessorRevokeOkM`, `EtcdServer.{LeaseGrant,LeaseRevoke}.spec`, `requireAuthInfo.specC`,
     `authedFrom` + instance + bridge in `LeaseCheck.lean`).
  7. read handlers (§4, §10 T1) and the per-member law (§5, §10 S1, `lessorLawMask`; the tie per §5.4 / R4-5).
  8. goose `authlease`, gen-init. 9. driver (STOP: D-k's exact texts; STOP: `Main.wp_proof` proved). 10. linking, gates,
     then the land stop (merge lean first: it is 61053b1f3c or later).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build …`; checks with
  `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json`; `etc/lean-check.py --max-open 2`, `--stop` before builds and at
  the end. `etc/importers.py --uses NAME FILE` to find what a changed statement breaks.
- **Pitfalls:** in a `wp_apply (wp_X … (by …))` argument, a `by` naming a local can fail or time out: `have` first.
  `receiptBound` is a `Nat`. Don't Monitor the build log for `error` (axiom lists name `errors` packages): wait on exit.
  `v3rpc.LeaseServer.ty` must be written `go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty` outside its namespace.


## Previous START HERE (S4, 2026-11-16, L1 option 1 drivers done: checkpoint)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (last entries).
- **Done:** raft L-r0..L-r6 (`f1540674ea`, `0d81d23b6f`), server (`d54c9155f6`), drivers (`a86afd08dc` + this commit):
  `kvJ`/`kvrJ`/`kdJ` with the cap; `cluster_alloc`'s `¬ clusterNoSnap` → `srvClusterBoot_alloc` → `memberBoot`/
  `memberRestartFacts`/`memberRestartBoot`; `kvCluster` gains it (kv's `KV__run`); kvreconf/kvdurable `isReplica`
  `%Hnsn`; `NewServer.spec` premise now `clusterNoSnap γ.cl → 2^48 ≤ SnapshotCatchUpEntries` (so no new
  `receiptBound` in specs: bounds at baseline), auth drivers `→ 2^48 ≤ catchUp`. Freeze §5: `Scratch/S4Freeze.lean`
  (copy `/shared/tmp/auth-lease-s4/S4Freeze.lean`) over `clusterNoSnap γr.raft.raft.cl`, checks with 0 errors.
- **Checked** (`full5.log`): full build passes; `tcb-report --check` matches the baseline (870 axioms, 4 sorries);
  all 63 collections pass; bounds 377 = baseline; mode 448 = baseline; interfaces regenerated (9 files: raft
  `InvNodeRule`, etcdstart `Alloc3`, `AllocN`, `Defs`, `Restart`, `StartMemberAuth`, `StartMembersAuth` (Proof and Spec)).
- **Next:** Freeze review rounds r2–r3, then items 5–10 (Draft §7); authlease's allocation sets the flag `true`
  (`cluster_alloc_ns`; `memberBootOn` carries no mode fact, by design).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build …`.
- **Pitfalls:** in a `wp_apply (wp_X … (by …))` argument, a `by` block naming a local can fail ("unknown free
  variable") or time out: prove it in a `have` first. `receiptBound` is a `Nat` (cast in `Int` goals: `omega`).

## Previous START HERE (S4, 2026-11-16, L1 option 1: raft + L-r5 + server committed; STOPPED at the checkpoint)

- **Branch** `auth-lease-s4` (worktree `/shared/etcd-grove-rs56`). Plan: Freeze `notes/auth-lease-s4-freeze.md` §8.4;
  GO and form decisions: `questions.md` (last entries, etcd-grove-02).
- **Done:** raft part 1 (`f1540674ea`: NsCap/storCapF, maybeSendAppend, L-r0..L-r4, L-r6, snapshotCert without the
  flag, `readySnap`'s mode conjunct); L-r5 (`0d81d23b6f`: `Bootstrap` sets `ns` via `ownRaftPhys_set_ns` from
  `⌜reNoSnap = false⌝ ∨ storCapF`, `setupNode` carries it in `InitialState`'s post, `StartNode` derives it,
  premise gone; `memStorInv_alloc`'s `sorry` takes `clusterNoSnap γ → c ≤ 1`); server (this commit):
  `compactRaftLog.spec` premise `clusterNoSnap → snapi ≤ scu`; `isServerApplyAll`'s scu row
  `clusterNoSnap → receiptBound ≤ scu` (start keeps it through the default-catch-up join; the five built hubs carry
  it on `Hscu`; `NewServer.spec` premise `clusterNoSnap γ.cl → receiptBound ≤ cfg.SnapshotCatchUpEntries'`);
  `clusterNoSnap → ai ≤ w` in `snapshotIfNeededAndCompactRaftLog.specBatch`, `applyAll.specBatch`, `applyResR`
  (run's loop; start: first start via `rnRestartOk_mode`/`isRaftNode_mode`, `srvRunRestartR`'s
  `clusterNoSnap → A₀ = []`); the snapshot job takes `¬ clusterNoSnap` from `rnApSnap` (from `readySnap`);
  restart path: `rnBootPre .restart`, `NodeStartSpecR`, `NewServer.specR`, `rnRestartOk`'s restart disjunct take
  `¬ clusterNoSnap`. Server `Link`, `Results`, `NodeApiLink`, `read.Link` build.
- **Not yet:** drivers/examples (callers of `NewServer.spec`/`specR`, `cluster_alloc*`, `StartNode`/`RestartNode`
  users outside raft, the kv examples' storage `B`), `tcb-report --check` (needs the full build), interfaces of
  other packages (`etc/api/etcdstart.txt` etc.), Freeze §5 `memberNoSnapInstall` → `⌜clusterNoSnap …⌝`.
- **Next, in order:** drivers (`etcdstart` `newServerMode`/`Restart`, cluster3, auth/auth3, k8s apimodel: flag
  `false` except authlease; discharge the scu premise from `Hrb48` and `NoSnapCatchUp = 2^48`); the kv examples
  (`KvStorage`, `KvrStorage`, `KdStorage`: their `memStorJ` copies, `storBnd` patterns gain one `-`); full build,
  `etc/tcb-report.py --check` + collections, `gen-interface --check` on every list; then §5 and items 5-10.
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build <targets>` (logs
  `/shared/tmp/auth-lease-s4/build-*.log`); `LAKE_OPTS=--packages=... etc/lean-check.py --max-open 2` only when
  imports are built, `--stop` before builds and at the end.
- **Pitfalls:** `applyResR`'s positional patterns (`stop_split`: `Hwt` is `rnWalTokA`, the `∃ w` is the next one);
  Go's default-catch-up `wp_join` leaves the else branch to close by hand; in `local macro`s with `hygiene false`,
  Iris hyps are not Lean hyps; `ApiImpl.readySnap`/`readySnap` stay defeq (`¬ … = true`).

## Previous START HERE (feasibility, superseded)


- **Branch** `auth-lease-s4` (worktree `/shared/etcd-grove-rs56`). S0–S3c on lean. Draft `notes/auth-lease-s4-draft.md`
  (statement approved). Decisions: `questions.md` (untracked), "auth-lease S4", "S4 Freeze r1 decisions", "S4 Freeze rev 2: L1 stop".
- **Done:** items 0, 2, 3 (`5baacbd07a`, `647aadf78b`, `7b126d3e4e`, `2bddb5967a`); item 4 Freeze rev 1 + r1 (`c4f188d250`),
  L1 stop (`ef4c34650e`), rev 2's texts (`5d142952af`; `Scratch/S4Freeze.lean`, copy `/shared/tmp/auth-lease-s4/S4Freeze.lean`);
  **L1 option 1 approved by the user**; its feasibility check: Freeze **§8.4** (this commit, no tree edits).
- **§8.4 in one line:** feasible, snapshot path untouched (flag `false` = today's invariant; proof bodies of the
  snapshot examples gain only a trivial `flag = false` conjunct at `Compact`/`ApplySnapshot`); estimate **11–14 days**
  (centre ~12.5, over the ~12 stop line); raft API laws L-r0..L-r6 listed there.
- **Next, in order (on the go):**
  1. raft (§8.4 table order): `NsCap`/`storCapF`; `maybeSendAppend`'s two branches; `ownRaftPhysC_sn` split; boot
     `set_ns` (revive from `ce370ad2a8^`); L-r0..L-r6; `etc/gen-interface.py etc/api/raft.txt`;
  2. server: `compactRaftLog` premise, the `ai ≤ w` clause (apply-loop specs), the `scu` row, `NewServer`, names;
  3. drivers/examples: flag `false` everywhere, authlease `true`; `etc/tcb-report.py --check` + collections;
  4. Freeze §5: `memberNoSnapInstall` → `⌜clusterNoSnap γr.raft.raft.cl⌝`; review rounds r2–r3
     (`/shared/tmp/auth-lease-s4/freeze-review-r{2,3}.md`); then items 5–10 (Draft §7).
- **Token:** `authlease-3354335` (ports 16000/17000).
- **Pitfalls:**
  - Build: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake
    --packages=/shared/tmp/manifest-e9e.json build …`. Run `etc/gates.sh` only under
    `flock /shared/tmp/etcd-grove-full-build.lock`.
  - Check: `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json etc/lean-check.py -a Scratch/S4Freeze.lean`.
  - `leaseTTLRow` needs `[go_etcd_io.etcd.server.v3.etcdserver.Assumptions]` in the section.
  - Auth-off lease users: `rw [hoff]` before `iintro`. Mode gate: no literal `true` in the new package (L3).
  - Ports 20000–21999 belong to another session.

Plan: `notes/auth-lease-scope.md` (approved; §0, §2, §5, §7). Decisions Q1–Q9: `questions.md`,
section "auth-lease". Worktree `/shared/etcd-grove-rs56`, branch `auth-lease` (off lean `89ef103d5b`,
with `auth-lease-scope` merged).

## Done

- **S0 (probe), 2026-11-14.** Unlinked, untracked: `Scratch/AuthLeaseProbe.lean` (the apply layer's lease
  check at the latest state) and `Scratch/AuthLeaseProbeModel.lean` (the mode-`on` model on the triple
  state). Both check with no `sorry`. Findings: CP0 report (below, "Pitfalls").

- **S1 (empty-user fix), 2026-11-14** (go from etcd-grove-81): `leaseCheckFrom` over `principalBound`,
  `v3rpc.leaseCheckT` over the new `v3rpc.principalBoundT` (`infoBoundTM` deleted); lemmas
  `principalBoundOn_of_ctxBound`, `principalBound_ctx` (`LeaseCheck.lean`); ledger and decisions.md entries;
  full build passes; interfaces unchanged (`gen-interface --check` on every `etc/api` list); waiting for the
  coordinator's go to run `etc/land.sh`.
- **S2 Draft** (design text): `notes/auth-lease-s2-draft.md`, reviewed in rounds (`/shared/tmp/auth-lease/`).

- S1 landed: lean `28b89b9dd6` (2026-11-14).
- **S2 (apply layer at the latest state with a lessor), proved, 2026-11-15** (Freeze approved by
  etcd-grove-81 with the five design choices): `AuthLatest` (lease vocabulary, `isAuthStoreL`'s snapshot
  clause), `AuthApplyLatestPut` (`checkLeasePuts{,Keys}.specL`, `checkPutAuth.specL`, `Put.specL`),
  `AuthApplyLatestTxn` (`txnPutsW`, `txnOutLL`, the txn checks), `AuthApplyLatestRevoke` (new:
  `revokePreW`, `LeaseRevoke.specL`), `AuthApplyLatest` (`authOutLL`, `kvPostFL` + lease class),
  `DispatchKVL` (`authKVKind`, `kvOutL`/`kvShapedL` with leases, `applierKVL`'s revocation triple,
  `dispatch.kvSpecL` widened, the revocation branch), `ApplyKVL`/`ApplyFnKVL` widened, `UberKVLBase`,
  server: `KVOutcomeOn` (`txnPutsW_plain`, `authOutL_of_kvOutL` over `plainCover`), `ApplyNormalOn`,
  `UberOn`, `UberKit` (`LeaseRevoke.specL`), `EtcdServer__applyEntryNormal`, `Results`
  (`apply_lease_revoke_latest`). Full build green; lean `dd068e790f` merged.

- S2 landed: lean `c3da59fa29` (2026-11-15).

## Next, in order

1. S3, revised (etcd-grove-81, 2026-11-15, option (a) of `/shared/tmp/auth-lease/s3-scope-gap.md`; 26–40 days after
   S3a review r1's F1 (ii), F2 (a), F3),
   in three Freeze packages:
   - **S3a** (now): the model and the apply thread: the triple state with the lease table, the client's half kept in
     `kvInvOn`, the auth-on table for `srvRest`, `authKVKind` in the three places, admission of grants, revocations and
     leased puts at the revocable mode. Design: `notes/auth-lease-s3a-draft.md` (revision 4 = the S3a Freeze package,
     three review rounds `/shared/tmp/auth-lease/s3a-review-r{1,2,3}.md`; N1 (ii′): `leaseExactL` in the class
     track's `kvPostF`); **frozen at revision 5** (etcd-grove-81, 2026-11-15, after round 4; tag
     `auth-lease-s3a-frozen`). **Probe done** (2026-11-15): `kvOwnAt` and `kvOwn ⊣⊢ ∃ L, kvOwnAt E log L` proved
     (`Scratch/S3aProbe.lean`, untracked); `applierV3backend.Put`'s proof has the live set `L` in hand and splits
     on `o.leaseID = 0 ∨ o.leaseID ∈ L` (`applierV3backend__Put.lean:97-170`), rebuilding `kvOwn` at the same `L`
     (`kvOwn_of_split`), so its `kvPostF` conjunct is local; the key-length bound is closed by §5. **Prove: started 2026-11-15, STOPPED at a finding**
     (see "S3a Prove: where it is" below). Order (Draft §8): (1) the model (`KVAuthModel.lean`: `OnState`, `kvEntryOn`/`kvRaftOfOn` on it,
     `kvGrantedL`/`leaseGrantedM`/`leaseOk` from `Scratch/AuthLeaseProbeModel.lean`, `plainEntryOn lm`/`plainReqL`/
     `txnPlainL`, `entryDetOn`/`entryShapeOn lm`, `keysNonEmpty`, `keysLeasesLive`, `KVAuthBridge.leaseOk_iff`);
     (2) `kvInvOn` + alloc, `appliedTableM`, `srvKVInvsOn`'s rows (`lm = E.lm`, `pre = []`), `appliedTableM_eq_model`;
     (3) `kvOwnAt`/`leaseExactL`/`kvPostF`'s conjunct through backend/quota/capped/corrupt/auth, `kvPostFL`, the four
     layer triples; the apply thread's model (`outcomeOn`, `kvAppliedOn`, the S2 `plainCover` lemmas restated);
     (4) the snapshot path (§5, its frozen `hnl` text); (5) `applyEntryNormal.wp_proofOn`/`apply.wp_proofOn`, the
     examples' proofs. `KVAuthModel` rebuilds ~1500 modules: full builds under the flock.
   - **S3b**: the request side (grant, revoke, leased put with auth on). **Draft** (2026-11-15):
     `notes/auth-lease-s3b-draft.md` (statements old → new, §6; decisions D1–D5, §7); probe `Scratch/S3bProbe.lean`
     (untracked; copy `/shared/tmp/auth-lease-s3b/S3bProbe.lean`, checked clean: the widened `authTie`, applied ⇒
     `kvGrantedL`, an applied put's lease live); reviews `/shared/tmp/auth-lease-s3b/review-r*.md`. No frozen text edited. **Rev 3 = the S3b Freeze package**
     (round 2: no first-tier finding); STOPPED for etcd-grove-81's decisions D1–D7 (questions.md). After the Freeze:
     the Draft's §8 order of work (est. 5–8 days).
   - **S3c**: the couplings and `NewServer`; the `lease.bootCfg` hub change and the `NewLessor` docstring (hard stops).
     **Plus (S3b decision D6, etcd-grove-81, 2026-11-15; +2–3 days):** the gRPC lease handlers' contracts at the mode
     (v3rpc `lessorGrantOkG`/`lessorRevokeOk` at `isServerReqM E.authOn` with the client's lease deposit, `KVDep.lease`/
     `LeaseDep` as S3b Draft §5 sketches; `lessor*_of_server`, `ServerLeaseGrant`/`ServerLeaseRevoke`, v3rpc `Results`'
     `lessor*_server`) and etcdstart's lease registrations at auth on (`etcdLeaseServedAt` at `etcdModelOfServer E γr
     E.authOn`), beside the couplings `etcdLeaseServedAt`'s revocable branch needs. Until then those callers stay at
     auth off (they hold `isServerReq` and pass the off permits).
   - The auth-on snapshot path carries the leases (F2 (a)); the latest track gains a lease-exact outcome (F1 (ii)).
2. S4 with the client's leased put (`WithLease`, `Put`/`Txn` with a lease) and linearizable client specs of
   `Lease.Grant`/`Revoke` (F3).

## S3a Prove: where it is (2026-11-15, after rev 6)

Rev 6 (§14) FROZEN with the stronger guard (etcd-grove-81); its frozen-text edits are made (`EtcdServer.{Put,
DeleteRange}.spec`, `txnAppliedOk`, v3rpc `putApplied`/`deleteApplied`/`txnAppliedAns`, client `KVService` rows,
`readQ_of_ansM`, `srvKVCoreM_fire` + `srvKVFacts_fire(0)`, `kvLogOkTo`). The tree does NOT build yet.

**Strategy: a transitional port first.** `srvKVInvsOn` keeps a TRANSITIONAL `γr.kv.lg = false` (beside the frozen
`lm = E.lm ∧ pre = []`); the apply and snapshot proofs take `lm = none` from it (`KVNames.lm_of_lg_false
Hrows.2.2.1`, marked "TRANSITIONAL until the §5 step") and keep their `plainCover` reasoning. Steps 3 (§3a
`leaseExactL`/`kvOwnAt`/Chain's `kvPostF`), 4 (§5, drop the transitional row) and 5 (revocable-mode apply arms) come
after the tree builds.

Checked clean with `etc/lean-check.py` (in order): KVAuthModel, KVApplyOn, KVModelM, KVReadOn, KVAuthShape, ProposeOn,
ServerOnDefs, ImageOn, ServerOn, NewServerAllocOn, AuthTie, AuthTieRead, ReqOn, ReadOn, auth/Hist, KVOutcomeOn,
ApplyEntryOn, ApplyTieOn, ApplyNormalOn, SnapRecvOn, MergedImageOn, SnapAuthRecover, AuthCompRows,
Spec/EtcdServer__applyAll, ApplyAllSnap, ModeSpecs, EtcdServer__Range, EtcdServer__apply, EtcdServer__applyEntryNormal,
StartOn, RunOn, NewServer, EtcdServer__applySnapshot (SnapApplyPost), SnapSendBranch, StopShutdown, EtcdServer__run,
ClientModel, EtcdServer__Put/DeleteRange/Txn. Edited, not yet checked: auth/MainAlloc, etcdstart/Alloc3On (alloc premises),
server Results (`server_member_alloc_on` premises), KVLogOk, client WatchFire/Results/KVService, v3rpc ServerKV, InvRead.

**Where it is (2026-11-15, session 2):** the full build is GREEN at `build9` (`/shared/tmp/auth-lease-s3a/build9.log`,
flock + 64G, commit after `auth-lease S3a §3a`); `etc/tcb-report.py --check` at 870 axioms, 4 sorries (run at `build8`,
before §3a; §3a adds no axiom). Done this session:
1. **The read rows' guard** (handoff item 1, decided by etcd-grove-81): `⌜on = true → γr.kv.lm = .none → kvLeasesOn γr.kv
   srvAuthSt0 L = []⌝` inside the `∃ L` of `rangeAnsOkM`/`txnReadAnsM` (`ServerKV.lean`), proved in `ServerKVOn` by
   `ReadOn.depQ_leases_none` (from `srvKVCoreM_leases_none`: `kv_log_plain_on` + `kvLeasesOn_none`; `iapply wp_fupd` before
   the `wp_apply` so the post can be updated). `readQ_of_ansM` (client Results) takes the guard;
   `rangeErrReply_of_errAt` became a fupd lemma over `srvKVCoreM E.authOn` (the error row `rangeErrAt` keeps its text).
   §14's table has the two rows.
2. **Client chain and examples** destructure the table (`ServerKVGet`, `ServerKVTxn`, `ClientPutGet`, `kubernetes/Defs`,
   k8s `etcd3/Compact`, `partition/WatchWrites`, `txnlin/Calls`, `auth/WorkCalls`). Pitfall: `simp only [hs, …]` on an
   Iris goal rewrites the context too: specialize `Himp $$ %hs` BEFORE the simp.
3. **§3a**: `apply.leaseExactL`, `leaseExactL_rejected`, `leaseExactL_other`, `kvOwnAt`, `kvOwn_iff_at`, `kvOwn_of_at(P)`,
   `kvOwn_atP`, `kvOwn_rejected`, `kvOwnAt_ltHalf` (Chain); `kvOwnAt_of_split`, `wSt_ne_false` (WriteLemmas). `kvPostF` and
   `kvPostFL` carry `∃ L, ⌜leaseExactL L rq log oc⌝ ∗ kvOwnAt E (oc.logAfter log) L`; the backend's Put (a dead lease's
   commit refuted by two writer halves), Txn (`txn.Txn.spec`'s `PathsLeaseOk`/rejection), DeleteRange (trivial) prove it;
   quota/capped/corrupt/auth pass it or reject (`kvOwn_rejected`); the class-track consumers (`apply/Results`,
   `uberApplier__dispatch`) forget it (`kvOwn_of_atP`). The latest track: `dispatch.kvSpecL` gains `⌜v3 = true → E.lg =
   true → leaseExactL T rq log o⌝` (from `kvOwnAt_ltHalf` at the caller's `ltHalf E T`), `uberApplier.Apply.kvSpecL`,
   `uberKVC`, `apply.Apply.kvSpecL` gain `⌜∀ o b, out = .dispatched o b → v3 = true → E.lg = true → leaseExactL T rq x.log
   o⌝`; `auth_pass_kvPostFL_nil` takes `dispatchKind rq = .leaseRevoke`. The server (`applyEntryNormal`) drops the new
   conjunct for now (`%HXo, -, #Hdel`): §6 consumes it.
4. **§4 started**: `appliedTableM`, `appliedTableM_false/true`, `appliedTableM_eq_model` in `KVModelM.lean` (checked with
   lean-check, not yet in a full build; it rebuilds ~1270 modules). **Finding:** `srvRest` (`InvRest.lean`) is imported
   by `KVAuthModel`, so it cannot read `kvLeasesOn`. Proposed form (to do): split `srvRest` into a table-generic
   `srvRestT E γr T A` in `InvRest` (`srvRest E γr A := srvRestT E γr (appliedTable γr A) A`, so the off proofs are
   untouched) and `srvRestM on E γr A := if on then srvRestT E γr (appliedTableM true γr A) A else srvRest E γr A` in a
   module after `KVModelM`; `srvRestRp`/`imageLeasesAt` and the auth-on users take `srvRestM E.authOn` (Draft §4's
   "`srvRest` and `srvRestAt`'s callers use `appliedTableM E.authOn`", in a Lean shape that fits the import order).

5. **§4's split done** (approved by etcd-grove-81 as a form, §14 row): `srvRestT`, `srvRest_eq_T` (`rfl`),
   `srvRestT_lg_false` (InvRest); `srvRestM on` (`srvRest` off, `srvRestT … (appliedTableM true γr A)` on),
   `srvRestM_false` (`rfl`), `srvRestM_lg_false`, `srvRestRpM on`, `srvRestRpM_false`, `srvRestRpM_lg_false` (ApplyRDefs);
   `imageLeasesAtT`, `imageLeasesAt_eq_T` (ImageLeases). Full build `build10` at `f0b7821df7`.

**Session 3 (2026-11-15):** the statement switch is DONE (commit after `82b6add2a9`, full build `build12`, `/shared/tmp/auth-lease-s3a/build12.log`):
- Defs: `srvRestM`/`srvRestRpM` moved to `KVModelM` (the snapshot files do not import `ApplyRDefs`); `srvRestRM on`
  (ApplyRDefs); `imageLeasesAtM on` (SnapApplyDefs); M laws in KVModelM (`srvRestT_eq_at`, `srvRestM_eq_at/_open/_close/
  _snoc`, `appliedTableM_cc`, `srvRestM_nil`, `leaseItems_of_noLease`) and ApplyRDefs (`srvRestRM_*`, `srvRestRpM_eq_at/
  _ro/_open/_close/_model`); `srvKVInvsM_rows` (ServerOnDefs).
- Statements at the mode: the five specs (applyEntryNormal, applyEntries, apply, applyAll specBatch/specSnapM,
  applySnapshot specSnapM incl. `hlease : imageLeasesAtM E.authOn` and the frozen rev-5 `hnl`), ModeSpecs.specOn, the
  run/start rows (RunOn, StartOn, AuthCompRows), `srvSnapAppliedG on`, `SnapImageFactsOn.nolease/.hlease` (rev-5 §5).
  The start rows convert at `isServerBuilt_of_gapOn` by `srvRestM_nil` (empty prefix), not transitional.
- `EtcdServer.apply.wp_proofOn` is ported to the M laws for real (no transitional step).
- **§5 started:** `keysLeasesLive_kvRaftOfOn` (KVAuthModel; needs only `LogNoLease log0`: `backendLog` enforces the
  live set, so no admission premise), with `liveSt` and its laws through `applyChange(s)`, `srvOps`, `backendLog`,
  the chain, `dispatchLog`, `kvEntry`, `kvEntryOn`; `kvInvOn_log0`, `kvInvOn_keysLive` (what the callers of
  `specSnapM` need for the new `hnl`). `keysNonEmpty`'s preservation NOT done (needs `kvShapeAll`'s put-key shape).
- TRANSITIONAL sites now (each marked "TRANSITIONAL until the §5 step"): `isServerC_restM` (AuthCompRows) used by
  applyAll's merged send; the `srvRestM_lg_false`/`srvRestRpM_lg_false` conversions in ApplyAllSnap (on branch:
  `snapRecv_imageOnR`, merged send), EtcdServer__applyEntryNormal (both on branches: `irevert HRS HΦ; simp only [hR]`),
  SnapApplyPost (`HrestM`), EtcdServer__run/StopShutdown/NewServerR (the run and stop rows at `srvRestRM K.isOn`, off by `srvRestRM_false`: not transitional), EtcdServer__applySnapshot (lg = false branch: `Hnil` derives `LogNoLease` of the auth-on
  image from `kvInvOn_log0` + `kvRaftOfOn_restorable` at lease mode none; `hleaseI` to the off table), SnapRecvOn and
  ApplyAllSnap (`SnapImageFactsOn` built from the lease-free image); plus the older ones (`grep -rn TRANSITIONAL Proof`).

**Session 4 (2026-11-15):** handoff items (a), (b) and most of (c) DONE (commits `26acfbb48f`, `1239efff42`; full
build `build13` at `1239efff42`, `/shared/tmp/auth-lease-s3a/build13.log`; see the session report):
- (a) `keysNonEmpty` preserved: `neSt`, `opKeysNE`/`opsKeysNE`, `reqKeysNE`, `entryKeysNE` and their laws through
  `applyChange(s)`, `srvOp(s)`, `backendLog`, the chain, `dispatchLog`, `kvEntry`, `kvEntryOn`, `kvRaftOfOn`;
  `reqKeysNE_of_shape` (`kvShapeAll`: a put's key is a point key of the cache's shape), `entryKeysNE_of_plain`,
  `keysNonEmpty_kvRaftOfOn` (KVAuthModel). Not yet used (§6's `kvShapedL` at a leased put takes it).
- (b) the snapshot consumers at the keys-live form: `applySnapshot_walk`'s `hnl` is "every leased key's lease is in
  `Recover`'s `Lr`" (pending items = the image's lease items, each short by `Hkey`), `snapWalkPost`'s `leaseOwn Lr`
  at the image's lease items, `snap_applyKV` at them (`leasesKnown_of_items`, SnapApplyKVLemmas), `snap_srvRest`
  at `srvRestM on` (`srvRestM_close`), `srvSnapApplied_of_walk` at `appliedTableM E.authOn` (its TRANSITIONAL
  `HrestM` gone). `EtcdServer.applySnapshot.wp_proof`'s leased branch (`E.lg = true`) now covers both auth modes:
  the mode's table (`ImageLeasesOn.lean`: `kvEntryOn_table_eq_or`, `kvRaftOfOn_table_{mem,nodup,mono}`,
  `appliedTableM_{nodup,ids_granted,mono_mem,mono_sub,rev_mem,granted_live}`, `kv_grantLog_nodup_on`), the image's
  records by `imageLeasesAtT_recs` (ImageLeases, table-generic), `hnl` from the frozen rev-5 text. The `E.lg = false`
  branch is not transitional (lease mode `none` from `E.lg = false`); its comment relabelled.
- (c) the auth-on image carries the leases (Draft §5's ImageOn/MergedImageOn/SnapSendBranch/snapRecv rows):
  `bkRestAtNAL T` (ImageOn) in `imageRestAtOn` at `kvLeasesOn γk st₀ L`; `mergedImgM`'s table `appliedTableM M.isOn`;
  `bkRestAtM_of_obs`, `mergedCreate_window`, `stop_obs` at `appliedTableM E.authOn`/`srvRestM E.authOn`;
  `merged_imageOn` builds the leased certificate (`kvLeasesOn_none` when `E.lg = false`); `snapRecv_imageOn`,
  `snapRecv_imageOnR` take `srvRestM true`/`srvRestRpM true`, no `hlg`, and give `SnapImageFactsOn` from the image's
  records (`bkRestAtNAL_other`, `restModel_bk_of_NAL`, `image_alarmNAL`, `image_membBucketsNAL`,
  `clusterImageOk_of_NAL`, `imageLeasesAtT_of_NAL`, SnapRecvOn; `nolease` from `keysLeasesLive_kvRaftOfOn`).
  TRANSITIONAL conversions removed: applyAll's merged send (`isServerC_restM` deleted), ApplyAllSnap (on receive and
  on merged send; the lessor-mode block `hEm`/`HElg`/`Hlrev` deleted: unused), SnapRecvOn, MergedImageOn,
  SnapApplyPost (`srvKVInvsM_lg` deleted).
- Left of (c), all bound to §6: the row `γr.kv.lg = false` in `srvKVInvsOn` (KVApplyOn) and its three users,
  `kv_entry_pre_on` (ApplyEntryOn:151, over `plainCover`) and `applyEntryNormal.wp_proofOn`'s two branches
  (v3 = false replay, 1293; v3 = true, 1519). Dropping the row before §6 breaks those proofs: the on branches must
  then cover the revocable mode.

Next (session 5), in order:
1. §6, pure side (KVOutcomeOn/ApplyNormalOn/ApplyEntryOn): `kvShapedL_of_log` at `plainReqL lm` with `keysNonEmpty`
   (a leased put's/txn's lease keys `reqShape k []` from `keysNonEmpty_kvRaftOfOn`); `authOutL_of_kvOutL`/
   `outcomeOn_of_kvOutL` at `plainReqL lm` with the lease verdict (`KVAuthBridge.leaseOk_iff`) and `leaseExactL T`
   at `T = (appliedTableM true γr A).ids` (`appliedTableM_eq_model`, `pre = []`); `kv_entry_pre_on` at the mode
   (`plainEntryOn γk.lm`, no `plainCover`); `kvOn_after_kv`, `authTie_of_kvOutL` likewise.
2. §6, `applyEntryNormal.wp_proofOn` v3 = true: the KV arm consumes the dropped `leaseExactL` conjunct (`%HXo, -,
   #Hdel` → keep it); new grant arm (the off arm's `srvEver_applyPre`, `kv_entry_grantFresh`, `grantReqA_of_res`,
   at the mode's table) and revocation arm (S2's `LeaseRevoke.specL`, `revokeOwn`, `ltHalf`, `revokeRestA`; the
   KV side new: the lease's keys' deletions committed, Draft §6 r2 N4); the rest at `srvRestM true` (no
   `srvRestM_lg_false`).
3. The replay branch (v3 = false): `srvRestRpM true` at the mode's table; at `v3 = false` `kvEntryOn` keeps the
   table (`dispatchTable` with `v3 = false`).
4. Drop `γr.kv.lg = false` from `srvKVInvsOn` (KVApplyOn:401) and from its provers (`NewServerAllocOn`,
   `srvClusterBootOn_alloc`); fix the destructurings of its pure row (`Hrows.2.2.1` etc. shift: grep `srvKVInvsOn` in
   ReadOn, ApplyNormalOn, KVApplyOn, ServerOnDefs (`srvKVInvsM_rows`), AuthCompRows (`isServerC_lm`), ModeSpecs,
   ApplyAllSnap (`Hcmlg`), EtcdServer__run/apply, WatchSrv, MainServe).
5. The land-stop checks (below, "Build").


**Session 5 (2026-11-15): STOPPED at a finding (ledger 2026-11-15, "the latest track's certificate premise for a
leased put or transaction").** The KV branch of Draft §6 cannot be proved for an admitted leased put or leased
transaction: the latest triples' premise `certPreVW … (kvOutL …)` becomes, through `certPreW_inner`, the class track's
`certPre` over every `backendStep` outcome, and `backendStep` admits an applied put of a lease not live (and an applied
transaction without `PathsLeaseOk`), whose log `kvNxOn` cannot certify. Options in the ledger entry ((1) the certificate
at the live set `T`, recommended as its own reviewed change; (3) narrow S3a to no leased put/transaction). Waiting for
etcd-grove-81. Done this session (pure, option-independent, checked with `etc/lean-check.py -a`, not yet in a full
build): `leaseOk_of_leasePassedL`, `not_leaseOk_of_leaseRefusedL` (the bridge; no shape needed), `kvGrantedL_of_kvOutL`
(every authKV kind), `backendTable_kv`, `chainTable_kv`, `backendLog_of_step` (a KV request's backend outcome is
`backendLog` given `plainCover ∨ leaseExactL lt.ids`), `outcomeOn_of_kvOutLL` (at `plainReqL lm`), `revokeLog_eq_backendLog`
(`liveSt` + `0 ∉ ids`), `outcomeOn_of_kvOutL_revoke` (KVOutcomeOn); `leaseShapedL_of_keysNE`, `kvShapedL_of_logL` (no
`plainCover`; ApplyNormalOn). Not blocked by the finding, next whatever the decision: the grant arm and the revocation
arm of `applyEntryNormal.wp_proofOn` (a revocation's certificate is the model's: `outcomeOn_of_kvOutL_revoke`; it needs
`liveSt` of the model's state, `liveSt_kvRaftOfOn`, and `0 ∉` the table's ids, from `appliedTableM_ids_granted`-style
facts), then the replay branch. The row `γr.kv.lg = false` stays until the KV arm covers the revocable mode.

**Session 5, continued (2026-11-15): decided by etcd-grove-81, (3) now, then (1) as stage S3a2.** Done:
- Rev 7 (Draft §15, ledger decision): `plainReqL lm := plainReq` (`plainReqL_iff`); destructurings of the old
  disjunction fixed (KVAuthModel, KVOutcomeOn, SnapRecvOn, ImageLeasesOn, SnapAuthRecover). Commit `…rev 7`.
- `kv_entry_pre_on` at the mode (no transitional step; grants/revocations are no KV kind).
- `applyEntryNormal.wp_proofOn` at `srvRestM true` throughout (no `srvRestM_lg_false`): new `RestOn.lean`
  (`appliedTableM_true_snoc/_eq/_nonLease/_nodata`, `srvRestM_keep`, `srvRestM_nodata/_admin/_applyP/_applyP0`).
  The replay branch (v3 = false) is DONE at the lease mode: plain, grant and revocation entries all by
  `Apply.spec` (`plainOrCmpG_of_entryOn`, `revokeOwn_take`), at `srvRestRpM true`. Commit `fdd1d88b44`; checked
  with `etc/lean-check.py -a` (0 errors).
- What is LEFT of the transitional row: the two `exfalso` bullets in the v3 = true data branch of `wp_proofOn`
  (marked "TRANSITIONAL until the grant arm" / "… revocation arm"), and the row itself in `srvKVInvsOn`
  (KVApplyOn) with its docstring. `grep -rn TRANSITIONAL Proof` lists exactly these.

Full build GREEN at `fdd1d88b44` (`/shared/tmp/auth-lease-s3a/build14.log`, flock + 64G).

**Next (session 6), in order:**
1. The grant arm (v3 = true), modelled on the cluster-request branch (`hA`, `Apply.spec`, auth passes a grant
   through: not `authChecks`): `applyStep_grant`, `kvEntry_grant`; the table after is `kvTable` (the model's write
   branch: a grant is no `authKVKind`, no admin), so generalize the `tail_on` macro to take the table `lt'` (it
   hardcodes `kvLeasesOn γr.kv srvAuthSt0 A`; `kvApplied_nextOn` already takes any `lt'`); certificate: the log
   kept (a `kv_certPre_keep` for a grant: `apply.chainStep_grant_logAfter`); `srvEver_applyPre` with a new
   `kv_entry_grantFresh_on` (port of `kv_entry_grantFresh` over `kvInvOn`'s `kvGrantIds`); `srvGrantIf_permPG`;
   `grantReqA_of_res`; `srvRestM_applyG` (port of `srvRest_applyG`'s `lg = true` branch at the auth-on table,
   `appliedTableM_true_snoc` + the write branch giving `dispatchTable`); the result's not-NOSPACE at the auth chain
   (`applyResultIs_notNoSpace_grant` is at `alarmChain false …`: port); `authTie_nonKV`; `grantArM_of_resW`.
2. The revocation arm (v3 = true), modelled on the KV branch (`hK`, `kvSpecL`: `authKVKind .leaseRevoke`):
   certificate from `outcomeOn_of_kvOutL_revoke` (needs `liveSt` of the model state: with rev 7 the model's log has
   no leased key, `LogNoLease`, so `liveSt` is immediate; and `0 ∉` the table's ids: a `kvRaftOfOn` port of
   `kvTableOf_ne0`); `kvShapedL_of_logL` + `keysNonEmpty_kvRaftOfOn`; `revokeOwn_take`; the post's
   `revokeIdsA`/`revokeRestA` at the model's table after (refused at the latest state: kept; applied:
   `backendTable`'s filter; port `revokeA_table`/`srvRest_applyR` to the auth-on table); `revokeArM` from
   `revokeAnsRA` (`InvRequest.lean:2031`); not-NOSPACE (`applyResultIs_notNoSpace_revoke` at the auth chain);
   `authTie` of a revocation (check `authTie`'s kind guard).
3. Drop `γr.kv.lg = false` from `srvKVInvsOn` (KVApplyOn) and its provers (`NewServerAllocOn`,
   `srvClusterBootOn_alloc`); shift the destructurings (`Hrows.2.2.1` → `Hrows.2.1` etc.: grep `srvKVInvsOn` in
   ReadOn, ApplyNormalOn, KVApplyOn, ServerOnDefs `srvKVInvsM_rows`, AuthCompRows `isServerC_lm`, ModeSpecs,
   ApplyAllSnap `Hcmlg`, EtcdServer__run/apply/applyEntryNormal (`obtain ⟨-, -, hlmE, -⟩ := Hrows`, `Hrows'.2.2.1`),
   WatchSrv, MainServe).
4. The land-stop checks (merge lean, full build under flock + 64G, tcb 870/4, gen-interface with only Alloc3On.txt,
   bounds/mode, no closed statement changed, `grep -rn TRANSITIONAL` empty, STATUS/handoff/status-history). STOP
   before `etc/land.sh`.

**Session 6 (2026-11-15): S3a's proof DONE, at the land stop.** Commits `9c2f582bd1` (the grant and revocation
arms), `b2550e6a1d` (the transitional row dropped):
1. The grant arm (v3 = true): `apply.Apply.spec` (the auth layer passes a grant through), the log kept, the table
   the model's step (`kvEntryOn_grant`: the third branch of `kvEntryOn`, `dispatchTable` at the auth-on chain);
   `srvRestT_applyG` (`srvRest_applyG` at any table), `kv_entry_grantFresh_on`, `kv_certPre_grantOn`,
   `applyResultIs_notNoSpace_grantOn` (`dispatchStep_start_grantB`). All in `RestOn.lean`.
2. The revocation arm (v3 = true): the latest-state triple `kvSpecL` (the auth layer checks a revocation);
   `revokeOn_after` (refused: the model's table kept; applied: `backendTable`); the certificate
   `kv_certPreVW_revoke_on` over `outcomeOn_of_kvOutL_revoke` (`liveSt` from `kvInvOn_log0`, `0 ∉` the table by
   `kvRaftOfOn_ne0`); `kvShapedL_revoke` from `keysNonEmpty_kvRaftOfOn`; `srvRestT_applyR` with the refusal;
   `applyResultIs_notNoSpace_revokeOn` (the auth error told apart). The table after needs the empty raft prefix
   (`srvKVInvsOn`'s `pre = []`) to be the model's state the outcome met.
3. `γr.kv.lg = false` dropped from `srvKVInvsOn`; `acModesOk` on: `cmp = false` only (`srvKVInvsC`); NewServer no
   longer proves it. `grep -rn TRANSITIONAL` is empty. The local macro `tail_on` takes the table after the entry.
4. Land-stop checks (2026-11-15): lean not moved (`c3da59fa29` merged); full build GREEN under flock + 64G
   (`/shared/tmp/auth-lease-s3a/build15.log`, 17537 jobs); `tcb-report --check` 870 axioms, 4 sorries; every
   `etc/api` list's `gen-interface --check` passes, no interface differs from lean (the Alloc3On change is a
   proof body only); bounds ok (351); mode gate: S3a's findings classified (`model`: the auth-on table's rows;
   `unmoved`: `specSnapM`'s frozen `hnl`), baselines raised (etcdserver lit-mode 156→252, match-mode 76→78,
   client/v3 lit-mode 18→22; commit `4f34346b9e`); no closed theorem statement changed (the diff in
   `Proof/github_com` is proof bodies). STOPPED before `etc/land.sh`.

**Stage S3a2 (after S3a lands; its own Scope and Freeze; 3–6 agent-days; S3b's leased put waits on it).** Leased
puts and leased transactions in the auth-on apply thread (ledger 2026-11-15, option (1)). Freeze items:
- `certPreT E c rq log T` in place of the class track's `certPre` for KV requests: the certificate of the outcomes
  that are lease-exact at the live set `T` (`apply.leaseExactL T`), with the class track's `leasesLive` at `T`
  (`kvOwnAt E log T`, split at the top layer from the two `ltHalf`s);
- the backend's `Put`/`Txn` take the certificate only when the lease is live (today `applierV3backend__Put.lean:88-95`
  takes it before the lease check);
- the latest track's `X` gains `leaseExactL T` (`certPreW_inner`, `Apply.kvSpecL`, `uberKVC`,
  `uberApplier.Apply.kvSpecL`, `dispatch.kvSpecL`: the exported `apply_*_kv_latest` change);
- `plainReqL` widened back to Draft §1's text; §6's KV arm over `outcomeOn_of_kvOutLL` (session 5's lemmas:
  `backendLog_of_step`, `kvGrantedL_of_kvOutL`, `kvShapedL_of_logL`).

**S3a2 (2026-11-15, session 7): Draft and Probe.** Draft `notes/auth-lease-s3a2-draft.md` (rev 1, commit `fd412d310d`).
Probe `Scratch/S3a2Probe.lean` (untracked, checked with `etc/lean-check.py -a`, no `sorry`): `certPreT`, `mPreAt`,
`putPre`/`txnPre` bundling `∃ T, certPreT … T ∗ mPreAt … T`, the backend `Put` with the witness taken in the live
branch (`Put_wp_T`), the backend `Txn` over a strengthened `txn.Txn.specSole` wand (`Txn_wp_T`; finding: the wand
must be told `PathsLeaseOk L`, a frozen `Spec/` text), `certPreW_innerT`, `certPreW_tie`. Review rounds:
`/shared/tmp/auth-lease-s3a2/review-r*.md` (r1–r5; r3 found `authTie` false at a leased request → Draft §4a, option (b)
probed in `Scratch/S3a2ProbeTie.lean`; r5 no first-tier finding). Draft rev 6 = the Freeze package (commit
`cb5bf97093`), STOPPED for etcd-grove-81 (`questions.md`). Probes copied to `/shared/tmp/auth-lease-s3a2/`. Next after
the Freeze: Draft §7's order (step 1 `Chain.lean`). No Lean outside `Scratch/` edited yet.

**S3a2 Prove (2026-11-15, session 8): FROZEN at Draft rev 6 (etcd-grove-81; tag `auth-lease-s3a2-frozen`), proved.**
Commits after `42827e4060` (the Freeze record): `4453757bc6` (apply layer and server lemmas), `a1dff7fc97` (the KV arm),
then the build fixes. Done, by Draft §7's steps:
1. `Chain.lean`: `leasesLiveAt`, `certPreT` (+ `_of_certPre`, `_mono`, `_auth`, `_quota`, `_capped`), `mPreAt`,
   `mPre_iff_at`, `leasesLive_iff_at`; `putPre`/`txnPre` bundle `∃ T, certPreT … T ∗ mPreAt … T`. `mPre`, `leasesLive`,
   `kvOwnAt` keep their bodies (form: equivalent, the laws relate them). WriteLemmas: `mPreRestAt`, `mPreAt_split_chain`,
   `mPreAt_of_rest`, `mPreRest_of_at`, `mPreRestAt_lend`, `mPreAt_ltHalf`, `putPre_of_mPre`, `txnPre_of_mPre`. The backend
   `Put` (witness in the live branch) and `Txn` (from the probe), quota/capped/corrupt/auth, class `dispatch`.
2. `txn.Txn.specSole`'s wand told `PathsLeaseOk`; `txn/Txn.lean` passes `⟨Hign, Hlok⟩`; `txn_runTxn` keeps its text
   (`wand_weaken_told`); `TxnSpecs.lean`, `clients-txn.md` §8 noted.
3. Latest: `putPreW`/`txnPreW` bundle `∃ T` with `leaseExactL T`; `certPreW_innerT`, `certPreW_tie`; `kvOutLT` and the four
   triples (`dispatch.kvSpecL`, `uberApplier.Apply.kvSpecL`, `uberKVC`, `Apply.kvSpecL`); the dispatch's put/txn cases split
   `mPre` at its live set and tie it to `T` (`mPreAt_ltHalf`).
4. Server: `authTie st lb rq out` at `kvGrantedL` (option (b)); `plainReqL` back to rev 5's text (rev 7's
   `plainReqL_iff` gone); `kvCover` (KVModelDefs: `plainCover` without the lease conditions) carries the Draft's
   `leasedKV`: the lemmas that read only those facts are restated over it in place; `kv_certPreW_on`/`kv_entry_pre_on`
   at `kvOutLT` (the model's table); the KV arm of `wp_proofOn` over plain and leased requests (`kvOn_after_kv` at
   `plainReqL lm` with the dispatch post's `leaseExactL`; `hne` from `keysNonEmpty_kvRaftOfOn`); the replay branch over
   `plainOrCmpG ∨ kvCover`; the four exported results restated (Draft §4's table).
Forms: `questions.md`, "S3a2 Prove". §5 (literal modes): only `srvRestM_nodata`/`srvRestM_admin` and the table-keeping
lemmas (`appliedTableM_nonLease`, `appliedTableM_nodata`) moved to either mode; etcdserver lit-mode 252 → 251 (the KV arm's
certificate at the server's live set added three); the aim of 200 is NOT reached (Left, below).
Land-stop checks (2026-11-15): lean `b7e3cf342a` not moved (merged); full build GREEN under flock + 64G
(`/shared/tmp/auth-lease-s3a2/build4.log`, 17537 jobs); `tcb-report --check`, `gen-interface --check`, bounds (351),
mode (baseline ratcheted 252 → 251): see the session report; no file under `Proof/github_com` or `interface/` changed, the
one `Spec/` change is the approved txn wand; `grep TRANSITIONAL` empty. STOPPED before `etc/land.sh`.
Next: S3b (the proposers of a leased put with auth on; `grantedAt` → `kvGrantedL` via `kvGrantedL_of_tie`-style use of
`authTie`'s converse).

## S3b Prove (2026-11-15, session 9): FROZEN at Draft rev 3 (etcd-grove-81; tag `auth-lease-s3b-frozen`)

Decisions D1–D7 (`questions.md`, "S3b Freeze"; ledger 2026-11-15, S3b entries). Done (commits after `76a28d8669`):
1. `ReqOn`: `authTie st lb lt rq out` (guard `authKVKind`, the lease-exact disjunct), `resultIsWOn`/`entryWitOn` (+ `lt`),
   `resultΨOn` (`∃ … lt`), `modelOutM true`; `grantedAt_of_dispatched`, `grantedAt_of_applied` (at `authKVKind`),
   `modelOutM_true_table`, `chainStep_applied_backend`, `leaseLive_of_tie` (D3), `txnLeaseLive_of_tie` (D7),
   `pathLeaseOk_of_plain`/`txnPathsLeaseOk_of_plain`; `grantedRes_applied`/`putQhOn_res`/`txnQhOn_res` return the model's
   table; `putPermitOn`/`txnPermitOn`/`txnPermitM` widened; `rqShape_put`/`rqShape_txnL`/`rqShape_grant`/`rqShape_revoke`;
   `reqPropOkM_true_writeL`.
2. `ProposeOn`: `grantedAt` at `kvGrantedL` (D2), `grantedAt_iff` restated, `grantedAt_kvGranted`, `grantedAt_plain`,
   `grantedAt_grant`, `writeGrantG_granted`; `reqPropOkOn`'s write form at `writePropOk lm` (`plainReqL ∨ grantPropOk ∨
   revokePropOk`), `rqShape lm`, `grantIdOwn`; `kv_prop_au_on`'s write branch (`commitOkOn_L`, `kvGrantIds_snoc`, a grant
   never refused).
3. New `LeaseReqOn.lean`: `leaseGrantPermitM`/`leaseRevokePermitM` (+ `_false`/`_true`/`_mono`), `grantQhOn`/`revokeQhOn`,
   `leaseGrantPermit_reqPropOk`/`leaseRevokePermit_reqPropOk`, `leaseGrantResM`/`leaseRevokeResM` (+ laws),
   `leaseGrantedRespAt`, `leaseGrantedResp_iff_at`, `leaseGrantResM_true_id`, `authedOutB_ctx`. `InvProposer`:
   `irrLeaseGrant`, `irrLeaseRevoke`.
4. `ApplyNormalOn`: `authTie_of_kvOutL` (+ `lt`, `hex`), `leaseExact_revoke`, `authTie_nonAuthKV`; the apply arms of
   `applyEntryNormal.wp_proofOn` (KV arm's `hex` from `HXL`, the revocation arm by `authTie_of_kvOutL`, the others
   vacuous); `processInternalRaftRequestOnce` destructures the table.
5. Specs: `Put.spec` (D3), `LeaseGrant.spec`, `LeaseRevoke.spec` (both at `isServerReqM E.authOn`, the permit, `authedOutB`,
   the result), `txnAppliedOk` (D7), `srvGrantsLeases`/`srvRevokesLeases` (auth-off conjunct dropped); proofs: `Put`, `Txn`,
   `DeleteRange`, `LeaseGrant`, `LeaseRevoke` (a mode split after `requireAuthInfo`, whose error is returned with auth on).
6. Callers: `revokeExpiredLeases` (off permit), v3rpc `ServerLeaseGrant`/`ServerLeaseRevoke` (off instance by
   `isServerReq_authOn`), `ServerKVOn` (`putPermitM_of_dep`/`txnPermitM_of_dep` left disjuncts; the extra conjuncts dropped),
   etcdstart `ServedLease`, `WorkAuth` (`grantedAt_kvGranted`). SpecPlan's `LeaseGrant`/`LeaseRevoke`/`Put` checked: an
   opaque-vocabulary statement S3b moves toward (the client's update fired at the commit); no defect found.
7. Land-stop checks (2026-11-15): lean `7d9d727fba` merged (two merges: restart3 A1 and restart3-c); full build GREEN
   under flock + 64G (`/shared/tmp/auth-lease-s3b/build4.log`, 17545 jobs); `tcb-report --check` 870 axioms, 4 sorries;
   `gen-interface --check` passes on every `etc/api` list (no `interface/` file changed); bounds ok (351); mode gate:
   the four new mode-indexed rows classified `model`, three LeaseReqOn lemmas `unmoved`, baselines raised (etcdserver
   lit-mode 251→278, match-mode 78→82: the specs' `hdrBoundM`/`pubAfterM` flags, the permits' and results' bridges,
   ReqOn's three new auth-on lemmas), for etcd-grove-81; no closed theorem statement changed (the diff under
   `Proof/github_com` is two proof bodies: `WorkAuth.lean:330`, `ServedLease.lean:263, 321`). STOPPED before
   `etc/land.sh`.

## S3c Draft (2026-11-15, session 10)

Draft `notes/auth-lease-s3c-draft.md` (rev 1, commit `64326e6fff`); probe `Scratch/S3cProbe.lean` (untracked; copy
`/shared/tmp/auth-lease-s3c/S3cProbe.lean`, clean: the guard C1, run's expiry arm, the new `bootCfg` and its laws,
`NewServer`/`NewServerR`'s guard). Reviews `/shared/tmp/auth-lease-s3c/review-r*.md`. Rev 2–4 applied rounds 1–3 (each had first-tier findings: C2→C2′, the quota wrapper's metadata spec, C5′ pair, `srvAuthAt_of_viewsM`, the registration lemma from `grpcServerAt` in client/v3, the two trusted docstrings' wording); rev 4 = commit `a5f0e9223b`; round 4 (§1–§6 clean; three first-tier in §7: `grpcUpOn`'s Lease conjunct, the exported mode corollaries, the quota server's revoke) applied as rev 5 = `9ce15e1837`. **Next: review round 5 on rev 5** (a fresh `spec-reviewer`, brief as round 4's), then the Freeze package. Session 10 stopped on context. Decisions asked: C1 (the guard
carries `on → leasesNoExpiry`; `run` has `runCfg`, not `bootCfg`), the hub change (`bootCfg`'s row, Scope text), C2
(`srvInvAt` drops `on`), C3 (`acLessor` deleted), C4 (auth-on lease registrations as an `Md` set), C5 (`…M` contracts
beside the off ones), the `NewLessor` docstring wording (§6). No Lean outside `Scratch/` edited.

## S3c Prove (2026-11-15, session 11): FROZEN at Draft rev 6 (tag `auth-lease-s3c-frozen`)

Round 5 (`/shared/tmp/auth-lease-s3c/review-r5.md`) found no first-tier problem; etcd-grove-81's conditional decisions are in
force (`questions.md`, "S3c Freeze"); ledger entry 2026-11-15 "auth on implies no lease granted". Done (commits
`334a059cef`, `e08989808d`, `28abd867e1`, after lean `2dbf6503cc` merged):
1. **Couplings (§1–§5):** C1 guard `srvGrantGuard := ⌜lg = true ∧ (on = true → leasesNoExpiry)⌝`, `srvGrantGuard_expired`
   restated, `srvGrantGuard_expired_off` new, `_false` deleted; `lease.bootCfg`'s row `on = true → m = .revocable →
   leasesNoExpiry` (hub), `bootCfg_mono` without `hon`, `bootCfg_auth` → `bootCfg_noExpiry`, `bootCfg_of_run`'s `hon`;
   `lease.srvInvAt` without `srvLessorNil` (C2′: `on` unused), `_lessorNil` laws deleted; `srvLessorNil`, `srvLessorNilM`,
   `lookupNil_of_guard`, `apply.lookupNil`, `acLessor` (C3 a) and their conjuncts deleted (apply specs, `srvUberOn`,
   `srv_uberKVL(_on)`, server `Results`' `server_uber_kvl(_on)`, `Start`/`start`/`applyAll.spec`, `isServerRunC`,
   `run_job_body`, `isServerBuilt_offC`); `revokeExpiredLeases.spec` takes `E.authOn = false`; `run`'s expiry arm from
   `srvGrantGuard_expired_off`; `NewServer`'s guard by `bootCfg_noExpiry`; the mode-allow line `::srvLessorNilM::` gone.
2. **C6:** `srvClusterBootOn_alloc` (+ `server_cluster_alloc_on`) takes `lm`/`gp`/`gps`/`hgps` (defaults), post `γk.lm = lm ∧
   γk.ids.pfx = gp ∧ γk.gps = gps`; `MainAlloc`/`Alloc3On` derive `lg = false`.
3. **§6 trusted docstrings** exactly as decided (`NewLessor.lean`, `LessorBackend.lean`); other docstrings restated.
4. **D6, server and v3rpc layer:** new `v3rpc/LeaseOn.lean` (`leaseGrantResT`/`leaseRevokeResT`, `lessorGrantOkGM`/`lessorGrantOkM`/
   `lessorRevokeOkM`/`raftLessorM`, `_false` bridges, `leaseGrantResT_true`/`leaseRevokeResT_true`, `lessorGrantOkGM_mono`);
   `lessorGrantOkLive_of_server`/`lessorRevokeOk_of_server` at `isServerReqM E.authOn` and the `…M` contract, with `_off`
   corollaries (form: the off discharges' texts kept under new names, used by `lessorGrantOkL_of_server` and v3rpc `Results`'
   unchanged `lessorGrantOkLive_server`/`lessorRevokeOk_server`); new exported `lessorGrantOkLiveM_server`, `lessorRevokeOkM_server`;
   `LeaseServer.LeaseGrant.spec`/`.LeaseRevoke.spec` at `on`, `ρ`, `Q`, the permit, the result (revoke narrowed to
   `lessorRevokeOkM`); `quotaLeaseServer.LeaseGrant.spec` metadata-indexed (`grpcHandlerOwnOkMd`, error clause);
   `quotaLease_grantHandlerOkMd_of` (plain `_of` its corollary), `quotaLease_revokeHandlerOkMd`; `srvAuthAt_of_viewsM` in
   **`ReadOn.lean`** (form: `AuthGuard.lean`, the Draft's place, is imported by `ReqOn`/`ReadOn`, a cycle); client off callers
   (`LeaseGrantServed.lean:142`, client `Results` `:3806`, `:3861`) at `on := false` with `ρ := ⟨γr.kv.st, γr⟩` (any wait name).

**Checks (2026-11-15):** full build GREEN (`/shared/tmp/auth-lease-s3c/build3.log`, flock + 64G, 17546 jobs);
`tcb-report --check` 870 axioms, 4 sorries (matches lean's baseline); bounds ok (351); mode gate: every finding classified
(the C5′ `pair` line, the client's auth-off callers as `bridge`), `gen-interface --check` passes on every `etc/api` list; baselines to raise for etcd-grove-81: v3rpc lit-mode 21→33
(the `…M` contracts' `_false`/`_true` bridges and the discharges' `hdrBoundM true` flags), client/v3 lit-mode 22→23; etcdserver
lit-mode 278→276, match-mode 82→81 (decreases); closed examples: proof bodies only (`auth/startServer`, `auth3/startMember`,
`auth/MainAlloc`, `etcdstart/{Alloc3On,Start,StartStop}`).

**Session 12 (2026-11-15): S3c's Prove finished** (lean `fa4909047e` merged, clean; commit `c15150ec34` and the
land-stop commit):
1. client/v3: `etcdLeaseGrantSpecOn`/`etcdLeaseRevokeSpecOn` and the handler lemmas `etcdLeaseGrantHandlerOkMd`/
   `etcdLeaseRevokeHandlerOkMd` in `LeaseGrantServed.lean` (form: not `KVServiceOn.lean`, which does not import the
   lease modules; the handler lemmas mode-generic, at `E.authOn`, no `hγa`: no literal mode); `etcdLeaseMethodsOn` and
   `etcd_lease_auth_served_on` in `AuthnServedOn.lean` (the Draft §7.3 statement; the lessor contracts at
   `S := etcdKVSlot s E γr`, the run slot `etcdGrpcSlot`); `etcd_leaseGrantMethodOkMd`/`etcd_leaseRevokeMethodOkMd` (client
   `Results.lean`, the plain revoke one now their corollary).
2. `Spec/…/etcdserverpb/_Lease_LeaseRevoke_Handler.lean` at the metadata form (`GrpcSpecMd`, `grpcHandlerOkMd`, `Ψe`;
   proof `wp_unaryHandlerMd`), as `LeaseGrant`'s and `Range`'s: the auth-on revoke spec reads the run's metadata (form:
   a stronger internal spec, its one caller adapted).
3. etcdstart: `grpcUpOn` gains `grpcLeaseUp s C.A regs`; `grpcUpM_true` keeps it (`leaseServerAt_revR`); the closed
   examples' destructurings (`auth/Run.lean`, `auth3/run.lean`, proof bodies).
4. r5 S5 applied (decided by etcd-grove-81): `leasesNoExpiry`'s docstring names `NewServer` and `NewServerR`.
5. Land-stop checks: see the report / STATUS entry.

**Left (after S3c):** S4 (client library, read handlers at auth on, `memberBootOn`'s `lg = false`, the closed
theorem); the cleanup stage (the C5′ pair, the literal modes).

## Pitfalls

- `kvStOn` is `@[reducible]` but `rw` does not see through it: write `kvStateOf (kvModelOn …) (kvLeasesOn …)`
  in goals that are rewritten.
- In an Iris proof, `cases hon : E.authOn` rewrites the goal but not the Iris context (an `iexact` of a hypothesis at
  `E.authOn` then fails at `false`): split with `by_cases hon : E.authOn = true` and rewrite where needed.
- `srvRestM false E γr A` is `srvRest E γr A` by `rfl` but `iexact` does not unify them (a `match` on the mode):
  `rw [srvRestM_false]` first.
- With `apply.DispatchKVL` imported, `and_false` can be ambiguous in `simp only` (`BI.and_false`): use
  `_root_.and_false`.

- The latest-state refusal must be stated in `refusedL`'s form (`leaseRefusedL`), not `¬ leasePassedL`:
  `latestOk` is vacuous at `hs = []` and in mode `any`.
- `isAuthStoreL`'s admin clause gives only the latest verdict; the lease class (`leaseKeysClass`'s
  admin disjunct) needs a recorded state: the probe adds `□ ∀ hs, L hs -∗ L hs ∗ auth.latestSnap M hs`
  (real store: `latestResC_snap`).
- The model's refusal guard `isKVKind` excludes `.leaseRevoke`: the triple-state model's guard must
  add it (`authKVKind`), or a refused revocation is applied.
- `txn.putsW`, `lease.keysOf`, `kvGrantedPerm` (Scope Draft names) do not exist; the probe defines
  `putsW` (mutual `opPuts`/`opsPuts`) and states key sets over `I.lookup ⟨k⟩ = some id`.

## Build

Targeted: `systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
<modules>`; check: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py FILE`. Full builds
under `flock /shared/tmp/etcd-grove-build.lock`. `TMPDIR=/shared/tmp`.

## Left (follow-ups)

- **The auth-on lease table's literal modes** (mode-gate raise accepted by etcd-grove-81, 2026-11-15): S3a raised the
  mode baselines (etcdserver lit-mode 156→252, match-mode 76→78, client/v3 lit-mode 18→22) with `appliedTableM true`,
  `srvRestM true`, `srvRestRM true`, `srvRestRpM true`, `kvModelM`/`kvStM` at literals; S3a2 should try to reduce the
  literal-`true` uses (state the auth-on arms' lemmas at `srvRestT` and the slot's `C.isOn`).

- **The literal-mode count is growing** (decided by etcd-grove-81, 2026-11-15: S3b's raise accepted, etcdserver lit-mode
  251→278, match-mode 78→82, the lease permits' and results' flags and bridges and three auth-on lemmas): reducing the
  literal-mode uses (below) is due before the count grows further.
- **S3a2 §5 not reached** (lit-mode 251, aim 200): the remaining literal uses are the auth-on arms of
  `applyEntryNormal.wp_proofOn`/`apply.wp_proofOn` (classified `unmoved`/`model`), `RestOn`'s lemmas true only of the
  auth-on table (`appliedTableM_true_*`, `srvRestM_keep`, `srvRestM_applyP0`/`_applyP`, which read the model's table) and
  `ReqOn`/`ReadOn`'s `…M true` rows; moving them means stating `RestOn`'s lemmas over `srvRestT` at any table with the
  entry's step as a premise (Draft §5's plan), a refactor of its own.
- **The empty-prefix fact ties the auth-on server to fresh starts** (S3a rev 5, `srvKVInvsOn`'s `γr.raft.pre = []`):
  an auth-on restart (future work) has to revisit it (the model's table folds over the applied entries, `srvRest`'s
  over the raft prefix and them).
- A revocable auth-on cluster's snapshots: carried by S3a §5 (the image's table, `keysLeasesLive`).
