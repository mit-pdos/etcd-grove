# WAL link: handoff

## START HERE (2026-11-17, after L0)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`, off `lean` `9702d5707e`; `.lake/build` from a full c6b
  build at 9702d5707e; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`. Coordinator: etcd-grove-03.
- **Decisions** (Scope §7, `questions.md`): plan approved by the user; Q1 L3 lands with L4; Q2 P2 (`--wal-dir` under
  per-member `fsExt` roots, examples' Go absolute); Q3 `NoIoErr` all inodes; Q4-Q6 as recommended (etcd-grove-03).
- **Done:** Scope + Go evidence (72997e9e36); **L0** `St/WalLinkPure.lean` (proved, no trust change): the read bridge
  `walRead_of_fold`, the eager steps `walFoldChkFrom_save_cons`/`_snoc_save`/`_snoc_snap` (`WalSaveOkC` = `WalSaveOk`
  unfolded, so the sealed `WalRecs` can import it), `walCommitLe_of_fold`, `walCommitLeFrom_snoc/_nil`, `walIdxLe_*`.
- **L1a in progress (no-twin collapses decided by etcd-grove-03, Scope §8).** Done: `PW/HandleShared.lean` (the shared
  handle `walOpenWS Sio P Mr w dir γ q`; laws `_alloc/_split/_pers/_acquire/_release/_finish/_reclaim`, `walHdl`
  + `walHdl_open/_close/_wf/_of_wf`, `ioNone`, `noErr_ioNone`); **`Sync` merged** (7eba580698; shape ACCEPTED by
  etcd-grove-03, `questions.md`); **`Save` merged** (one spec, one proof; `WAL__SaveNoErr` spec+proof deleted;
  `saveRoom` moved to `WAL__Save`'s spec, premise `walCov Sio → saveRoom … ≤ walFreshRoom`); `PW/CalleeCov.lean`:
  the callees' two specs chosen at a call by `walCov` (`saveEntry`, `saveState`, `sync`, `cut`; bridges, not
  specs, gone with the queued cleanup); `etc/link_walfs.py`: a binder's `(Sio := ioNone)` reaches the result's
  hypotheses, and a no-error spec hypothesis at `ioNone` is discharged by `noErr_ioNone` (else WalTester's
  `member.wp_save` would take the unproved `cut.specNoErr`); WalTester's `member__save` shares the handle.
  **`ReleaseLockTo`** renamed (`specNoErr` is `spec`, over `walOpenWS`; the weak form is the corollary
  `specR`/`spec_R`, which WalTester's `member__opOwnSnap` takes). **`Close`** merged: one spec over the
  handle's state (`WalCloseSt`: `shared γ` | `failed` | `opening s` | `unnamed Rp qp tf`, `HandleShared.lean`;
  pre and post a `match` on it); one proof by cases, the states' proofs its lemmas (`WAL.Close.wp_shared`,
  merged from the former `wp_proof`/`wp_proofNoErr`; `wp_failed`, `wp_opening`, `wp_unnamed`); the four
  other spec files and `WAL__CloseNoErr` deleted; users moved (`cleanupWAL`, `Open` at the P-free model
  `walPbNone`, WalTester's `member__close` (shares the handle) and `restartRead`).
- **Next, in order:** SaveSnapshot (`specPre` as a precondition
  disjunct) once the (B) blocker is decided (see Open). Then L1b, L2 (HARD STOP before `ReleaseSnapDBs`).
- **Pitfall (lock + later credit):** a method that needs the handle *before* its first resolution after `Lock`
  (Save's step bound) takes `Lock` with `+noauto`, steps the deferred `Unlock`'s resolution by hand with
  `wp_go_step_receipt'` (its `£ 1` strips the invariant's later), then `wp_raise_receipt` at the next resolution
  (`WAL__Save.lean`). Macros in proofs: `$H` in spec patterns is an antiquotation; expand by hand. A spec whose
  pre/post is a `match` on a state: `dsimp only` first in the call's side goal; a nested `isPkgInit` needs
  `iPkgInit`. Names in a binder the Link copies must resolve without `open WalFs` (`WalFs.ioNone`). A
  `lean-check` "0 errors" once hid an unknown identifier: build the Links before committing.
- **SaveSnapshot's room: (A), the user's choice 2026-11-17** ((B) closed: a covered-case error cannot lose a
  shared handle). Design (form decided by the agent, `HandleShared.lean`): `WalShN` gains `γu`; `walUsed γ u` :=
  `ghostVar γ.γu ½ u` (the client's view: bytes of room the snapshot records took since the tail was last fresh);
  `walHdl … γ` := `∃ u, ghostVar γ.γu ½ u ∗ ⌜walCov → u ≤ walSnapBudget⌝ ∗ ((⌜¬walCov⌝ ∗ walOpenWF) ∨ walOpenWFR
  (walFreshRoom - u))` (the old `walHdl` is `walHdlF`, the input of `walOpenWS_alloc`, which also returns
  `walUsed γ 0`); `walSnapBudget := 2^42`, `walSaveRoom := walFreshRoom - walSnapBudget`, `snapRoom Mr md :=
  |encSnap md| + 64`. The AUs carry the view: `SaveSnapshot`'s pre `walUsed γ u ∗ ⌜walCov → u + snapRoom ≤
  walSnapBudget⌝`, post `walUsed γ (u + snapRoom)`; `Save`'s post `walUsed γ (if hsEmptyP hs ∧ es = [] then u
  else 0)` (a writing Save ends below `2^43`: below `SegmentSizeBytes`, or a cut), its room premise `saveRoom ≤
  walSaveRoom`. Two AU transformers (method side: the handle's half and the big AU give the `walDiskAt` AU whose
  COMM returns the updated half and the budget fact; client side: the view and the fact turn a `walDiskAt` AU
  into the big one), on `TracedCap.aupd_wand_post`'s `aupd_intro` pattern.
- **SaveSnapshot's one spec:** a `match` on `WalSnapSt` (`shared γ q` | `pre …`, the former `specPre`'s binders),
  as `Close`'s `WalCloseSt`; one proof by cases (`wp_shared`: the former `wp_proof`+`wp_proofNoErr` merged as in
  `Save`; `wp_pre`: the former `specPre` proof). `WAL__SaveSnapshotNoErr` goes; `WAL__SaveSnapshotPre.lean` keeps
  `walPreIn`/`snapFrame`/`walPreSyncOk`/`sync.specPre` (untouched family).
- **Open (for L3/L5):** nothing produces `walOpenWFR` yet (Create's/ReadAll's posts give `walOpenWF`; room is an
  open layer-1 decision, `notes/wal-units/noioerr.md`): the server's shared handle needs the fresh room from
  bootstrap's slot (L3, trusted) and, in L5, from `Create` (headers < 2^43) and the restart's `ReadAll` (a tail bound).
- **Pitfalls:** WAL Go sources at the pin: `/shared/tmp/wallink/etcd` (shallow fetch of `8c28a4296`); `.lake/go-src/etcd`
  is older. `E/WalApi.lean`'s header "NOT YET IN USE" is stale (fix in L3). `WalViews.lean` is over the old `absDiskExt`.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`
  (`--stop` before builds and at the end). **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`.

## History

### START HERE (2026-11-17, Scope)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`, off `lean` `9702d5707e`; no `.lake/build` (disk);
  `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`. Coordinator: etcd-grove-03.
- **Done:** the Scope, `notes/wal-link-scope.md` (HARD STOP: Scope ready for review); Go evidence
  `examples/wallink/link_test.go` (C1-C7), all pass at the etcd pin `8c28a4296`
  (`cd examples && GOWORK=off TMPDIR=/shared/tmp systemd-run --scope -q -p MemoryMax=32G go test -race -count=1 -v ./wallink/`,
  ~95 s, most of it C1's fsyncs; last run log `/shared/tmp/wallink/test-run.txt`). No Lean changed.
- **Next, in order, once the Scope is approved:** L0 (pure read bridge, `St/WalHistLemmas.lean` neighbours) ∥ L1a
  (layer 1's shared handle, `PW/Handle.lean`) ∥ L1b (the server's `WalPbIn`/`WalMarshal`; check R5 first: are
  `hardStateAt` and raft's snapshot conf state frozen?); then L2 (`storage.toml`, `serverstorage` proofs,
  `ReleaseSnapDBs` axiom: HARD STOP), then L3 with L4 (Q1). Scope §5.
- **Open decisions (Scope §5):** Q1 land L3 with L4 (recommended); Q2 placement P2, `DedicatedWALDir` under
  per-member `fsExt` roots (recommended; changes the examples' Go); Q3 `NoIoErr` on all inodes now; Q4 the
  received snapshot's bounds from the cluster's room invariant; Q5 take `walFiles`' exclusivity and the `walSnapRec`
  witness; Q6 drop the `sized = false` law.
- **Pitfalls:** the WAL's Go sources at the pin are not in any local checkout (`.lake/go-src/etcd` is at
  `6e8f0c004c`); a shallow fetch is in `/shared/tmp/wallink/etcd` (`git fetch --depth 1 https://github.com/upamanyus/etcd 8c28a4296f…`),
  and the module cache has `server/v3@v3.0.0-20261115085855-8c28a4296f16`. `E/WalApi.lean`'s header still says
  "NOT YET IN USE" (stale since R2b-1; fix it in L3, not in a Scope commit). `WalViews.lean` is over the old
  `absDiskExt`, not `WalFs`: L0 states its lemmas over `WalHist` only.
- **Build (L1+):** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`; a `.lake/build`
  must be seeded or moved here first (the coordinator; `df -h /shared` ≥ 40 GB before any `cp -a`).
