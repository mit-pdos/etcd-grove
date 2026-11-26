# etcd_safe P5: the crash-aware stop, spec-first draft (2026-11-26)

Branch `etcd-safe-crash-p5s/2026-11-26`, from `etcd-safe-crash-s0/2026-11-26` @9e66b4dbac. Helper of the etcd_safe
lead. Draft approved by the lead (2026-11-26, shape of §2); the startable parts are done (§7). Built on B4's slot vocabulary
(`notes/etcd-dist-b4.md` §9 in the B4 worktree, not pushed yet when this was written: `srvKeepInv`, `srvKeepAt`,
`SrvKeepPh`, `srvKeepPh`, `Kb`/`Kbc`/`Xr`). Paths: `E/` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`,
`SE/` = `Spec/go_etcd_io/etcd/server/v3/etcdserver/`, `P/` = `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/`.

## 0. Summary

* **Finding (proved, commit 6de6a3d93f).** S0's `memberStop.law` is true and says nothing about the crash. `HardStop`
  only sends on `s.stop` and waits for `done` (`E/EtcdServer__HardStop.lean`). `memberStop_law_holds` is
  `HardStop.wp_proof` with the slot framed away.
* **Where the shutdown runs.** In `run`'s deferred code (`SE/EtcdServer__run.lean`'s docstring), on resources `run`
  has held since `Start`:
  * `sched.Stop`, then `s.wg.Wait`;
  * `s.r.stop()`. The raft loop's `onStop` calls `WAL.Close` and takes raft's state and records out of `rnDurInvK`
    with `rnDurK_take.law`;
  * `Cleanup()`, which ends in `backend.Close`, then bbolt's `DB.Close`;
  * `close(done)`, which announces the image.

  So the crash-aware content belongs to the spec that starts the server: `Start` → `start` → `run`, plus the two
  closes that `run`'s defer reaches.
* **Proposed statement** (§2). A crash-mode `EtcdServer.Start.specK` and `run.specK`, as instances of generalized
  specs, so that there is one proof per function:
  * the pre adds B4's slot and the run's phase half;
  * the post's stop right announces `True`, not the image (`srvStopRightG … True`);
  * `HardStop.specG` (any escrow) replaces `memberStop.law`.

  Along the way:
  * raft's records stay in `rnDurInvK` across a crash-aware `WAL.Close` (`walClose_specK`);
  * the slot's phase moves from running to `.stopped` at the backend `Close`'s commit point, through the backend
    wrapper's crash-mode `Close` (hypothesis H1, §3).
* **Gaps in what exists** (§4). The serious one is G1. B4's `specGK`/`specCK` keep "the success arm verbatim". That
  cannot hold: the server's backend must then be in crash mode, holding half of bbolt's state, because the other
  half is in `dbCrashKeep` inside `Kb`. G2–G5 are smaller.
* **Cost** (§6): about 1.1–2.2k Lean lines. They need T10's crash-mode backend, B4's §9 vocabulary in Lean, and
  hypothesis H1.

## 1. The stop path, step by step, and what each step must do to the crash keeps

| Step (Go) | Today's proof (in-process) | Crash mode needs |
|---|---|---|
| `HardStop`: send on `stop`, wait on `done` | `HardStop.wp_proof`: the escrow `srvDoneInv γ ρ id dd c` gives `srvDiskImage` | the escrow announces `True`. Nothing survives the stop in-process: R-A exits, and the image comes from the crash |
| `run`'s defer: `sched.Stop`, `wg.Wait` | `run.wp_proofG`'s stop branch | unchanged |
| `s.r.stop()` → the loop's `onStop`: `node.Stop`, `WAL.Close` | `raftNode.stop.spec`: `onStop` uses `rnDurK_take.law`, which needs `token νk.ν.stop`, and returns `raftState`, the closed WAL `rnWalClosed`, and the facts | **no take**. B4's `srvDurKeep` holds `token νk.ν.stop` in the slot, so the take is impossible by construction (D-T7-3's `rnTakenK_stop`). `WAL.Close` fires an AU on `walRecsH` inside `rnDurInvK`'s live body, unchanged (§2.3). The loop then drops its view half `rnWalViewK` and its `walOpen 1` |
| `Cleanup()` → `backend.Close` → `DB.Close` | `Cleanup.spec`, `backend.Close.spec` (full `boltState`), giving `bClosed γ.db D` | the crash-mode `Close` threads W5's AU on the record `dbCrashKeep` (H1). At its commit point the slot's phase moves `.restart true` → `.stopped`, or `.first true true true` → `.stopped`, with `Kbc` holding `fileHoldsMDur i0 D` and T10's payload (§2.5) |
| `close(done)` | escrow `srvDiskImage` | escrow `True` |

A crash at any step: the slot is valid at every step.
* Before the commit point, the phase is the running one: `Kb` with the record (C-I1's `dbCrash`), raft's records in
  `rnDurInvK` (T2's `rnDurK_crash.law`), and `walInv` (T5).
* After it, the phase is `.stopped`, with `Kbc` (`fileHoldsMDur_crash`) and everything else unchanged.

## 2. The statements (drafts; Lean text after the dependencies land)

### 2.1 `srvStopRightG`, `srvDoneInvG`, `HardStop.specG` (replaces `memberStop.law`)

In `E/InvRestart.lean`, sealed as today. A generalization: the done escrow's content `Img` becomes a parameter.

```lean
@[no_expose] def srvDoneInvG (Img : IProp GF) (c : GName) : IProp GF := inv srvDoneN (Img ∨ token c)
@[no_expose] def srvStopRightG (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (dd : GoString) (Img : IProp GF) :
    IProp GF :=
  iprop(∃ (stc dnc : Loc) (γst γd : ChanNames) (c : GName),
    srvStopAddr s ↦□ stc ∗ isChanBag γst stc (V := Unit) (fun _ => srvStopReq s E ρ dd) ∗
    srvDoneAddr s ↦□ dnc ∗ ownBroadcastChan dnc γd (srvDoneInvG Img c) .Unknown ∗
    token c ∗ srvCfgFieldAddr s go!"DataDir" ↦□ dd)
-- today's names, by definition (no statement changes):
srvDoneInv γ ρ id dd c := srvDoneInvG (srvDiskImage γ ρ id dd) c
srvStopRight s E γ ρ id dd := srvStopRightG s E ρ dd (srvDiskImage γ ρ id dd)
```

```lean
/-- `HardStop` with any escrow (today's proof, which never looks inside the escrow). -/
abbrev EtcdServer.HardStop.specG : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (dd : GoString) (Img : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvStopRightG s E ρ dd Img ∗ srvStopReq s E ρ dd }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"HardStop")) (Val #()))
  {{ RET #(); ▷ Img }}
```

`HardStop.spec` becomes an instance, with its statement unchanged. The crash proof (P4) uses `specG` at
`Img := True`. **Retires** `memberStop.law` and `memberStop_law_holds` (P/crash/MemberBoot.lean) once P4 switches.
Nothing else uses them.

### 2.2 `EtcdServer.Start.specK` (the statement that carries the crash-aware stop)

`Start.spec`'s text (`SE/EtcdServer__Start.lean`) with three changes:

```lean
-- binders gain
(L : GooseLocalGS GF) (γph : GName) (ph : SrvKeepPh) (Kb Kbc Xr : SrvKN GF → IProp GF) (γd : GName)
-- pre: `isServerBuiltC …` at the crash-mode backend (G1: T10's mode, which `NewServer.specGK/specCK` must give),
-- and
"#Hkeep" ∷ srvKeepInv γrn γn.id dd γd Kb Kbc Xr γph L ∗ "Hph" ∷ srvKeepPh γph (1/2) ph ∗
"%Hph"   ∷ ⌜ph = .first true true true ∨ ph = .restart true⌝ ∗
"#Hkbc"  ∷ kbClose.law Kb Kbc ∗            -- T10's step (§2.5), or a premise of the spec's proof
-- post: the right to stop, at the escrow `True`
∃ dd : GoString, srvStopRightG s E ρ dd iprop(True)
```

Read: a server started from B4's slot in a running phase can be stopped, and the slot stays valid at every step of
the stop. The slot's invariance is automatic for an `inv`. What makes the statement non-trivial is that the
resources it is given are the crash-mode ones:
* raft's stop token is in the slot, so no take is possible;
* the backend holds only half of bbolt's state, the other half being in `Kb`'s record.

So the proof cannot close the backend without moving the slot.

### 2.3 Raft: `walClose_specK` and the loop's keep-mode stop

**`walClose_specK`.** A new conjunct of the WAL contract `isWalStorage` (`E/WalApi.lean`, untrusted: proved by
`rnNewStorageOk_holds`). It follows `Release`'s AU pattern:

```lean
□ ∀ (id cid : w64) (Q : IProp GF),
  {{ storage.walOpen h 1 ∗ walMetaIs h id cid ∗ walPurgeRight h ∗
      AU <{ ∃∃ (σ : StorContents) (Hs : WalHist) (sz : Bool), walRecsH h σ Hs sz }> @ WalFs.walAuMask, ∅
        <{ walRecsH h σ Hs sz, COMM Q }> }}
    (App (Val #(methods si.ty go!"Close" si.v)) (Val #()))
  {{ (err : GoInterface), RET #err; Q ∗ WalFs.walUnlockedTok ∗ Fs.osCallPerm (Fs.callKey h.R h.dir) (1 : Qp).half }}
```

It is proved from `WAL.Close.spec`'s `shared` arm, whose AU is already over `walDiskAtI` with the state unchanged
(`Spec/.../storage/wal/WAL__Close.lean:76`). `walRecsH`'s `walDiskAtI` is that state. Error arm: the WAL proof's
`walCov Sio → err = nil` gives `nil` under the server's file semantics, as `walClose_spec` does today.

**The loop.** `raftNode.stop.specK`: `raftNode.stop.spec`'s pre at the wrapper's keep mode, with post
`∃ x, nodeVacantA γ.node.cl γ.id x`. No `raftState`, no `rnWalClosed`. Its proof is the loop's `onStop` in keep
mode: `node.Stop`, then `walClose_specK` with the AU opened on `rnDurInvK`'s live body, with no `rnDurK_take`. Then
`rnStopImageK γ := ∃ x, nodeVacantA …` goes into `done`'s escrow `rnDoneEscK`. The mode is fixed when the loop
starts (G2).

### 2.4 `Cleanup.specK` and the backend's `Close` (H1, the hypothesis)

**H1, the backend wrapper's crash-mode `Close`.** The bbolt-crash lead's, not yet written. Named hypothesis
`backend.Close.specC`, stated as `backend.backend.Close.spec` with W5's `DB.Close.specC` threaded through:

```lean
abbrev backend.backend.Close.specC : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (X Y : IProp GF) (i0 : Fs.Ino)
    (Q : Data → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackendK γ P W Pk b ∗ isStopChans γ P W Pk b ∗ bOpen γ 1 ∗ X ∗ commitReq γ P Pk b X Y ∗
      -- (W5) the record, kept by the caller's invariant (T10's `Kb`), reached by the update
      AU <{ ∃∃ (Dl Dn : Data), dbCrashKeep γ.db i0 Dl Dn }> @ ⊤ \ ↑(bbolt.crashN γ.db.ns), ∅
        <{ fileHoldsMDur i0 Dn, COMM Q Dn }> }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err;
      Y ∗ ∃ D : Data, bStopView γ P W Pk D ∗ ((⌜err = GoInterface.nil⌝ ∗ Q D) ∨ ⌜¬ dbCloseOk⌝) }}
```

* `isBackendK` is the backend in crash mode (T10/bbolt-crash): its stop escrow holds `boltState ½`, not `1`.
* W5's `⌜Dn = D⌝` becomes the backend's `D` named by `Q`'s argument.
* The mask is W5's `⊤ \ ↑γ.ns`, at the backend's `DBNames`.
* **Nothing is derived on the error path.** On `¬ dbCloseOk` the update may not have fired, and the record stays in
  `Kb`, as W5 says.

**`Cleanup.specK`.** `Cleanup.spec` with the same AU and `i0` added to the pre, and the post's
`backend.bClosed d.γB.db D ∨ …` replaced by `Q D ∨ ⌜¬ dbCloseOk⌝`. The proof is today's, with `backend.Close.specC`
in place of `backend.Close.spec`. `Cleanup` adds no other step on the file.

### 2.5 The slot's move at the commit point: `kbClose.law` (T10's, with B4's vocabulary)

```lean
/-- At the crash-mode `Close`'s commit point: the slot at a running phase, with the run's phase half, gives the
update's frame. The record goes out of `Kb`, its file comes back durable, and the slot moves to `.stopped`
with `Kbc` at the closed data. -/
abbrev kbClose.law (Kb Kbc : SrvKN GF → IProp GF) : Prop :=
  ∀ γ id dd γd Xr γph L ph (i0 : Fs.Ino) (γb : DBNames), ph = .first true true true ∨ ph = .restart true →
    ⊢ srvKeepInv γ id dd γd Kb Kbc Xr γph L -∗ srvKeepPh γph (1/2) ph -∗ kbCloseTok … -∗
      AU <{ ∃∃ (Dl Dn : Data), dbCrashKeep γb i0 Dl Dn }> @ ⊤ \ ↑(bbolt.crashN γb.ns), ∅
        <{ fileHoldsMDur i0 Dn, COMM srvKeepPh γph (1/2) .stopped }>
```

The update is built from `Kb`'s invariant (T10: the record and the payload, or a closed mark the token `kbCloseTok`
leaves) and the slot. Its body is T10's: what `Kb` and `Kbc` are. The slot's part is one step of B4's phase
variable.

**For a first generation** (`.first true true true` → `.stopped`), `.stopped` needs two things `.first` lacks:
* `Xr k` (`memberRestartFacts`);
* the spine `osSpineDur k.jd …`.

This is G3.

### 2.6 `run.specK`, `start.specK`

These are `run.spec`'s and `start.spec`'s texts with §2.2's changes:
* `isServerRunC` at the crash-mode backend and the raft wrapper in keep mode;
* the slot and phase half carried down to `Cleanup.specK`'s AU, built by `kbClose.law`;
* `done`'s escrow `srvDoneInvG True c`.

One proof per function: `run.wp_proofG` gains the stop mode as a parameter, a record holding:
* the done escrow;
* the raft wrapper's stop mode;
* the backend close's AU provider.

Its two instances are today's `spec` (the image: `stop_split`, `stop_cleanup_image`, `StopImage`) and `specK`
(no image). `StopShutdown`/`StopImage`/`StopCensus` are untouched. They are the image instance's.

## 3. Hypotheses of the proof plan (named laws, each matching a planned proof)

| Name | Statement | Discharged by |
|---|---|---|
| H1 `backend.backend.Close.specC` | §2.4 | the bbolt-crash lead's backend wrapper over W5's `DB.Close.specC` (`origin/bbolt-crash-w5/2026-11-26` @ff0e39fdaa, `Spec/go_etcd_io/bbolt/DB__Close.lean:69`) |
| H2 `kbClose.law` | §2.5 | T10's `Kb`/`Kbc` definitions plus B4's phase step (no trust) |

No other hypothesis. `walClose_specK` is proved here, from the proved `WAL.Close.spec`. T2's laws are used as they
are, minus `rnDurK_take`.

## 4. Gaps in what exists (for the lead)

* **G1 (B4 §3.1/§3.2, serious).** `NewServer.specGK`/`specCK`'s success arm is "otherwise `specG`'s verbatim".
  That bundle, through `srvStop.keep` and `isServerBuiltC`, holds the backend in in-process mode, with bbolt's
  whole `boltState` in the backend's stop escrow (`backend.Close.spec` takes it). Meanwhile `Kb` in the slot holds
  `dbCrashKeep`, which holds `dbHalf γ Dn`. The halves add up to more than one, so the post is unsatisfiable, or
  `Kb` cannot be built. So `specGK`/`specCK`'s success arm, `Start.specK`, `run.specK` and every spec on the apply
  path that reaches the backend's commit must be at T10's crash-mode backend. This is cheap only if T10 makes the
  backend's commit invariant generic in its client payload, so that the existing specs are instances
  (BackendImage.lean's `kbStep.law`/`kbSync.law` point that way). Otherwise it is a re-proof of the apply path.
  **Needs a T10 decision before §2.2 can be written in Lean.**
* **G2 (B4 §4's `newRaftNode` row).** The loop's stop mode, take or keep, must be fixed when the loop starts:
  `newRaftNode`'s and `raftNode.start`'s specs, which B4 already restates. The crash mode's loop does not get
  `token νk.ν.stop`, because it is in the slot. B4's restated `newRaftNode` should carry the mode, and the keep
  mode's escrow `rnDoneEscK`.
* **G3 (B4 §9, `.first` → `.stopped`).** `.stopped` needs `Xr k` = `memberRestartFacts k.γ k.ρo id` and the spine.
  B4 says the stop has them through `srvStopReq`'s boot evidence and the persistent spine:
  * `srvBootApplied ρ` does not obviously give `memberRestartFacts` (which T7 builds at boot);
  * B4 left the spine out of `.first`.

  Recommendation: add both to `.first _ _ true`, since bootstrap's `TouchDirAll`s make the spine before the backend
  opens, and `memberRestartFacts` are pure or persistent facts of the names at boot. Alternatively, add a
  `.firstStopped` phase whose crash target is `memberGen` (D-B4-2's).
* **G4 (T5).** After `WAL.Close` the WAL's `walInv` is in its parked state. That state must be covered by
  `walInv_crash` and by `walRecsH_crash` at `rnDurK_crash.law`. It is presumably covered, since boot holds the
  parked state, but this is to be checked, not assumed.
* **G5 (the error paths).** The backend's `¬ dbCloseOk` arm leaves the phase running with the record in `Kb`,
  consistent with W5. `walClose_specK` has no error arm under the server's file semantics (`walCov`). Neither needs
  a premise.

## 5. Clean end state

When this lands:
* `memberStop.law` and `memberStop_law_holds` are deleted. P4 uses `HardStop.specG` at `True`.
* `memberKeepRc` is deleted (B4: `.stopped`).
* S0's `memberKeepS`/`memberKeepInv` are B4's restatements.
* Today's `Start.spec`, `run.spec`, `start.spec`, `Cleanup.spec`, `raftNode.stop.spec` and `HardStop.spec` stay, as
  instances of the generalized specs, for the no-crash line and the single-process results, with their statements
  unchanged.
* Every spec here is of a translated, proved function, so none is trusted. Only H1 is open, and it is a planned
  proof.

## 6. Proof plan and cost

| Piece | Lean lines | Depends on |
|---|---|---|
| `srvDoneInvG`/`srvStopRightG`, `HardStop.specG`, `spec` as an instance | 50–100 | nothing |
| `walClose_specK` (contract conjunct, `rnNewStorageOk_holds` extended) | 100–200 | nothing |
| raft loop keep mode: `onStop`'s branch, `rnDoneEscK`, `raftNode.stop.specK` | 300–600 | G2 (B4's `newRaftNode`) |
| `Cleanup.specK` (today's proof over H1) | 150–300 | H1's text agreed |
| `run.wp_proofG` over the stop mode; `spec`/`specK` instances | 300–600 | G1 (T10), the two above |
| `start`/`Start.specK` plumbing (escrow, slot, phase) | 100–200 | B4 §9 in Lean |
| `kbClose.law`'s proof | 50–150 | T10's `Kb`/`Kbc`, G3 |
| **Total** | **1.05–2.15k** | |

Order:
1. The first two rows can start now, independent of the rest.
2. Then the raft keep mode, once B4 fixes `newRaftNode`'s restatement.
3. Then `Cleanup.specK` over H1.
4. `run`/`Start` last, after T10's G1 decision.

## 7. Progress (2026-11-26, after the lead's approval)

Approved: §2's shape. G1 is with T10 (kaashoek); G2/G3 go into B4's draft after its review; H1/H2 stay named
hypotheses. Done on this branch (proof-only, no Spec/ change):

* **§2.1.** `srvDoneInvG`, `srvStopRightG` (sealed), `srvDoneInv_eq_G`, `srvStopRight_eq_G` and
  `EtcdServer.HardStop.specG` are in `E/InvRestart.lean`. `EtcdServer.HardStop.wp_proofG` proves `specG`, and
  `HardStop.wp_proof` now follows from it (`E/EtcdServer__HardStop.lean`), with `HardStop.spec` unchanged.
  `memberStop.law`, `memberStop_law_holds` and `hardStop_frame` are deleted from `P/crash/MemberBoot.lean`.
  `member_crash_boot`'s `hstop` is now `∀ L, EtcdServer.HardStop.specG` at the generation's heap
  (`P/crash/MemberCrashBoot.lean`).
* **§2.3, the WAL half.** `isWalStorage` has a sixth conjunct, the crash-aware `Close`, with an identity update over
  `walRecsH` and post `⌜err = nil⌝ ∗ Q`. Pieces:
  * `walCloseK_spec` (`E/WalApi.lean`);
  * `walCloseK_law`, proved from `storage.Close.spec` through `walRecsH_closeAU` (`storage/WalRecsH.lean`);
  * a new `isWalStorage_intro` hypothesis, `hCloseK`;
  * `rnNewStorageOk_holds` extended (`E/RnNewStorage.lean`).

  The unlocked token and the directory's call permission, which `Close` also returns, are dropped from the post:
  under R-A nothing reopens the WAL in the same process.
* **G4: checked, covered.** `walInv_crash` (`storage/wal/Crash.lean:257`) takes only the invariant, `crashed`,
  `walCrashTok`, `osSharedInv` and the crash rest. It opens `walInv` in whatever state it is, parked included
  (`walParked`, :295), and constrains no state. `rnDurK_crash.law` reads `walRecsH` from `rnDurInvK`'s live body,
  where `walCloseK` leaves it. So a crash after the crash-aware `Close` is covered by the proved laws as they are.

**Integration note (the lead, 2026-11-26).** `etcd-safe-p5r` (P5 (b) steps 2–5, merged into kaashoek's
`etcd-safe-t10b/2026-11-26` @16f728437b) deletes `walRecsH`: `rnDurInvK`'s body holds `walHistH h Hs true` plus
`HistReadsK`. There, the contract's `Release` takes `AU <{ ∃∃ (Hs : WalHist) (s : Bool), walHistH h Hs s }>`, with
`walHistH_releaseAU`. `walCloseK` as written here, an identity AU over `walRecsH` through `walRecsH_closeAU`, will
conflict when this branch meets t10b. The fix is to restate it over `walHistH` with t10b's `Release` binders, through
a `walHistH_closeAU` beside `walHistH_saveAU`/`walHistH_releaseAU` (`walHistH` is `walRecsH` without the fold row,
so the proof carries over). Do not merge t10b until it settles.
**Done** (after the gates at 3a301609d6): `walCloseK` is now stated over `walHistH` with `Release`'s binders
(t10b's), through `walHistH_closeAU` (`storage/WalRecsH.lean`, beside `walHistH_saveSnapAU`); `walRecsH_closeAU` is
gone. On this branch `rnDurInvK`'s body still holds `walRecsH`, and a caller converts with `walRecsH_iff_hist`;
on t10b the body's `walHistH` is the update's object directly.
