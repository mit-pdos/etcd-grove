# etcd_safe B4: a crash-aware keep slot in `NewServer`'s specs (design, 2026-11-26)

Branch `etcd-safe-crash-b4/2026-11-26`, from `etcd-safe-crash-s0/2026-11-26` @9e66b4dbac. Helper of the
etcd_safe lead. **Design only: no Lean edit for B4.** The design changes S0 statements and needs trusted
changes besides `NewServer_dist`'s text, so it went to the lead before any re-proof (§7). The decisions taken
are in §7a. The re-proof waits on T10, T6 and kaashoek's case (D-B4-7); §8 is the handoff, §9 the layering.
**Revision 1** (branch `etcd-safe-crash-b4r/2026-11-26`, at the end of this note) applies review D5, withdraws
D-B4-6, and revises §9. Where it differs from §2–§9, Revision 1 wins. Paths: `P/` = `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/`,
`S/` = `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/`, `E/` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`.

## 0. Summary

* **What a crash inside the call leaves.** With the fork's torn-`Save` fix (`DiscardUnsaved`, C-I3), a WAL
  holding no `Save` is discarded at the next start. No `Save` happens inside `NewServer`: raft's first `Save` is
  in the raft loop, which `Start` runs. So a crash anywhere inside a **first** `NewServer` leaves a first start
  again, and this stays true until the first durable `Save`, after the call has returned. A crash inside a
  **restart's** `NewServer` leaves a restart. That restart may start from a changed image: the WAL's tail cut
  or an unsaved WAL discarded, `<k>.snap.db` renamed onto `db`, and the backend committed.
* **What the slot holds** (§2). Only two kinds of things, and never the running code's exclusive state:
  1. the cluster's ghost rows a crash must hand back and the next generation cannot allocate again: `raftState`
     at `init`, the armed vacancy's crash token, and the snapshot directory's map at `∅`. Each stays in the slot
     only until it moves into a per-generation crash invariant;
  2. per-generation crash invariants, each with its crash token: the WAL area's `walInv`, raft's `rnDurInvK`,
     the snapshot directory's `snapDirKeep`, the backend's crash invariant (T10's `KeepB`), and the durable
     spine's persistent facts.

  Every running step reaches its state through those invariants, not through the slot. That keeps the
  serving axioms free of the slot.
* **Precedent used.** kvnet's `kvGen_boot` (KvRaft/.../kvraft/TopBoot.lean:177) allocates the file
  invariant, which holds `raftState`, before `StartNode`, and `StartNode` reads `raftState` through an atomic
  update. etcd's raft has the same interface:
  * `StartNode.spec` takes `raftState` by an AU (Spec/go_etcd_io/raft/v3/StartNode.lean:83);
  * `RestartNode.spec` says it is made for a client keeping `raftState` in a crash invariant
    (RestartNode.lean:42, :116-123);
  * `rnDurK_alloc.law` (E/InvWalCrash.lean:331) needs only `raftState` and the WAL's records.

  So `rnDurInvK` can be allocated before the node is started. A first start allocates it at `newRaftNode`'s
  entry. A restart allocates it at the generation's boot (P3).
* **S0 statements this changes** (§6): `memberGen_boot.law`'s output; `memberKeepS`'s abstract `KeepF`/`KeepB`,
  which a spec that updates the slot must fix; `memberFirstCrash.law`'s target (`memberFirst` →
  `memberGen`), which lives in MemberCrash.lean (kaashoek's file); and the layering, because the in-process
  specs cannot import `memberKeepInv`.
* **Trusted changes besides `NewServer_dist`** (§5): `NewServerC_dist`, a draft the brief allows; the
  bootstrap contract, either `bootstrap.wp_proof_dist` (approved) or C-I2/C-I3 (laws now, axioms later),
  depending on decision D-B4-5; possibly `bootOk`'s or `storage.OpenBackend`'s post, for T10's backend
  invariant at creation. `Serve_dist`/`Serve_distR` need no change if D-B4-1 and D-B4-2 are taken.
* **Cost of the in-process re-proof** (§4): about 2.5–4.5k Lean lines. It depends on T10 (the backend's
  crash invariant), T6 (`snapDirKeep` at a first start) and kaashoek's open `sorry` in `NewServer.wp_proofC`.
  `specG` itself can stay and be derived from the new `specGK` by allocating a slot and dropping it, as
  `wp_proofG` is derived from `wp_proofGAt`. So the no-crash line's callers do not move.

## 1. The steps of `NewServer` that matter for a crash

All references are to Go `server/etcdserver/bootstrap.go` and `server.go` at the pin. The fork changes only
the WAL.

| # | Step | What happens on disk or in ghost state | Crash at or after it leaves |
|---|---|---|---|
| 1 | `TouchDirAll(DataDir)`, `TouchDirAll(MemberDir)` (:64, :68) | directories, synced parents | first start / the same image |
| 2 | `bootstrapSnapshot` (:213): `TouchDirAll(SnapDir)`, three `RemoveMatchFile`s | the snapshot directory; `tmp*`, `db.tmp*` and `*.snap` deleted | the same |
| 3 | `bootstrapBackend` → `OpenBackend` (:255) | bbolt `Open`: creates or opens `member/snap/db`; on a restart, `<k>.snap.db` may be renamed onto `db` first; the backend's commit goroutine starts | first start (C-I3's leftovers; **bbolt's init window panics the next start**: `issues/bbolt-init-not-crash-safe.md`, blocks-proof) / the restart's image with the backend's new commits |
| 4 | restart: `bootstrapWALFromSnapshot` (`wal.Open`, `ReadAll`) | the fork: a torn tail cut, unsaved WALs discarded (`DiscardUnsaved`) | restart, or first start when every WAL was unsaved |
| 5 | first start: `bootstrapNewWAL` → `wal.Create` (:710) | `.tmp` dir, rename, parent fsync | first start, because the fork discards a WAL with no `Save` |
| 6 | `cluster.Finalize`, `bootstrapRaft` | backend writes (membership) | as row 3 |
| 7 | `newRaftNode` → `StartNode`/`RestartNode` | the node goroutine; the vacancy armed; `raftState` read by AU; **no `Save`** | as before |
| 8 | lessor (`Hlslot`), mvcc, auth store (`Hγa`), transport, ... | ghost state only, plus backend commits | as before |
| — | (after the call) `Start` → the raft loop's first `Save` | the WAL holds a `Save` | restart |

## 2. What goes in the slot, and when each piece enters or leaves

The slot is S0's `memberKeepInv C cfg id KeepF KeepB KeepBc L` (P/crash/MemberBoot.lean:160), an invariant at
`memberKeepN` holding `memberKeepS`. A ghost phase variable is added: half in the slot, half with the caller.
It tells the call which disjunct currently holds, which the invariant alone cannot say.

**A first generation** (`specG`'s case; memberKeep's `KeepF L` disjunct throughout, decision D-B4-2):

| Piece | Enters the slot | Leaves the slot | Why it survives a real crash |
|---|---|---|---|
| `memberWalKeep h` (`walInv` + `walCrashTok` + `osSharedInv`) | at the generation's boot (P3), from `wal.bootRes`'s boot (`Boot0.lean`'s `walInv_alloc`, which already runs before the program) | never | T5's `walInv_crash` is proved against the file extension's crash (`OsCrash`): the next generation gets exactly the WAL files the crashed tree holds |
| `raftState γ.cl id RaftState.init` | P3 (out of `memberFirst`'s slice) | at `newRaftNode`'s entry, into `rnDurInvK` (`rnDurK_alloc.law`), in the same ghost step | before `newRaftNode` no node of `id` exists, so nothing has changed raft's durable state. `StartNode`'s AU only reads it (its post has `S` unchanged) |
| `nodeCrashTok γ.cl id x` | P3 arms the vacancy (`nodeVacant_arm`); the call gets `nodeVacantA` | never | raft's `nodeCrash` (InvNodeRule.lean:745): whatever the node held, a crash gives the vacancy back |
| `memberDurKeep` (`rnDurInvK` + `token νk.tk` + `nodeCrashTok` + `token νk.ν.stop`) | at `newRaftNode`'s entry (replacing the two rows above) | never | T2's `rnDurK_crash.law`: the state the WAL prefix a crash reads holds; with no `Save`, `init` and the vacancy |
| `ghostMapAuth γd 1 ∅` (snapshot map) | P3 | at `snapDir_init` (inside `NewServer`), into `snapDirKeep` with its token | no snapshot is saved before the raft loop runs, so the map is `∅` in either form |
| `memberSnapKeep` (`snapDirKeep` + token) | at `snapDir_init` | never | T6's `snapDir_crash.law` (proved over `OsCrash`); **needed:** a first-start form returning the map at `∅` (T6) |
| `osSpineDur jd [member, snap] J` (persistent) | after rows 1–2's `TouchDirAll`s (`osPathDur_child`) | never | the parent fsync commits the names (F-N2, `fileutil.go:49-85`) and the claims are discarded, so Go never writes those names again |
| T10's backend crash invariant + token (`KeepB`, holding `dbCrashKeep`) | once `NewServer` holds the backend's write transaction (`dbCrashKeep_new`, C-I1) | never; the stop moves it to `KeepBc` (P5) | C-I1 (interim axioms, reviewed): the backend file after a crash holds `Dl` or `Dn`. In a first generation, a crash before the first `Save` ignores the record: the next start is a first one over C-I3's leftovers |

The rows `memberFirst` needs that are **not** in the slot, and how B4 gets them back after a crash:
* `nodeBoot`: persistent.
* the fresh names (`Hkvs`, `Hcok`, `Hrev`, `Hrd`, the registry): allocated again.
* `idShare`/`idWaitTok`: from the issue record's crash rest (B6 (b), `idPfxInv_crash`).
* the lessor slot `Hlslot` at the start's `γl`: **cannot** be handed back; it is consumed by `NewLessor` and
  `γl` is fixed by the view. (Revision 1, F-A6) The boot's first-start arm allocates a fresh lessor name and
  its slot (`lease.lessorSlot_alloc`), and the call is made at that name. D-B4-6 is withdrawn.

**A restart generation** (`specC`'s case):

| Piece | Enters | Leaves | Why it survives |
|---|---|---|---|
| `memberWalKeep h` | P3, from T5's crash outputs (`walBootCrash`, `walDir_boot`) | never | as above; the restart's `ReadAll` cut and the fork's `DiscardUnsaved` are WAL steps proved over `walInv` (ReadAllInv.lean, DiscardR.lean) |
| `memberDurKeep` | P3: `rnDurK_alloc.law` at the image's `raftState S` and records `σ` | never | T2's crash law. **Needed:** `rnDurInvK` kept across bootstrap's WAL repair (the records' history changes under it), so either the repair is a `rnDurInvK` step (new law) or P3 allocates after a pre-read (D-B4-5) |
| `memberSnapKeep` | P3, from the image's `snapDirKeep` | never | T6 |
| the spine | P3, from the image's durable names | never | as above |
| `KeepBc` (the image's backend file, durable: `fileHoldsMDur i0 D`) | P3 (S0's stopped disjunct, `memberKeepRc`) | at bbolt `Open`'s commit point inside `NewServer`: the slot moves to `memberKeepR` with `KeepB`. This is the inverse of the crash-mode `DB.Close` (bbolt-crash's) | the file on disk after a crash is durable by definition; C-I1 from the open on |

So a restart's slot starts in S0's **stopped** disjunct and moves to the running one inside the call. Both
disjuncts exist in S0. `memberKeepRc`'s docstring must say that it also describes a restart before its
backend is open.

## 3. The four specs, restated

Notation: `srvKeepInv γ id dd ph L` is the etcdserver-level slot (D-B4-4). `memberKeepInv` is defined from it.
`srvKeepPh γph q ph` is the phase variable. Only the changed rows are shown; everything else is verbatim.

### 3.1 In-process `NewServer.specGK on cmp` (new; `specG` derived from it, §4)

Binders gain `(L : GooseLocalGS GF) (γph : GName)`. Precondition rows:

```lean
-- before
"Hnboot" ∷ (nodeBoot γ.cl srvClusterN γ.vs ctxs id ∗ raftState γ.cl id RaftState.init ∗ nodeVacant γ.cl id) ∗
"%Hsloc" ∷ ⌜γ.snapLoc id = some γd⌝ ∗ "Hsdir" ∷ ghostMapAuth γd 1 (∅ : GMap w64 Unit) ∗
-- after
"Hnboot" ∷ (nodeBoot γ.cl srvClusterN γ.vs ctxs id ∗ ∃ x, nodeVacantA γ.cl id x) ∗
"%Hsloc" ∷ ⌜γ.snapLoc id = some γd⌝ ∗
-- (B4) the generation's keep slot at a first start's entry: `raftState` at `init`, the vacancy's crash
-- token, the snapshot map at `∅`, the WAL area's keep (`srvKeepF0`); the call moves raft's state into
-- `rnDurInvK` at `newRaftNode`, the map into `snapDirKeep` at `snapDir_init`, and adds the backend's crash
-- invariant once it holds the backend's write transaction
"#Hkeep" ∷ srvKeepInv γ id cfg.DataDir' γph L ∗ "Hph" ∷ srvKeepPh γph (1/2) .first0 ∗
```

Post: in both arms, `srvKeepPh γph (1/2) .firstRun`. The slot then holds the first generation's run keep: the
WAL keep, `memberDurKeep`, `memberSnapKeep`, the spine, and the backend's crash invariant. The success arm is
otherwise `specG`'s verbatim. The error arm also leaves `.firstRun`, or `.first0` if the call failed before
`newRaftNode`: `∃ ph, ⌜ph ∈ [.first0, .firstRun]⌝`.

### 3.2 In-process `NewServer.specCK` (`specC` restated; one restart spec, as today)

```lean
-- before
"Himg" ∷ srvCrashImageAt γ ρo id cfg.DataDir' S σ i A D mb M ∗
-- after
-- (B4) the image's exclusive rows are in the slot, which the boot allocated (`memberGen_boot.law`):
-- raft's durability at the image (`rnDurInvK` at `S`, `σ`), the WAL area, the snapshot directory, the
-- backend file durable and closed; the call holds the loop's side of `rnDurInvK` and the image's pure
-- and persistent rows (`srvCrashImagePure`: `A`, `i`, `D`'s facts, `confAt`, the read facts)
"#Hkeep" ∷ srvKeepInv γ id cfg.DataDir' γph L ∗ "Hph" ∷ srvKeepPh γph (1/2) .restart0 ∗
"Hloop" ∷ srvDurLoop γ id νk h (σview S σ) ∗ "#Himgp" ∷ srvCrashImagePure γ ρo id cfg.DataDir' S σ i A D mb M ∗
```

The post drops `(∃ x, nodeCrashTok γ.cl id x) ∗ srvSnapKeep γ id cfg.DataDir' ∗` because both are in the slot
now, and gains `srvKeepPh γph (1/2) .restartRun`. The success arm is otherwise `specC`'s verbatim.
`srvDurLoop` is the loop's share that `rnDurK_alloc.law` returns: `rnWalViewK`, `token ν.app`,
`walCommitLb`. Today `newRaftNode` makes it; it now takes it as an input.

### 3.3 `NewServer_dist` (approved; restated on this branch only, for the packet)

This is `specGK`'s text with the existing dist changes, so the slot rows are token-identical to §3.1. The
exact before/after is in `b4-scratch/newserver-dist-before-after.md`, outside the repo, for the crash packet.

### 3.4 `NewServerC_dist` (draft)

This is `specCK`'s text with `specG_dist`'s network changes, again token-identical. The header's "Not in this
draft (open)" paragraph is replaced by the slot's docstring.

**dist-axiom-diff pairing.** Re-pair `NewServer_dist.wp_proof` with `NewServer.specGK` and
`NewServerC_dist.wp_proof` with `NewServer.specCK`, in `etc/dist-axiom-diff-allow.txt`. The slot rows need
no `dev` line, since they are token-identical. The existing `dev` lines stay unchanged, apart from the `pair`
lines' target names.

## 4. The in-process re-proof and its cost

| Piece | Change | Size (Lean lines) | Owner / dependency |
|---|---|---|---|
| `srvKeep*` definitions, the slot, the phase variable (new `E/SrvKeep.lean`); `memberDurKeep` moved there | definitions; `memberKeep*` restated over them | 150–250 | this task, but MemberCrash.lean is kaashoek's |
| `bootstrappedRaft.newRaftNode.spec` + `NodeStart.lean`/`NodeStartLinked.lean` | take the slot; `raftState` through `StartNode`'s/`RestartNode`'s AU from the slot (first start) or from `rnDurInvK` (restart); `rnDurInvK` allocated in the slot at entry (first) or taken from the caller (restart) | 300–600 | etcdserver (untrusted) |
| `snapDir_init` inside `NewServer` | the map into `snapDirKeep` + token, in the slot | 100–200 | T6 (a first-start form) |
| the backend's crash invariant at creation | from `bootOk`'s backend: needs `boltIno`, `dbHalf`, a live write tx | 200–500 | **T10**; may need `bootOk`'s or `OpenBackend`'s trusted post (§5) |
| the spine at a first start | `osPathDur_child` from bootstrap's `TouchDirAll`s | 100–200 | T8; `bootOk` does not expose them today (§5) |
| `NewServer.wp_proofGK` (from `wp_proofGAtA`'s 2.8k lines) | plumbing: the slot through the hypotheses `h0..h95` that change (newRaftNode's, the snapshot directory's, the backend's) | 300–500 | etcdserver |
| `specG` from `specGK` | allocate a slot from the pre's rows (`raftState`, the vacancy, the map) and drop it | 50–100 | etcdserver |
| `NewServer.wp_proofCK` | over `specRAt` restated the same way (NewServerR.lean's newRaftNode use and the restart contract); the backend's `KeepBc`→`KeepB` at `Open` | 800–1500 | after kaashoek's `σ.commit < i` case (NewServerCrash.lean:81) |
| callers | `etcdstart` / `AllocN` (none if `specG` stays); `NewServerDist`/`NewServerCDist`; the S0 stubs (`member_crash_boot`) | 100–200 | — |

Total: about 2.5–4.5k lines. Most of it is in T10's, T6's and kaashoek's files, or depends on them. No part
can be closed before T10 makes the backend's crash invariant concrete: a spec that puts `KeepB` into the
slot must name it, because the callee builds it. With `KeepB` left as a parameter, `KeepB := False` would
make the spec claim to produce `False`.

## 5. Trust

* `NewServer_dist`: restated (§3.3). This is what the brief allows.
* `NewServerC_dist`: a draft, restated.
* **The bootstrap contract** (`bootstrapContract`, a persistent triple; in dist from the approved axiom
  `bootstrap.wp_proof_dist`, in one process from the axiom `bootstrap.wp_proofOne`):
  * At a first start, `bootstrap` touches no slot row: it consumes `wal.bootRes` and `memStorRegAuth`, both
    obtainable again. A crash inside it is C-I3's (leftovers). It does not have to be slot-aware.
  * The pieces it creates still have to reach the slot: the spine from its `TouchDirAll`s, and the backend's
    write transaction and inode for T10's invariant. Either `bootOk`'s post exposes them, which is a change
    to an approved axiom's post, or they are derived from what `bootOk` gives (T10 decides).
  * At a restart, bootstrap changes the image: it cuts the WAL tail, `DiscardUnsaved`, and does the
    `.snap.db` rename. The slot must stay valid across those changes. Either C-I2 (`bootstrapCrashContract`,
    a law now and an axiom when the pin moves) becomes slot-aware, or the restart's `rnDurInvK` is allocated
    after bootstrap's WAL read (D-B4-5).
* `Serve_dist`/`Serve_distR`: **no change** if D-B4-1 and D-B4-2 hold, because the running code touches only
  the per-piece invariants. Otherwise the raft loop's first `Save` would have to open the slot inside an
  approved axiom.
* **The abuse question** (for the fresh review): the slot holds, at every step, only
  1. cluster ghost rows whose post-crash value is the pre-call value, because no Go step before their move
     can change them (no node of `id` exists before `newRaftNode`; no snapshot exists before the raft loop);
  2. invariants with crash tokens whose crash laws are proved, or for the backend reviewed (C-I1), against
     the file extension's crash semantics.

  It holds no running state. Nothing in it says what a file holds except through those crash laws.

## 6. S0 and T7 statements this design changes

1. `memberGen_boot.law` (P/crash/MemberBoot.lean:76). Its output gains the allocated slot at the phase's
   entry content: `.first0` (WAL keep, `raftState` `init`, the vacancy's crash token, the map), or
   `.restart0` (`memberKeepRc` at `KeepBc`, and the loop's side `srvDurLoop`). The restart case loses
   `srvCrashImage`'s exclusive rows (kvGen_boot's shape).
2. `memberKeepS` / `memberKeepInv` (:146, :160). They are restated as the etcdserver slot `srvKeepInv` at the
   member's names, with the phase variable. `KeepF` stops being abstract: it is the first generation's
   phase-indexed content above. `KeepB` stays T10's, but must be concrete before §3's specs can be stated.
3. `memberFirstCrash.law` (MemberCrash.lean:~880, **kaashoek's file**). Its target becomes `memberGen`: a
   first generation keeps `KeepF` after its first durable `Save` (D-B4-2). Its docstring's "before
   `newRaftNode` …, or with an unsaved first `Save`" becomes "until the WAL holds a `Save` (the fork's
   `DiscardUnsaved`)". `memberKeepR` (:822) is restated over `srvKeep*` (`memberDurKeep` moves to etcdserver).
4. `memberKeepRc` (:118): docstring only (it also describes a restart before its backend is open).
5. `memberFirst_of_share.law` / `memberFirst`: (Revision 1, F-A6) `memberGen_boot.law`'s first-start arm gains
   `∃ γl, ghostMapAuth γl ½ ∅ ∗ lease.lessorSlot γl` (`lease.lessorSlot_alloc`). D-B4-6 is withdrawn.

## 7. Decisions for the coordinator (each with a recommendation)

* **D-B4-1. Pieces in their own invariants; the slot holds invariants and tokens.** Recommended. The
  alternative, running state inside the slot, makes `Serve_dist`/`Serve_distR` open the slot. Needs T10's
  `KeepB` as an invariant plus a token (T10's plan already moves `dbCrashKeep` out of `memberKeepR`'s body).
* **D-B4-2. No first-start-to-restart swap during serving.** Recommended: `KeepF`'s crash law targets
  `memberGen`. Alternative: swap at the first durable `Save`, inside the raft loop, which is inside the
  serving axioms (a trusted change).
* **D-B4-3. A restart's slot is allocated at the boot (P3)**, in the stopped disjunct, and moves to the
  running one at bbolt `Open`'s commit point. Recommended. It needs a crash-mode `Open`, the dual of
  bbolt-crash's `DB.Close` (bbolt-crash lead).
* **D-B4-4. Layering.** Recommended: an etcdserver-level `srvKeep*`/`srvKeepInv`, with `memberKeep*`
  restated over them. The slot rows are then token-identical in the dist pairs. Alternative: a HOCAP slot,
  where the spec quantifies over the caller's `inv N P` with four caller-proved update laws. That keeps
  etcdserver free of dist definitions, but puts quantification over a caller's invariant into trusted axiom
  text, which is a harder review.
* **D-B4-5. A restart's WAL repair under `rnDurInvK`.** Either (a) a new `rnDurInvK` step law for
  `ReadAll`'s cut and `DiscardUnsaved`, with the bootstrap contract (C-I2) slot-aware; or (b) a crash inside
  the restart's bootstrap is covered by `walInv` plus the slot's raw rows (`raftState S`, the vacancy's
  token), and `rnDurInvK` is allocated after bootstrap's read, at `newRaftNode`'s entry as at a first start.
  Recommended: (b). It touches no trusted contract, provided C-I2's post says the records `bootstrap` read
  still hold `S`, which it does through `walReadFacts`.
* **D-B4-6 (WITHDRAWN, Revision 1; replaced by review D5's F-A6, §R1.2). The lessor slot at a first start.** `Hlslot` at the view's `γl` is consumed by `NewLessor` and
  cannot come back after a crash. Recommended for the crash class (lease mode `.none`): `NewServer_dist`
  allocates its own lessor name there, as `specG` does (`lessorSlot_alloc`), with `Hlslot` only when
  `lm ≠ .none`. That is a further change to `NewServer_dist`'s text, in the same packet. Alternative: a
  generation-indexed lessor slot (new ghost design).
* **D-B4-7. Order.** T10's `KeepB` (concrete, an invariant) and T6's first-start `snapDirKeep` come first.
  Then this task re-proves the specs (§4) after kaashoek's `σ.commit < i` case lands. Until then the dist
  restatement can only be drafted, as text, which is the scratch file.

## 7a. Decisions taken (the lead, with the coordinator, 2026-11-26)

* **Decided as recommended:** D-B4-1 to D-B4-5 and D-B4-7.
* ~~**D-B4-6: drafted as recommended.**~~ **Withdrawn** (Revision 1, the coordinator and the lead,
  2026-11-26). It broke the proved member proof at `lm = .none` (`server/MainLogger.lean`, review D5's F-A6).
  `NewServer_dist`'s lessor text stays unchanged. The boot allocates a fresh lessor name for a first start
  after a crash, and the axiom pairs with `specGAtK` (§R1.2).
* **The re-proof waits on its dependencies** (D-B4-7): T10's concrete `KeepB`, T6's first-start
  `snapDirKeep`, and kaashoek's `σ.commit < i` case.

## 8. Handoff (this session's end state)

* (Superseded by §R1.7.) `NewServer_dist`'s and `NewServerC_dist`'s draft text (B4, rev 0), with the slot's docstring
  (what it holds, and why each piece survives a real crash), is outside the repo, for the packet:
  `/home/ubuntu/.claude-E/jobs/b20ef685/tmp/b4-scratch/newserver-dist-before-after.md`.
* Not applied in Lean: it names §9's vocabulary, which is not written.
* §9 is specified here and not written in Lean, for one reason. A faithful `srvKeep*` needs definitions that
  live in `MemberCrash.lean`, kaashoek's file: `MemberKN`, `osSpineDur`, `memberDurKeep`, `memberWalKeep`,
  `memberSnapKeep`. They would have to move down to etcdserver, and `memberKeepR`/`memberFirstCrash.law`
  would have to be restated there. Writing stubs beside them would leave a second, unused vocabulary.
* On the re-proof's resumption, the order is: §9's move (coordinated with kaashoek), then §4.
* `etc/dist-axiom-diff.py --check`: ok, unchanged from S0. The re-pairings of §3 apply with the Lean text.
* Also on this branch: the `GracefulStop_dist` review's fixes F1-F5, and the review itself
  (`notes/axiom-review/gracefulstop-dist.md`, with its index row).

## 9. The etcdserver-level slot vocabulary (D-B4-4), specified

New defs module `Proof/go_etcd_io/etcd/server/v3/etcdserver/SrvKeep.lean`, namespace `EtcdGrove`.
* It imports `InvWalCrash`, `InvCrashImage`, raft's API, the WAL's `Inv`, `Fs`/`CrashTok`, and nothing under
  `examples/`.
* The move from `MemberCrash.lean` keeps names and bodies verbatim. The old names stay as `abbrev`s until
  their users are moved.

| New (etcdserver) | From | Body |
|---|---|---|
| `SrvKN` (structure) | `memberCrash.MemberKN` | the same 13 fields (`γ ρo h νk cid γb i0 Dl Dn J γd γm jd`); all are etcdserver types |
| `osSpineDur`, `osPathDur` (+ `Persistent` instances, `osSpineDur_nil/_cons`) | `MemberCrash.lean:69-112` | verbatim |
| `srvDurKeep γn id νk h` | `memberDurKeep` | `rnDurInvK γn id νk h ∗ token νk.tk ∗ nodeCrashTok γn.cl id νk.x ∗ token νk.ν.stop` |
| `srvWalKeep h` | `memberWalKeep` | `walInv … h.R h.jr h.r ∗ walCrashTok ∗ osSharedInv h.R` |
| `srvSnapKeepK k dd` | `memberSnapKeep` | `snapDirKeep (snapDirOf dd) k.γd (srvImageM k.γ.authOn k.γ) (fun j => monoNatLbOwn k.γm (j+1))` |
| `srvKNOk γ id dd k` (pure) | `memberKeepR`'s pure row | the same conjunction, with `∃ r, k.γ = {γ with reg := r}` |

New definitions:

```lean
/-- The keep slot's phase: a first generation's (`node`: raft's state moved into `rnDurInvK`; `snap`: the
snapshot map moved into `snapDirKeep`; `be`: the backend's crash invariant added), a restart's (`open`: the
backend open, its crash invariant in place of the closed durable file), or a stopped run's. -/
inductive SrvKeepPh | first (node snap be : Bool) | restart («open» : Bool) | stopped

/-- The phase variable (half in the slot, half with the code that moves it). -/
def srvKeepPh (γph : GName) (q : Qp) (ph : SrvKeepPh) : IProp GF := ghostVar γph q ph

/-- What the slot holds at phase `ph`, for member `id` of raft names `γ` with data directory `dd`, over the
backend's open and closed keeps `Kb`/`Kbc` (T10's; parameters until T10 defines them) and the member-level
persistent facts `Xr` of a restartable run (`memberRestartFacts k.γ k.ρo id`, supplied by the dist layer). -/
def srvKeepAt (γ : SrvRaft) (id : w64) (dd : GoString) (γd : GName)
    (Kb Kbc Xr : SrvKN GF → IProp GF) : SrvKeepPh → IProp GF
  | .first n s e => iprop(
      (∃ h : WalH GF, ⌜h.dir = srvWalDirOf dd⌝ ∗ srvWalKeep h ∗
        (if n then ∃ νk, srvDurKeep γ id νk h
         else raftState γ.cl id RaftState.init ∗ ∃ x, nodeCrashTok γ.cl id x)) ∗
      (if s then ∃ γm, snapDirKeep (config.snapDirOf dd) γd (srvImageM γ.authOn γ)
                         (fun j => monoNatLbOwn γm (uint.nat j + 1))
       else ghostMapAuth γd 1 (∅ : GMap w64 Unit)) ∗
      (if e then ∃ k, ⌜srvKNOk γ id dd k⌝ ∗ Kb k else True))
  | .restart o => iprop(∃ k : SrvKN GF, ⌜srvKNOk γ id dd k⌝ ∗ Xr k ∗ srvDurKeep k.γ id k.νk k.h ∗
      srvWalKeep k.h ∗ srvSnapKeepK k dd ∗ osSpineDur k.jd [go!"member", go!"snap"] k.J ∗
      (if o then Kb k else Kbc k))
  | .stopped => iprop(∃ k : SrvKN GF, ⌜srvKNOk γ id dd k⌝ ∗ Xr k ∗ srvDurKeep k.γ id k.νk k.h ∗
      srvWalKeep k.h ∗ srvSnapKeepK k dd ∗ osSpineDur k.jd [go!"member", go!"snap"] k.J ∗ Kbc k)

def srvKeepN : Namespace := nroot.@"srvKeep"

/-- The slot (persistent), at the generation `L`. The specs fix `γd` (from `γ.snapLoc id`), `Kb`, `Kbc` and `Xr`
once T10 lands; the draft text abbreviates them as `srvKeepInv γ id dd γph L`. -/
def srvKeepInv (γ : SrvRaft) (id : w64) (dd : GoString) (γd : GName) (Kb Kbc Xr : SrvKN GF → IProp GF)
    (γph : GName) (L : GooseLocalGS GF) : IProp GF :=
  letI : HeapGS HasLC.hasLC GF := ⟨G, L⟩
  inv srvKeepN (∃ ph, srvKeepPh γph (1 : Qp).half ph ∗ srvKeepAt γ id dd γd Kb Kbc Xr ph)
```

**Left out of the slot, deliberately:**
* `.first`'s spine. A first generation's crash target before its first durable `Save` is a first start, which
  needs no spine. T7's law needs it from that `Save` on, because the next start is a restart. If so, it is
  added to `.first _ _ true`: the spine exists from bootstrap's `TouchDirAll`s, before the backend opens.
* The cluster facts and the second later credit of S0's `memberKeep`. They belong to the member layer and stay
  in `memberKeepS` below.

**`memberKeep*` restated over them** (S0/T7 statements, P/crash/MemberBoot.lean and MemberCrash.lean):

```lean
/-- (replaces S0's `memberKeepS`/`memberKeepInv`; `KeepF` is gone: a first generation's keep is `srvKeepAt`'s
`.first` phases) -/
def memberKeepS (C) (cfg) (id) (γd) (KeepB KeepBc : GooseLocalGS GF → SrvKN GF → IProp GF) (γph) (L) : IProp GF :=
  memberClusterFacts C ∗ £ 1 ∗
    srvKeepInv C.γ id cfg.DataDir' γd (KeepB L) (KeepBc L) (fun k => etcdstart.memberRestartFacts k.γ k.ρo id) γph L
```

* `memberKeepR C cfg id KeepB` becomes `srvKeepAt … (.restart true)`, and `memberKeepRc` becomes `.stopped`.
  Both are `abbrev`s, with `dbCrashKeep` inside `KeepB` per D-B4-1.
* `memberFirstCrash.law` is stated at `srvKeepAt … (.first n s e)`, with target `memberGen`.
* `memberGen_boot.law`'s output gains `∃ γph, srvKeepInv … γph L ∗ srvKeepPh γph ½ ph₀`, where
  `ph₀ = .first false false false` (first start) or `.restart false` (restart).
* `memberGen_crash.law`'s `Keep` becomes `memberKeepS … γph`. The crash proof opens the invariant, splits on
  `ph`, and applies T2's, T5's, T6's and C-I1's crash laws piece by piece.
* `memberStop.law` moves the phase from `.restart true` to `.stopped` at `DB.Close`'s commit point. For a
  first generation's stop, the move from `.first true true true` to `.stopped` needs the restart facts `Xr`
  and the spine, which the stop has: `srvStopReq`'s boot evidence, and the persistent spine.
## Revision 1 (2026-11-26): review D5 applied, D-B4-6 withdrawn, P5's G2/G3 folded

Branch `etcd-safe-crash-b4r/2026-11-26`, from `etcd-safe-crash-b4/2026-11-26` @a45701179d. This is draft text
only: no Lean edit and no re-proof.

Inputs:
- review D5, `coordinator-notes/plans/review-d5-newserver-slot.md`;
- P5's gaps G2/G3, `notes/etcd-dist-p5s.md` on `etcd-safe-crash-p5s/2026-11-26`;
- the lead's and the coordinator's decisions of 2026-11-26.

Outputs, outside the repo, for the crash packet:
- `b4-scratch/newserver-dist-before-after.md` (rev 1; rev 0 kept as `…rev0.md`);
- `b4-scratch/c-i2-before-after.md` (new).

### R1.1 Each fix, and where it went

| Fix | What | Where |
|---|---|---|
| F-A1 (generation) | binder `L` dropped; the slot is at `hG.goose_localGS` | scratch §A.1, §A.3; §R1.3 |
| F-A1 (arm) | the vacancy's arm tied to the slot's crash token by a proved raft lemma, `nodeVacantA_crashTok_agree` | §R1.6 (stated, with a proof sketch; not proved in Lean); scratch §A.2, docstring item 2 |
| F-A2 (spine) | item 6 rewritten. The spine is in the slot at a restart, and in a first generation only from `be` on (G3); before that a first generation holds none | scratch §A.7(b) item 6; §R1.3 `.first`. **See §R1.8 (1)**: decision 2's "restart-only" and decision 5's G3 conflict, and F-A2 names G3's option as its alternative |
| F-A3 (what a crash leaves) | the sentence replaced by F-A3's wording. It names directories, `.touch` files, the unsaved WAL, the backend file that no later start removes (a crash between `OpenBackend` and `wal.Create`'s rename), and bbolt's init-window file | scratch §A.7(b), "So a crash at any step …" |
| F-A4 (`wal.Discard`) | item 4 uses `wal.Discard` (fork `251a430ce`, after `wal.Unsaved` and `removeBackendDurably`) | scratch §A.7(b) item 4 |
| F-A4 (duplicates) | the existing paragraph on duplicates is at `nodeVacantA` and `Hph` | scratch §A.7(a) |
| dedup | rev 0's "Nothing else is in the slot" and "What the slot cannot do" are merged into one paragraph | scratch §A.7(b) |
| F-A5 | not applicable (D-B4-6 withdrawn) | — |
| F-A6 | `Hlslot` and `mvccLeases E.γ = γl` unchanged. The boot allocates a fresh lessor name for a first start after a crash. The axiom pairs with `specGAtK` | scratch §A.3', §A.6, §A.8; §R1.2; §2, §6 item 5, §7, §7a |
| F-B1 | premise `γ.cl.bootLen ≤ σ.commit →` in `specC_dist` and `specCK` | scratch §B.3 |
| F-B2 | premise `σ.b ≤ uint.nat i →` in both | scratch §B.3; the rename-window phase is in `c-i2-before-after.md` §4 |
| F-B3 (rows) | `"Hvac" ∷ nodeVacantA γ.cl id νk.x`, `"Hrauth" ∷ memStorRegAuth M`, and the removal counter `"Hrmc"` (F-B3's third row) | scratch §B.5 (with a table of where each of `srvCrashImageAt`'s rows went) |
| F-B3 (tie) | the slot's witness `k` is tied to `νk h D` (and `ρo`, `γm`) by the restart key `srvKeyR ρo νk h γm D`. `S σ` are tied through `Hloop`'s view half | scratch §B.5; §R1.3 |
| F-B4 | the crash-aware C-I2 (`bootstrapCrashContractK`), with `#HbootC` moved to it in both texts | `c-i2-before-after.md`; scratch §B.4, §B.7 |
| F-B5 | the duplicate sentence is at `Hvac` and `rnDurInvK` | scratch §B.7 |
| G2 | the raft loop's stop mode (keep) is fixed at `newRaftNode`; the posts' built part and stop keep are at `(sm := rnStopMode.keep)` | §R1.4; scratch §A.5, §B.6 |
| G3 | `.first _ _ true` gains the spine, and the restart facts `Xr`, through the key. **This departs from a literal "`.first _ _ true` gains `Xr`"**: see §R1.5 | §R1.3, §R1.5 |
| (new) restart error arm | `NewServerC_dist`'s error post admits `.stopped`: `bootstrap.go` and `NewServer`'s deferred `b.Close()` close the backend on an error | scratch §B.6; `c-i2-before-after.md` §3.2 |

### R1.2 D-B4-6 withdrawn: the F-A6 route

- `NewServer_dist`'s lessor text is unchanged: `Hlslot` at `γl` and `mvccLeases E.γ = γl`.
- `memberGen_boot.law`'s first-start arm gains `∃ γl, ghostMapAuth γl (1 : Qp).half ∅ ∗ lease.lessorSlot γl`, from the
  proved `lease.lessorSlot_alloc`, as `NewServer.wp_proofG` derives `specG` from `specGAt`. A first start after a
  crash is called at that fresh name.
- `NewServer_dist` pairs with `NewServer.specGAtK`, which is `specGAt` plus the B4 rows, stated with `Hlslot` last
  as in the dist text. The `mvccLeases` dev line is deleted, and the `γl`/`Hlslot` parts of lines 12–13 go.
- `server/MainLogger.lean`'s `lm = .none` case keeps working.

### R1.3 §9 revised: self-contained replacement code (for `E/SrvKeep.lean`)

**What changes from §9.** Apply these on top of §9's verbatim move. Everything not listed stays as §9 has it:
`SrvKN`, `osSpineDur`/`osPathDur`, `srvDurKeep`, `srvWalKeep`, `srvSnapKeepK`, `srvKNOk`, `srvKeepPh`, `srvKeepN`.
1. **`srvKeepAt`/`srvKeepInv` lose the parameter `Xr`** and gain a key `kr : SrvKeepKey GF`. `.restart`/`.stopped`
   drop the conjunct `Xr k`. The restart facts move to `memberKeepS`, through the key (§R1.5).
2. **Each `SrvKN` witness must satisfy the key** `kr ph k` at its phase. This is F-B3's tie. `SrvKeepPh` stays
   unparameterized: a `ghostVar` over `SrvKN GF` would need `Pos.Countable`, which `WalH GF`'s instance fields do not
   have.
3. **`.first` is restated under one set of witnesses** `h νk γm`, and its `be` arm's `k` must agree with them
   (`k.h = h ∧ k.νk = νk ∧ k.γm = γm`). The `be` arm also gains the spine (G3). So at `.first true true true` one
   `k` carries everything `.stopped` needs, which P5's `kbClose.law` move uses.

```lean
/-- (unchanged from §9) -/
inductive SrvKeepPh | first (node snap be : Bool) | restart («open» : Bool) | stopped

/-- **The slot's key** (Revision 1, review D5 F-B3): which witnesses `k` a phase may hold. It is pure and fixed for
the generation, so the specs tie the slot's pieces to their binders without a ghost variable over `SrvKN`. -/
abbrev SrvKeepKey (GF : BundledGFunctors) := SrvKeepPh → SrvKN GF → Prop

/-- **A first start's key**: the pieces are this run's (`k.ρo = ρ`). -/
def srvKeyF (ρ : ReqNames) : SrvKeepKey GF := fun _ k => k.ρo = ρ

/-- **A restart's key**: the names the boot allocated from the image. They are raft's crash-aware durability `νk`,
the WAL `h`, the removal counter `γm` and the image's writer `ρo`. While the backend is closed and not yet opened
(`.restart false`), its file is at the image's data `D`. That constraint is phase-indexed: `.stopped` holds the data
the stop closed. -/
def srvKeyR (ρo : ReqNames) (νk : WalNamesK GF) (h : WalH GF) (γm : GName) (D : backend.Data) : SrvKeepKey GF :=
  fun ph k => k.ρo = ρo ∧ k.νk = νk ∧ k.h = h ∧ k.γm = γm ∧ (ph = .restart false → k.Dn = D)

/-- What the slot holds at phase `ph`, for member `id` of raft names `γ` with data directory `dd`, over the backend's
open and closed keeps `Kb`/`Kbc` (T10's: fixed definitions in the specs, never binders) and the key `kr`. -/
def srvKeepAt (γ : SrvRaft) (id : w64) (dd : GoString) (γd : GName)
    (Kb Kbc : SrvKN GF → IProp GF) (kr : SrvKeepKey GF) : SrvKeepPh → IProp GF
  | .first n s e => iprop(∃ (h : WalH GF) (νk : WalNamesK GF) (γm : GName),
      ⌜h.dir = srvWalDirOf dd⌝ ∗ srvWalKeep h ∗
      (if n then srvDurKeep γ id νk h
       else raftState γ.cl id RaftState.init ∗ ∃ x, nodeCrashTok γ.cl id x) ∗
      (if s then snapDirKeep (config.snapDirOf dd) γd (srvImageM γ.authOn γ)
                   (fun j => monoNatLbOwn γm (uint.nat j + 1))
       else ghostMapAuth γd 1 (∅ : GMap w64 Unit)) ∗
      -- (G3) from the backend's move on: the backend's crash keep and the durable spine, at one witness
      -- agreeing with the arms above
      (if e then ∃ k : SrvKN GF,
          ⌜srvKNOk γ id dd k ∧ kr (.first n s e) k ∧ k.h = h ∧ k.νk = νk ∧ k.γm = γm⌝ ∗
          osSpineDur k.jd [go!"member", go!"snap"] k.J ∗ Kb k
       else True))
  | .restart o => iprop(∃ k : SrvKN GF, ⌜srvKNOk γ id dd k ∧ kr (.restart o) k⌝ ∗
      srvDurKeep k.γ id k.νk k.h ∗ srvWalKeep k.h ∗ srvSnapKeepK k dd ∗
      osSpineDur k.jd [go!"member", go!"snap"] k.J ∗ (if o then Kb k else Kbc k))
  | .stopped => iprop(∃ k : SrvKN GF, ⌜srvKNOk γ id dd k ∧ kr .stopped k⌝ ∗
      srvDurKeep k.γ id k.νk k.h ∗ srvWalKeep k.h ∗ srvSnapKeepK k dd ∗
      osSpineDur k.jd [go!"member", go!"snap"] k.J ∗ Kbc k)

/-- The slot (persistent), at the generation `L`. The specs pass the generation they run in (`hG.goose_localGS`,
review D5 F-A1). -/
def srvKeepInv (γ : SrvRaft) (id : w64) (dd : GoString) (γd : GName) (Kb Kbc : SrvKN GF → IProp GF)
    (kr : SrvKeepKey GF) (γph : GName) (L : GooseLocalGS GF) : IProp GF :=
  letI : HeapGS HasLC.hasLC GF := ⟨G, L⟩
  inv srvKeepN (∃ ph, srvKeepPh γph (1 : Qp).half ph ∗ srvKeepAt γ id dd γd Kb Kbc kr ph)
```

`memberKeep*` are restated over this. This replaces §9's `memberKeepS` block; it lives in S0/T7's files, not in
etcdserver:

```lean
def memberKeepS (C) (cfg) (id) (γd) (KeepB KeepBc : GooseLocalGS GF → SrvKN GF → IProp GF) (kr : SrvKeepKey GF)
    (γph) (L) : IProp GF :=
  memberClusterFacts C ∗ £ 1 ∗
    srvKeepInv C.γ id cfg.DataDir' γd (KeepB L) (KeepBc L) kr γph L ∗
    -- (G3, §R1.5) the restart facts at every witness the key admits, in any phase: the boot proves it at
    -- allocation (a restart from the image's, a first start from `memberBoot_restartFacts` at the run's names)
    □ (∀ (ph : SrvKeepPh) (k : SrvKN GF), ⌜srvKNOk C.γ id cfg.DataDir' k ∧ kr ph k⌝ →
        etcdstart.memberRestartFacts k.γ k.ρo id)
```

Uses:
- `memberGen_boot.law`'s output gains `∃ γph, srvKeepInv … kr γph L ∗ srvKeepPh γph ½ ph₀`, where either:
  - `kr = srvKeyF ρ` and `ph₀ = .first false false false`, plus the armed vacancy `nodeVacantA γ.cl id x` with the
    slot's `nodeCrashTok … x` and F-A6's fresh lessor slot; or
  - `kr = srvKeyR ρo νk h γm D` and `ph₀ = .restart false`, plus the call's rows of scratch §B.5 (`srvDurLoop`,
    `Hvac`, `Hrauth`, `Hrmc`, `srvCrashImagePure`).
- An unsaved image (`σ.commit < bootLen`) goes to the first-start arm (F-B1).

### R1.4 G2: the raft loop's stop mode is fixed at `newRaftNode`

`bootstrappedRaft.newRaftNode` gets a keep-mode spec (`newRaftNode.specK`, untrusted, part of §4's
`newRaftNode` row).
- **At a first start** it takes the slot at `.first false s e`. In one ghost step at entry it allocates
  `rnDurInvK` with `rnDurK_alloc.law`, from the slot's `raftState … init` and the WAL's records. It puts
  `srvDurKeep γ id νk h` into the slot, including `token νk.ν.stop` and the arm's crash token at `νk.x`. That needs
  `x` = the arm of `Hnboot`'s vacancy, which §R1.6's lemma gives. The phase moves to `.first true s e`.
- **At a restart** it takes the loop's side `srvDurLoop` (the slot already at `.restart true`) and moves nothing.
- **Either way** it starts the loop in the keep stop mode: `rnStopMode.keep`, whose `onStop` uses no
  `rnDurK_take` and puts `rnStopImageK γ := ∃ x, nodeVacantA …` into `done`'s escrow `rnDoneEscK` (P5 §2.3).
  The wrapper predicate it returns carries the mode.
- So the built part and the stop keep in `specGAtK`/`specCK`, and in the two dist texts, are at
  `(sm := rnStopMode.keep)` (scratch §A.5, §B.6). Today's `specG`/`specC` are the `.take` instances. The argument's
  final name and position are P5's.

### R1.5 G3: the spine and the restart facts for `.first _ _ true` → `.stopped`

- **The spine** is in `.first _ _ true` (§R1.3). It exists from `bootstrap`'s `TouchDirAll`s, before the backend
  opens. The call needs `bootOk` to expose it (§5, T8: a change to `bootstrap.wp_proof_dist`/`wp_proofOne`'s post,
  or derived from what `bootOk` gives).
- **The restart facts `Xr`** are **not** a conjunct of `.first _ _ true`. Instead, `memberKeepS` holds their
  evidence over the key, persistently, from allocation (§R1.3), and `.restart`/`.stopped` drop `Xr k` too. Why
  this departs from P5's literal recommendation:
  - An in-process `specGAtK` (or `NewServer_dist`) that must *put* `Xr k` into the slot at `be` must produce it.
    For a parameter `Xr` it cannot: `Xr := False` would make the post claim `False`, the §4 lesson about `KeepB`.
  - Fixing `Xr := memberRestartFacts` in the etcdserver text is not possible either. etcdserver cannot name it
    (it is in `examples/etcd/restart`), and it holds only in the crash class (auth off, no compaction,
    `lease.runCfg … .none`, `¬ clusterNoSnap`), while `NewServer_dist` covers every mode.
  - With the evidence in `memberKeepS`, the consumers (the member layer's crash law and `memberGen_boot` after a
    first generation's first `Save`) instantiate it at the slot's `k`, which the key admits. P5's `kbClose.law`
    then needs no `Xr`.
- **The literal alternative,** if the lead prefers it: keep `Xr` as a parameter of `srvKeepAt`, put `Xr k` in
  `.first _ _ true`'s `be` arm and in `.restart`/`.stopped` (as §9), and make `srvKeepInv` carry the persistent
  evidence `□ ∀ ph k, ⌜srvKNOk γ id dd k ∧ kr ph k⌝ → Xr k` beside the `inv`, so the call gets `Xr k` from the slot
  itself. That is sound, but the two copies of `Xr` are redundant.

### R1.6 The raft lemma tying the vacancy's arm (F-A1)

The lemma is stated here; it is not written in Lean (no edit on this branch). It goes in
`Proof/go_etcd_io/raft/v3/InvNodeRule.lean`, beside `nodeCrash`:

```lean
variable [CrashGS GF] in
/-- **The armed vacancy and a crash token of one id are of one arm** while the generation runs. Both hold the
arm's crash invariant `nodeCrashInv` (`raftArmed`, `raftCrashTok`), which `nodeCrashInv_agree` makes one. -/
theorem nodeVacantA_crashTok_agree (γ : Cluster) (N : Namespace) (id : w64) (x y : CrashNames) (E : CoPset)
    (HE : ↑N ⊆ E) :
    ⊢ isCluster (GF := GF) γ N -∗ notCrashed -∗ nodeVacantA γ id x -∗ nodeCrashTok γ id y ={E}=∗
      notCrashed ∗ nodeVacantA γ id x ∗ nodeCrashTok γ id y ∗ ⌜x = y⌝
```

- **Proof sketch** (about 15 lines):
  1. Unfold `nodeVacantA`/`nodeCrashTok` to `raftArmed γ.raft id x` and `raftCrashTok γ.raft id y`. Each contains
     the persistent `nodeCrashInv γ.raft id _`.
  2. `isCluster` gives `γ.raft.reNs = N .@ "raft"`, so `↑(crashNs γ.raft id) ⊆ ↑(raftN γ.raft) ⊆ ↑N ⊆ E`
     (`crashNs_raftN`).
  3. Apply `nodeCrashInv_agree`.
- **Why not proved:** it needs a build of raft's `InvNodeRule` in a worktree with no built `.olean`s.
- **Review D5's form** (`notCrashed -∗ nodeVacantA -∗ nodeCrashTok ={E}=∗ notCrashed ∗ ⌜x = y⌝`) would consume both
  exclusive resources. This statement gives them back.
- **Where it is used:** in `newRaftNode.specK`'s move (§R1.4), which needs `notCrashed`. `StartNode`'s update does
  not hand it out; only `RestartNode`'s does (`InvNodeRule.lean:1331`). So the move must be made at a step whose
  proof can take the generation's `notCrashed` from the state interpretation, as the WAL's crash steps do
  (`InvWalCrashSteps.lean`).
- **Fallback:** if no such step exists at `newRaftNode`'s entry, use F-A1's text option: a binder
  `(x : CrashNames)`, `nodeVacantA γ.cl id x` in `Hnboot`, and `.first`'s `nodeCrashTok γ.cl id x` (the arm a
  parameter of `srvKeepAt`, as kvnet's `fl.x`).
- **At a restart** no lemma is needed: the key pins `k.νk = νk`, and `Hvac` is at `νk.x`.

### R1.7 Handoff

- The draft texts, outside the repo, for the crash packet and the delta review:
  - `/home/ubuntu/.claude-E/jobs/b20ef685/tmp/b4-scratch/newserver-dist-before-after.md` (rev 1);
  - `…/newserver-dist-before-after.rev0.md` (rev 0, kept for the diff);
  - `…/c-i2-before-after.md` (new, the crash-aware C-I2).
- No Lean is changed on this branch. §R1.3 is ready for kaashoek's `E/SrvKeep.lean`
  (`etcd-safe-crash-b4move/2026-11-26`) as a delta on §9's verbatim move.

### R1.8 Still open (for the lead and the delta review)

1. **The spine's wording (F-A2 against G3).** Decision 2 says "the spine is restart-only". Decision 5 folds G3,
   which puts the spine in `.first _ _ true`. F-A2 itself names G3's option as its alternative. I applied G3: the
   spine is in the slot at a restart, and in a first generation from `be` on; a first generation holds none
   before. If the lead wants "restart-only" literally, G3's first-generation stop needs another source for the
   spine.
2. **D-B4-5 is not what the texts do.** §7a records (b): `rnDurInvK` is allocated after bootstrap's read, at
   `newRaftNode`'s entry. But §3.2, §9 and both rev 0 and rev 1 of `NewServerC_dist`/`specCK` allocate it at the
   restart's boot: `srvDurLoop` is in the precondition, and `.restart` holds `srvDurKeep`. That is (a)'s shape.
   Rev 1 keeps it, because F-B3's tie and the crash-aware C-I2 are written for it. It needs `ReadAll`'s
   torn-tail cut to be a step that keeps `rnDurInvK`'s records at `σ` (a new law if the history changes under
   it). `Discard` is excluded by F-B1. The lead should either re-decide D-B4-5 as (a), or have §B restated to
   (b): `.restart` gains a `node` flag, the precondition loses `srvDurLoop`, and the C-I2-K contract carries the
   raw `raftState S`.
3. **The success posts' pure claims.** Each success post's phase (`.first true true true`, `.restart true`) claims
   a witness with `srvKNOk γ id dd k`. Its pure rows (roots in `k.h.R`, `PathFits` of every `.snap.db` path, …)
   must follow from the precondition. Otherwise the in-process spec is unprovable and the interim axiom would
   give `False`. Someone has to check each row against `wal.bootRes`/`bootCfgOk`/`srvCrashImagePure` before the
   packet goes out.
4. **G1** (the backend in T10's crash mode inside `srvBuiltG`/`srvStop.keep`, and `bootOkRK`'s backend rows) is
   not in rev 1. It needs T10's decision.
5. **`srvKb`/`srvKbc`, `wal.restartOkK`, `srvCrashImagePure`, `(sm := …)`** are placeholders until T10, T5 and P5
   write them. The gate's token-identity with `specGAtK`/`specCK` can only be checked against the written specs.
6. **The crash-mode bbolt `Open`** (D-B4-3) is a dependency of C-I2-K's commit point. It is the bbolt-crash
   lead's.

## Revision 2 (2026-11-26): review D5r applied, G1 answered, kaashoek's `SrvKeep.lean` names

Branch `etcd-safe-crash-b4r/2026-11-26`, on top of rev 1 (@b0478f37e0). Draft text only: no Lean edit, and no
re-proof.

Inputs:
- the delta review of rev 1, `coordinator-notes/plans/review-d5r-newserver-slot.md`. Its verdicts: §A and §B are
  sound with fixes; C-I2-K is **unsound as written**;
- kaashoek's G1 answer (#50, comment 7199212727; `notes/etcd-dist-d6.md` "T10 step 2 … G1" on
  `etcd-safe-t10b/2026-11-26`);
- kaashoek's vocabulary move, `etcd-safe-crash-b4move/2026-11-26` @16fdd8add3 (`SrvKeep.lean`; built);
- the statements kaashoek left for the owner (#50, comment 7200454986).

Outputs, outside the repo, under `/home/ubuntu/.claude-E/jobs/b20ef685/tmp/b4-scratch/`. Each rev-1 file is kept as
`*.rev1.md`.
- `newserver-dist-before-after.md` (rev 2: §A `NewServer_dist`, §B `NewServerC_dist`);
- `c-i2-before-after.md` (rev 2: C-I2-K);
- `srvkeep-member-before-after.md` (new):
  - §1, trusted: `SrvKeep.lean`'s two new definitions, `srvKNDirOk` and `srvWalProg`;
  - §2, untrusted: `memberKeepS`, `memberKeepR`/`Rc`, and the four member laws over the slot.

### R2.1 Each review finding, and how it was resolved

| Finding (D5r) | Resolution | Where |
|---|---|---|
| A-1 (`.first true true true` asserts `srvKNOk`'s witness-free rows) | premise `srvKNDirOk (GF := GF) cfg.DataDir' →` after `bootCfgOk … → N + 7 + bootWB ≤ backend.wbInit →`, in `NewServer_dist` and `specGAtK`. `srvKNDirOk` is new in `SrvKeep.lean`. **Deviation:** `srvKNOk`'s body is kept (a projection lemma `srvKNOk_dirOk` instead of redefining it), so the move's destructurings and `MemberCrash.lean` are untouched | scratch §A.1b; srvkeep §1.1 |
| A-2 (`specGAtK` blocked on G1) | restated over G1's answer. T10's backend is one bundle with a payload `KB` (`cmtInvK := inv cmtN (cmtBody ∨ crashed ∗ token γk)`, `cmtBody ∋ dbCrashKeep ∗ KB`; `KB := True` untracked). So `srvBuiltG`/`srvStop.keep` keep their text, with no mode argument. `srvKb k` holds only crash tokens, the record being inside `cmtInvK`, so the doubled `dbHalf` does not arise. The landing conditions are restated (§R2.4) | scratch header, §A.5, §A.9, §B.9 |
| A-2 (vacancy lemma not proved) | stated as obligation O-vac, a landing condition, with F-A1's binder as fallback | scratch §A.0, §A.2, §A.7 item 2, §A.9 |
| A-3 (docstrings) | applied verbatim: "raft's lemma … (design §R1.6; to be proved from `nodeCrashInv_agree` before this text lands)"; "A crash leaves a prefix of the history at least as long as the synced mark" | scratch §A.0, §A.7(b) |
| B-1 (WAL program side missing) | `"Hwalp" ∷ srvWalProg h` after `Hvac` in `NewServerC_dist`, `specCK` and the C-I2-K precondition. The row is named (`srvWalProg`, new in `SrvKeep.lean`) instead of inline, for one token-identical row in three places. B.5's table row is corrected | scratch §B.5; srvkeep §1.2; c-i2 §3.2 |
| B-2 (B.3 "exactly") | replaced by D5r's wording, with the converse's counterexample recorded | scratch §B.3 |
| B-3 (coverage: `i < σ.b`) | D5r's wording in B.1 and C-I2-K §4. `specC`/C-I2's `.snap.db` case are not retired before `restartSnap`. C-I2's first case goes when `specC` → `specCK`. `memberGen_boot.law` keeps a window arm (W) | scratch §B.1, §B.9; c-i2 §1, §4, §6; srvkeep §2.4 |
| K-1 (post fixes the fresh `*WAL` address) | `bootOkRK`'s `"Hwal" ∷ wal.restartOkK cfg id cid h bw.w' σ`, at the handle `{h with w := bw.w', γ := γs}`, with no `walRecsH`. Obligation O-w (untrusted lemma, T2/T5) | c-i2 §3.3 |
| K-1b (new in rev 2, beyond D5r) | `wal.Open` also allocates the handle's ghost names `h.γ.γ`/`h.γ.γl` (`storage.walOpen` holds `ghostVar h.γ.γ`). Fixing them to the boot's `h` is the K-1 refutation again. So `γs : WalShN` is existential, with only `γs.inc = h.γ.inc` tied | c-i2 §3.3 |
| K-2 (precondition lacks lock token, call permission's half) | `srvWalProg h` in the precondition. It is given back on an error at `.restart false`, and is inside the open handle on success | c-i2 §3.2 |
| K-3 (step list) | replaced by D5r's list, plus the reason `Unsaved` is false (it reads a state record first) | c-i2 §3.2 docstrings |
| Q4 (`kr` never an axiom binder) | stated as a rule in all three scratch files. `memberKeepS` and the member laws take `kr` as an existential or binder: allowed, since they are untrusted (srvkeep §2) | all |
| "Recorded, not filed" (an unsaved WAL with a CRC error is restarted by Go) | open question Q8, for `memberGen_boot.law`'s (T3/C-I3) review | §R2.5 |
| SrvKeep names (kaashoek's move) | every text uses `SrvKeep.lean`'s names and argument order (`srvKeepInv γ id dd γd Kb Kbc kr γph L`). The `atCtx` read is `hG` itself in the specs (`G`, `lctx` are `hG`'s instances; structure eta) | scratch header, §A.3 |
| owner's statements (#50 7200454986) | drafted, untrusted: `memberKeepS` (`γ' γd γph kr` existential: `Keep` is per-generation, and the slot is at the run's `{C.γ with reg := r}`), `memberKeepR`/`Rc` as `srvKeepAt … (.restart true)`/`.stopped`, `memberFirstCrash.law` (target `memberGen`), `memberGen_boot.law` (arms F, R, W), `memberGen_crash.law` (text unchanged, instance changed), `memberStop.law` (key premise `∀ ph k, kr ph k → kr .stopped k`) | srvkeep §2 |
| R1.8 (1) spine, (2) D-B4-5 | decided by the lead: G3 applied (the spine is in `.first _ _ true`), D-B4-5 = (a) (`rnDurInvK` is allocated at the restart's boot) | — |

### R2.2 Trusted items in rev 2 (each in Today / With this change form in the scratch texts)

| Item | Kind | Text |
|---|---|---|
| `NewServer_dist` | approved axiom, changed | scratch §A |
| `NewServerC_dist` | draft axiom | scratch §B |
| `bootstrapCrashContractK` + `.law` | new interim law (a premise, so trust) | c-i2 §3.2 |
| `bootOkRK`'s `"Hwal"`, `wal.restartOkK` | read by C-I2-K | c-i2 §3.3 |
| `srvKNDirOk` | read by `NewServer_dist` | srvkeep §1.1 |
| `srvWalProg` | read by `NewServerC_dist`, C-I2-K | srvkeep §1.2 |
| the rest of `SrvKeep.lean` (unchanged) | read by the three | srvkeep §1.3 |
| `srvKb`, `srvKbc` | read by the three; T10's placeholders | scratch header |

### R2.3 Untrusted (srvkeep §2)

`memberKeepS`, `memberKeepR`, `memberKeepRc`, `etcdstart.memberBootK`, `memberFirstCrash.law`, `memberGen_boot.law`,
`memberGen_crash.law` (unchanged text), `memberStop.law`. No axiom reads any of them. Each law is proved by its
owner, and the closed theorem discharges it.

### R2.4 Obligations (untrusted; each is a landing condition of an after-text)

- **O-vac** (raft): prove `nodeVacantA_crashTok_agree` (§R1.6), or fall back to F-A1's binder `x`.
- **O-w** (T2, T5): `walRecsH`, `walHistH`, `walInv`, `srvWalKeep`, `srvWalProg`, `rnDurInvK`, `srvDurLoop`,
  `srvDurKeep` and `walSaveH.law`'s update read `h : WalH` only through fields other than `w`, `γ.γ`, `γ.γl`.
  `srvWalKeep`/`srvWalProg` read only `WalA` fields, so for them it holds by `rfl`. Two things need it: C-I2-K's
  fresh handle, and `specGAtK`'s re-pick of the slot's WAL witness after `wal.Create`.
- **O-Kb** (T10): `srvKb`/`srvKbc` read neither `k.h` nor `k.νk`. Reason: at a first start the backend's piece
  enters (`be`) before `wal.Create` and `newRaftNode`, so the proof re-picks `k.h`/`k.νk` afterwards.
- **O-pure** (`specGAtK`, `specCK`): the witness-dependent rows of `srvKNOk` at the success posts' phases (roots in
  `k.h.R`, `IsUnder`, `k.h.md`) follow from `wal.bootRes`/`bootOk` (first start) or the boot's image (restart).
  This is R1.8 (3) minus A-1's part.
- **Landing**, beyond these: T10's crash-aware backend in Lean, with `OpenBackend.spec` opening the server's backend
  with the server's payload; `specGAtK`/`specCK` written, proved, and gated; `NewServer_dist` to the user as a
  changed approved axiom (scratch §A.9, §B.9).

### R2.5 Still open

1. **K-1b's incarnation.** Does `wal.Open` of an existing WAL keep the files' incarnation (`γs.inc = h.γ.inc`)?
   That is T5's to confirm. If it does not, `inc` becomes existential too, and `walRecsH`'s tie is restated.
2. **The tie at the stop** (P5, T10). `kbClose.law` turns the slot's `srvKb k` into `srvKbc k` at `DB.Close`'s
   commit point. That needs the closing backend's names to be `k.γb`, but `srvBuiltG`/`srvStop.keep` do not expose
   them. Either the crash-mode `Close` recovers the tie through the token's exclusivity, or the stop keep exposes
   `B = k.γb`.
3. **A-1 by derivation?** If `srvKNDirOk` follows from `wal.bootRes`/`bootCfgOk` (D5r: the `PathFits` row plausibly
   from `WalA.fits`; the file-system context and `snapDirOf`'s path have no derivation in the text), the premise can
   go before landing.
4. **`wal.restartOkK`'s `Hs`.** It is existential, as today's `wal.restartOk`. Tying it to `rnDurInvK`'s `walHistH`
   is T5's.
5. **`memberFirstCrash.law` lacks `idIssueCrashStart`.** Today's law lacks it, and `memberGen_crash.law` has it.
   The owner should align the two (srvkeep §2.3).
6. **Elaboration.** The specs' `srvKeepInv … hG.goose_localGS` is meant to read the slot at `hG` (structure eta).
   Confirm when `specGAtK` is written.
7. **Arm (W) of `memberGen_boot.law`.** A generation started inside the `.snap.db` window has no keep slot, so the
   B4 crash law does not cover it until `restartSnap` exists. That is today's coverage. The etcd_safe crash theorem
   already takes `¬ clusterNoSnap` and cannot close for runs with snapshot transfer before the window has a phase.
8. **F-B1's converse** (D5r, recorded). Go restarts an unsaved WAL when `wal.Unsaved` hits a CRC read error
   (`bootstrap.go:92`), so arm (F)'s "unsaved → first start" is not always what Go does. This is for
   `memberGen_boot.law`'s and C-I3's review (T3).
9. Carried from R1.8: the placeholders `srvKb`/`srvKbc`, `srvCrashImagePure` and `(sm := …)`; the crash-mode bbolt
   `Open` (D-B4-3, the bbolt-crash lead's).

### R2.6 What needs a fresh delta review

- **C-I2-K (c-i2 §3.2–§3.3), in full.** Rev 1 was unsound; rev 2 adds K-1b, which D5r did not ask for, and
  `wal.restartOkK`'s text. Re-run D5r's refutation with `h.w` and with `h.γ.γ`.
- **`NewServerC_dist` §B.5/§B.6.** `Hwalp`, and the claim that the post exposes no `h`.
- **`NewServer_dist` §A.1b**, A-1's premise, and the deviation (projection lemma instead of redefining
  `srvKNOk`). Also §A.5/§A.9, G1's reading.
- **`srvkeep` §1** (the two new trusted definitions).
- **`srvkeep` §2** needs a lighter review, for vacuity or unprovability only, since it is untrusted. Two points
  above all: `memberKeepS`'s existentials, and `memberStop.law`'s key premise.

### R2.7 Handoff

- No Lean is changed on this branch. `SrvKeep.lean`'s additions (srvkeep §1) are ready for kaashoek's move branch as
  a delta. The member restatements (srvkeep §2) are for their owner, after the bbolt-crash lead's C-I1 swap lands in
  `MemberCrash.lean`.

## Revision 3 (2026-11-26): review D5r2 applied

The input is review D5r2, `coordinator-notes/plans/review-d5r2-newserver-slot.md`: nothing UNSOUND, every item
SOUND WITH FIXES. The scratch texts are updated in place, with the rev-2 copies kept as `*.rev2.md`. Every trusted
delta is in Today / With this change form.

### R3.1 Each finding, and how it was resolved

| D5r2 | Resolution | Where |
|---|---|---|
| K-4 (`0 < bootLen` unsupplied) | premise `γ.cl.bootLen = γ.boot.length →` in C-I2-K's law **and C-I2's**. It can be met: `srvClusterOk` (in `srvRaftLogInv`, which `#Hsrl` and `memberRestartFacts` hold) has the equation, and `srvBootLogOk ps γ.boot` with `ps ≠ []` gives `γ.boot.length > 0`. `NewServerC_dist` needs no premise: its B.3 argument derives it from `#Hsrl` | c-i2 §3.2, §3.4; scratch §B.3 |
| K-5 (program side incomplete) | `srvWalProg h` widened to `Open.spec`'s inputs (lock token, `osCallPerm (callKey h.R h.r) 1`, `∃ q, osPathS h.R h.r (own q) h.jr`, `walAreaRes h.jr`). New `srvDataProg h dd`: the data root's path share and whole permission, and `DataDir`'s and `member/`'s name claims less the spine's (exact name sets are T8's). In C-I2-K, `NewServerC_dist` (`"Hdata"`) and arm (R). K-3's bullet corrected: `member/` belongs to no piece, and the WAL area (`walAreaOf dd`) lies outside `DataDir` | srvkeep §1.2–§1.3; c-i2 §3.2; scratch §B.5; srvkeep §2.4 |
| S-1 (unpinned `k.γ`) | `srvKeyF γ ρ`, `srvKeyR γ ρo νk h γm D` add `k.γ = γ` (trusted, `SrvKeep.lean`) | srvkeep §1.4; all texts |
| S-1′ (contradictory evidence) | fixed by S-1. Arms (F)/(R) state `memberRestartFacts` at the run's names; `memberKeepS`'s `□ ∀` form follows from it | srvkeep §2.1, §2.4 |
| K-6 (O-w false) | restated over `walHEq` (equal except `w`, `γ.γ`, `γ.γl`): the readers of `νk.ν.h` take the open handle `h'` with `walHEq νk.ν.h h'`. The alternative is `WalNames.h` as a durable descriptor; T2 chooses | c-i2 §3.3 |
| A-4 (error arm after `newRaftNode`) | **(a), kept in the slot.** `srvKeepAt`'s `.first n s e` arm, at `e = false ∧ n = true`, holds `srvLoopViewInit γ id νk h`, the loop's view half at its initial value. Reasons: a crash law reads only the slot, so a half returned to the caller would not help; the success path never visits `.first true _ false` (`be` precedes `n`); it records the Go fact (`raftNode.start` never ran) from which the crash law gets "no `Save`". (b) would need the crash-mode `Close` and the image payload at a first start, plus a split on durable `Save`s. `NewServer_dist`'s error-arm text is unchanged | srvkeep §1.5; scratch §A.0 |
| A-4′ | `memberFirstCrash.law` is provable at `.first true s false` with the new conjunct | srvkeep §2.3 |
| K-7 (`Hs` rows empty) | dropped from `wal.restartOkK`. New obligation O-hist (T2/T5): `specCK` gets the history's facts from `rnDurInvK` | c-i2 §3.3 |
| K-8 (placeholders) | rule recorded: `srvDurLoop` and `srvLoopViewInit` hold nothing keyed by `h.w`, `h.γ.γ`, `h.γ.γl`; `srvKb`/`srvKbc` read no `k.h`/`k.νk` | c-i2 §3.3 |
| K-9 (backend names not tied) | decided in the text: a one-shot name `γbk`. The precondition holds `srvKbPend γbk`, the commit point sets it, and the slot's open-backend arms hold `srvKbName γbk k.γb`. `bootOkRK` and the stop keep (`srvStop.keep (bk := γbk)`, P5's argument) expose `srvKbName γbk B`, so `kbClose.law` gets `B = k.γb` by agreement. It may be pre-chosen because pending excludes any caller-owned shot. This also closes §R2.5 Q2 (the first start's stop) | srvkeep §1.5; c-i2 §3.2–§3.3; scratch §A.10, §B |
| K-10 (commit point) | "the crash-mode open's commit point, the first write transaction (`dbCrashKeep_new`); before it `srvKbc` holds the closed file through the crash-mode `Open`'s atomic steps" | c-i2 §3.2 |
| T10 note | `memberBackend.law` uses only `dbCrash`'s output and `KB`, and drops the rest of `cmtBody` (`fkRd`, `cmtRegs … Dc`, the absorbed `dbHalf`). The tracked `cmtBody` keeps no old `dbHalf` beside the record's | scratch §A.9 item 7 |
| §R2.5 Q1 (incarnation) | closed by D5r2 (`Open`/`Repair` keep `ic`; K-4 excludes `Discard`) | c-i2 §3.3 |

### R3.2 Still open

1. `srvLoopViewInit` (T2): its exact text, `rnWalViewK`'s half at `rnDurK_alloc`'s initial view.
2. `srvDataProg`'s name sets (T8): `.except [member]`/`.except [snap]` against the spine's discarded claims, and the
   tie `osSpineDur jd [member] Jm` to the slot's `osSpineDur k.jd [member, snap] k.J`.
3. The one-shot resource for `srvKbPend`/`srvKbName` (an agreement over `backend.DBNames`), and P5's
   `(bk := γbk)` argument of `srvStop.keep`/`srvStopReq`.
4. O-w over `walHEq`, or `WalNames.h` as the durable descriptor (T2's choice); O-hist; O-vac; O-Kb; O-pure.
5. Carried: arm (W) coverage (§R2.5 Q7), F-B1's converse (Q8), `memberFirstCrash.law`'s `idIssueCrashStart` (Q5),
   the elaboration check (Q6), and the placeholders.

### R3.3 What needs a fresh delta review

- **Trusted, new in rev 3:**
  - `srvDataProg`, `srvKbPend`/`srvKbName`, and the widened `srvWalProg`;
  - the keys with `k.γ = γ`;
  - `srvKeepAt`'s two new conjuncts (`srvLoopViewInit` at `.first true _ false`; `srvKbName` at the open arms);
  - `srvKeepInv`'s new parameter.
  Check above all whether `srvLoopViewInit` and `srvKbName` can outlive a real crash or contradict a caller.
- **C-I2-K rev 3:** K-4's premise (also in C-I2), the narrowed `wal.restartOkK` (K-7), the precondition and error
  arm with `srvDataProg`/`srvKbPend`, and the K-10 commit-point wording.
- **`NewServer_dist`:** the binder `γbk`, `"Hbk"`, and `srvStop.keep (bk := γbk)`, as changes to the approved axiom.
- **`NewServerC_dist`:** `"Hdata"`, `"Hbk"`, and B.3's K-4 argument.
- **Untrusted, lighter:** srvkeep §2's rev-3 edits (the evidence rows, A-4′, the `γbk` existentials).

## Revision 4 (2026-11-26): review D5r3 applied

The input is review D5r3, `coordinator-notes/plans/review-d5r3-newserver-slot.md`: nothing unsound, and C-I2-K
sound with fixes. The scratch texts are updated in place, with the rev-3 copies kept as `*.rev3.md`.

| D5r3 | Resolution | Where |
|---|---|---|
| D-1 (must fix: `srvDataProg` took the data root's whole call permission; the slot's `snapDirKeep` and `srvKbc` hold shares of the same root key `callKey R (dd/member/snap) = dd`, so the preconditions were unsatisfiable) | `∃ qc, osCallPerm (callKey h.R dd) qc`, a share. `TouchDirAll`/`IsDirWriteable`/`CreateTmp` take any share. `srvWalProg`'s whole area-root permission stays: `walInv` holds none of it while the WAL is closed | srvkeep §1.3; c-i2 §3.2 |
| D-2 (coordinator's decision: the one-shot `γbk` cannot follow a backend swap, and `(bk := γbk)` would write that limit into the approved axiom's post) | `γbk` is a ghost variable: `srvKbVar γbk q (oB : Option DBNames)`, with `srvKbPend γbk := srvKbVar γbk 1 none`. At the commit point it becomes `some k.γb`, with one half in the slot's open arms and the other with the backend's holder (`srvStop.keep (bk := γbk)`, `bootOkRK`). A swap moves both halves. Choosing `γbk` before the call stays sound, because the precondition holds the whole. Condition: `Pos.Countable (Option backend.DBNames)` for `ghostVar`; otherwise T10's `bkKeepInvK` current-backend record replaces it, with the same shape | srvkeep §1.5; scratch §A, §B; c-i2 §3.3 |
| D-3 (T2's condition) | recorded: `srvLoopViewInit` is exactly `rnWalViewK νk vk0` at `rnDurK_alloc`'s initial view, with nothing keyed by `h.w`/`h.γ.γ`/`h.γ.γl`; `rnDurInvK`'s body turns `vk = vk0` into "no state record" (`HistOkK` at the empty history) | srvkeep §1.5; scratch §A.9 item 6 |
| D-4 (arm (F) needs `¬ clusterNoSnap`) | already a premise: `memberClOk C`'s last conjunct is `¬ clusterNoSnap C.γ.cl`, stated before `⊢` in `memberGen_boot.law` (and `{C.γ with reg := r}.cl = C.γ.cl`). The arm's comment and the notes now name it. The closed crash theorem takes it as its own premise (§R2.5 Q7) | srvkeep §2.4 |

**Still open:** the countability of `Option backend.DBNames`, or else `bkKeepInvK` (T10); and §R3.2's items 1–5.

**For review:** D-2's ghost variable (§1.5) and D-1's share (§1.3). Both are small.
