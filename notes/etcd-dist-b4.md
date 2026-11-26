# etcd_safe B4: a crash-aware keep slot in `NewServer`'s specs (design, 2026-11-26)

Branch `etcd-safe-crash-b4/2026-11-26`, from `etcd-safe-crash-s0/2026-11-26` @9e66b4dbac. Helper of the
etcd_safe lead. **Design only: no Lean edit for B4.** The design changes S0 statements and needs trusted
changes besides `NewServer_dist`'s text, so it went to the lead before any re-proof (§7). The decisions taken
are in §7a. The re-proof waits on T10, T6 and kaashoek's case (D-B4-7); §8 is the handoff, §9 the layering. Paths: `P/` = `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/`,
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
  `γl` is fixed by the view. See D-B4-6.

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
5. `memberFirst_of_share.law` / `memberFirst`: D-B4-6's decision on the lessor slot.

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
* **D-B4-6. The lessor slot at a first start.** `Hlslot` at the view's `γl` is consumed by `NewLessor` and
  cannot come back after a crash. Recommended for the crash class (lease mode `.none`): `NewServer_dist`
  allocates its own lessor name there, as `specG` does (`lessorSlot_alloc`), with `Hlslot` only when
  `lm ≠ .none`. That is a further change to `NewServer_dist`'s text, in the same packet. Alternative: a
  generation-indexed lessor slot (new ghost design).
* **D-B4-7. Order.** T10's `KeepB` (concrete, an invariant) and T6's first-start `snapDirKeep` come first.
  Then this task re-proves the specs (§4) after kaashoek's `σ.commit < i` case lands. Until then the dist
  restatement can only be drafted, as text, which is the scratch file.

## 7a. Decisions taken (the lead, with the coordinator, 2026-11-26)

* **Decided as recommended:** D-B4-1 to D-B4-5 and D-B4-7.
* **D-B4-6: drafted as recommended.** At `lm = .none`, `NewServer_dist` allocates its own lessor name
  (`lessorSlot_alloc`, as `specG`), and takes `Hlslot` only when `lm ≠ .none`. It is a trusted text change,
  so it stays a draft until Upamanyu decides it with the crash packet.
* **The re-proof waits on its dependencies** (D-B4-7): T10's concrete `KeepB`, T6's first-start
  `snapDirKeep`, and kaashoek's `σ.commit < i` case.

## 8. Handoff (this session's end state)

* `NewServer_dist`'s and `NewServerC_dist`'s final draft text (B4 + D-B4-6), with the slot's docstring
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