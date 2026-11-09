# Repair 4: the crossing laws at the current generation (F-raft-storage F1, F2; F-server-boot F1)

2026-11-09. Inputs: `F-raft-storage.md` (F1, F2), `F-server-boot.md` F1 (added by the coordinator),
`repair2-crash.md`, Perennial's `CrashAdequacy.lean`, `CrashToken.lean`, `Lifting.lean` (`HeapGS`,
`gooseBstateInterp`), OsFs's `Crash.lean` (`crashRest`).

## F-raft-storage F1 / F-server-boot F1: fixed

**The fix: the per-generation tokens are a token or the generation's `crashed`; their exclusivity
gives `crashed`, not `False`.** This is F-server-boot's option (a). I weakened the exclusivity laws
rather than dropping them: two tokens still give something, the generation's `crashed`. The
crossing laws' statements are unchanged.

Why this and not the alternatives:
- **Consuming an exclusive witness of the old occupancy** (F-raft-storage's (a), e.g.
  `nodeRunning n 1`) was rejected. While a node runs, `nodeRunning`'s fractions are with the
  threads that use it (Propose, Step, the Ready loop), so a crash frame cannot gather them. It would
  also add a premise to `disk_crash`'s realization that has no source.
- **A freshness premise** (option (b)) needs a Perennial change, which the brief excludes.
- The weakening also covers an `L'` that is not `hG`'s but reuses its crash name, or an earlier
  generation's (see "Reused crash names" below). Option (a) alone would not cover that case for 2e.

**Raft** (`Spec/go_etcd_io/raft/v3/Api.lean`):
- `exclusive.spec`'s vacancy clause changed from `nodeVacant γ id ∗ nodeVacant γ id ⊢ False` to
  `⊢ crashed`. A docstring now says why.
- `nodeVacant`'s docstring now reads "exclusive while the generation runs".
- The header's realization bullet is updated.
- The "Crashes and generations" header is rewritten:
  - The laws hold at every `L'`, and the header says how.
  - Why the occupancy witness was not taken.
  - **Realization:**
    - `nodeVacant` at `hG` is `occ(id, g) ∨ crashed@g`.
    - Raft's invariant holds, per id:
      - the record's authority at `cur`;
      - the set `S` of names whose token was handed out;
      - `crashed@g'` for every `g' ∈ S \ {cur}`;
      - the pool of tokens for the names outside `S`.
    - A crossing to `g'`:
      - moves the record;
      - gives the pool's token if `g'` is new;
      - otherwise gives `crashed@g'`: either the given one, or a recorded one.
    - The starts take the vacancy at their first step. That step owns `notCrashed@g`, which refutes
      the `crashed` disjunct. This is the same lifting fact the crash pass's realization already
      relied on.
- `raftState_gen`, `raftState_crash`: Changes lines (`verify-round: F-raft-storage F1`), statements
  unchanged.
- R-A8 N1's parenthetical is corrected. It said "two vacancies, refuted by `exclusive`", which is
  no longer true.

**Lean check** (scratch, `/home/ubuntu/.claude-E/jobs/b4c3a1d2/tmp/`):
- The reviewer's `rv_false` (`/tmp/rvchk/Eta2.lean`), run against the new `Api`, now fails at its
  last step: `iapply: cannot apply crashed to iprop(False)`.
- `F1check.lean` proves the same derivation's best result, `raftState γ id D ∗ crashed ⊢ |={⊤}=>
  crashed`, which is what the premise already holds.

**2e** (`ApiBoot.lean`):
- `diskIdle_excl` and `memberDisk_excl` now give `crashed` in place of `False`.
- `diskIdle_agree` gives `⌜k = k'⌝ ∨ crashed`: an idle token minted at a crash name used before
  carries no kind.
- The header's `diskState`/`diskIdle` realization bullet is rewritten:
  - `diskState` carries a per-disk generation record;
  - `diskIdle` is the token for `g` or `g`'s `crashed`, as raft's vacancy;
  - `NewServer`'s first step refutes the alternative.
- Changes lines added on `disk_crash`, `memberBoot_crash`, `memberJoin_crash`. These consume their
  token and give one back, so they are the identity at `L' = L`.

**Users checked:**
- No spec or snippet uses `Raft.exclusive`'s vacancy clause, `diskIdle_excl` or `memberDisk_excl`
  (grep).
- `diskIdle_agree` is named only by `ReqCrashRecover`'s Specs line. There `disk_crash`'s post
  already gives both predicates at one kind. The line now says so (`examples/specreq/etcdserverboot/
  boot.go`).
- `RestartNode.lean`'s Margin still said "a crash's vacancy is out of scope". It is updated: the
  vacancy comes from the crossing, and the start refutes `crashed`.
- `examples/specreq/raftnode/restart.go` `ReqRestartDurable` now allows a crossed crash in its
  Assumes. This also closes F-raft-storage's second-tier s1.

## Every generation-crossing law, checked at `L' = L`

| law | form | at `L' = L` | verdict |
|---|---|---|---|
| raft `global` | `⊣⊢` re-index | identity | sound |
| raft `raftState_gen` | consumes `raftState`, gives `raftState ∗ nodeVacant` | gives a second vacancy | **fixed** (vacancy = token ∨ `crashed`; `exclusive` gives `crashed`) |
| raft `raftState_crash` | consumes `readyEnter ∗ raftState` | same as `raftState_gen` | **fixed** for `L'`; **new finding N1 below (escalated)** |
| W0 `etcdState_gen`, `etcdLb_gen`, `urlsRight_gen`, `urlsReserve_gen`, `soleMember_gen`, `peerLeaseServed_gen` | `⊣⊢` re-index of global resources | identity; an exclusive one is converted, not copied | sound |
| W0 `envUpd_gen` | `⊢`, follows from `etcdState_gen` | identity | sound |
| 2e `srvNet_gen`, `srvEp_gen` | `⊣⊢` | identity | sound |
| 2e `memberBoot_crash`, `memberJoin_crash` | consumes the token, gives one | identity (raft's crossing inside) | sound once raft is fixed |
| 2e `disk_crash` | guarded by OsFs's `crashRest hG L'` (holds the old maps' `gAuth`, one-shot per file) | needs `crashRest hG hG`, which no real frame has | statement sound; the realization of `diskIdle` was not (F-server-boot F1), **fixed** as above |
| 2e `dataDirFresh_crash` | `crashRest`-guarded; consumes and gives | identity | sound |
| 2f `raftProto_gen` | equality of values | trivial | sound |
| 2f `peerAddr_gen`, `Http.protoAt_gen`, `Http.addrFree_gen` | `⊣⊢` | identity (`addrFree` converted, not copied) | sound |
| wal `walRecs_crash`, `walWriting_crash` | consume the records, give records `R'` (trusted) | the records may change, nothing minted | sound |
| snap `snapDbs_crash`, `snapSaving_crash` | consume `snapDbs`/`snapSaving ∗ snapGone`, give them back | nothing minted | sound |
| 4a `beCrash`, `beFile_crash` | `crashRest`-guarded; mint `beNoRevert`/`beFile` at `L'` from OsFs's `fileStart` | needs `crashRest hG hG` | sound |
| 4c `boltCrash` | `crashRest`-guarded | the same | sound |

**Reused crash names (second tier, recorded).** An `L''` can share `hG`'s crash name while having
the real `L'`'s OsFs names. `crashRest hG L''` is then the frame's real one.
- At such an `L''`, a realization keyed only by "the generation name, minted once" cannot mint again.
  That was raft's and 2e's stated realization, and it was wrong for every reused name, not only at
  `L' = L`.
- The token-or-`crashed` realization handles every case.
- The 4a, 4c and OsFs mints come from `crashRest`'s `fileStart` at the OsFs names, which the
  one-shot `crashRest` keeps unique. They need nothing more.

## F2 (F-raft-storage): fixed (snippet), recorded

- `examples/specreq/backend/commit.go` `ReqReopen` gets a new Assumes clause: the file at `path`
  exists with a durable name before the first open (`beFile path (some I)`, from `beFile_of` or an
  earlier generation's `Close`).
  - A file created by the first open has no durable name, so `backend.Close.spec` is not provable
    for it (the gap recorded in `backend__Close.lean` and top.md K6).
  - etcd's first boot's `member/snap/db` is such a file.
- `go vet`- and `gofmt`-clean.
- The open-question entry is requested below.

## New finding N1 (first tier, escalated: needs new client-visible ghost state)

**`raftState_crash.spec` is not realizable as stated, whatever `L'` is. Its evidence can be
forged.**
- `readyEnter n γ id st b dl` is a transparent wand whose premise includes `nodeRunning n q`.
  - `node.Stop`'s post gives the persistent `nodeStopped n`.
  - `exclusive` has `nodeRunning n q ∗ nodeStopped n ⊢ False`.
  - So a client that has stopped any node `n` proves `readyEnter n γ id st b dl` for **any** batch
    `b`: the wand's premise is refutable.
  - The law then gives `raftState@L' D'`, where `D'` comes from `D.next b` for a batch raft never
    made: a second vote in the same term, or entries never proposed under a commit.
  - In the next generation a program can turn that into a safety violation against `committedLb`.
- Raft's proof also cannot inspect a wand without firing it. Firing mints the batch's `msgSent`
  (global and persistent), after which rolling back to a crash prefix of the batch is unsafe.
- The issue is pre-existing: round 3's statement had the same evidence.

**Proposed** (not done: it is new client-visible ghost state in raft's user-approved node API, so it
goes to the user):
- An opaque **persistent** `readyBatch n γ st b`, raft's record that it handed out `b` at `st`.
- `readyGot` gives it.
- `raftState_crash` takes it in place of `readyEnter`. `raftState` at `st.durable` already says the
  batch was not entered.
- 2e's disk realization deposits it beside the `readyEnter` it fires.

The law's docstring now states this as **Open (soundness, escalated)**.

## Requests

- **Coordinator / open questions:**
  - F2: add an entry "4a `backend.Close` is not provable for a file created in the same generation
    (no durable name: `nonissues/bbolt-create-dir-not-synced.md`, C2's root). Fix: `beFile` with a
    name state (a `named` flag, `beFile_crash` with an `o' = none ∧ ¬named` case), or keep it
    excluded (`ReqReopen`'s Assumes)."
  - N1: the `readyBatch` decision (above).
- **`notes/perennial-changes.md`** (coordinator, optional): F-raft-storage's option (b), "the crash
  frame gets a one-shot witness of `L → L'`, or a fresh-name fact", as the general fix.
  - It would let per-generation tokens stay exclusive (`⊢ False`).
  - Its realizations would not need the `crashed` disjunct.
  - Not needed for soundness now.
- **2e owner:** after these edits, the `diskIdle_excl`, `diskIdle_agree` and `memberDisk_excl` laws
  are mine. F-server-boot F2-F5 are untouched, as instructed.

## New decisions

1. **Per-generation tokens are a token or the generation's `crashed`.** Their exclusivity gives
   `crashed` (raft's vacancy; 2e's `diskIdle`, `memberDisk`), and `diskIdle_agree` gives
   `⌜k = k'⌝ ∨ crashed`.
   - A running program never sees the alternative: a step refutes it.
   - What it costs: a client cannot refute two vacancies in pure reasoning, only at a step. No
     client did so.
2. **N1 is escalated, not fixed.** The fix adds a client-visible opaque to `readyGot`.

## Build

- `etc/specs-build.sh Spec.go_etcd_io.raft.v3.Api Spec.go_etcd_io.raft.v3.RestartNode
  Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot`: **OK**.
- Every `Spec` importer of raft's `Api` (`etc/importers.py --leaves`, 719 leaves; ApiBoot's
  importers among them): **OK (719 modules)**.
- Snippets `raftnode`, `backend`, `etcdserverboot`: `go vet` clean, `gofmt -l` empty.
