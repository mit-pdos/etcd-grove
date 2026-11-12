# out_size: handoff

Worktree `/shared/etcd-grove-outsize`, branch `out-size` (off lean `2004e1b2d1`). Scope:
`/shared/tmp/out-size/scope.md` (decisions D1-D7 approved, recorded in the worktree's `questions.md`,
untracked, with the forms decided). Coordinator: etcd-grove-81 (rules:
`/shared/tmp/coord-81/common-rules.md`). Goal: delete the `sorry` in `out_size`
(`Proof/go_etcd_io/raft/v3/MsgOut.lean`), its text unchanged; tcb 5 → 4.

## Build

```
export TMPDIR=/shared/tmp
# targeted (no flock):
systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json <modules>
# full:
timeout 14000 flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G \
  lake build --packages=/shared/tmp/manifest-ddc.json
LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py -q -a FILE...
```

Targets for raft's log: `etc/importers.py --uses Huents --uses Hents --uses ownUnstable --uses
unstableOf Proof/go_etcd_io/raft/v3/InvRaftlog.lean` (list in `/shared/tmp/out-size/p1-raft.txt`).

## Done

- **C1 (P0 vocabulary, P1 log)**, 2026-11-12:
  - `PbSized.lean` (new, importable): `entBytes`/`entSizeOk` (moved from `MsgOut`), `entRZ sz l e`
    (a frozen entry at a content, `entSizeOk` when `sz`), `entsPtsZ`/`entsROz` and the slicing laws
    (`entsBigZ_*`, `entsPtsZ_*`), the `sz = false` bridges (`entsPts_entsPtsZ`, `entsPtsZ_false`,
    `ite_entsPtsZ_false`).
  - `PbContent`: `entRoC` and the entry lemmas generic in `hlc`.
  - `UnstableSt.sz` (default `false`); `ownUnstable` holds `entsROz us.sz`; `unstableOf` passes
    `false`; `ownRaftLog`/`ownRaftLogW` hold `entsROz false` (the node's flag `LogState.sz` comes at
    P4).
  - unstable specs: `nextEntries`/`slice` posts `entsROz us.sz`, `truncateAndAppend` over
    `entsPtsZ us.sz`, `restore` keeps `sz`. raftLog's specs unchanged (`append` converts with
    `entsPts_entsPtsZ`; `slice`, `nextUnstableEnts` weaken with `entsROz_entsRO`).

- **C2 (statements)**, 2026-11-12, commit `909347aa5e`, **waiting for etcd-grove-81's review** of
  `/shared/tmp/out-size/freeze-c2.md` (the Freeze package: old → new, changes in meaning, the D4
  axioms, the restart clause, Go evidence). Written: `outSetR` sized (and `out_size` proved from it),
  `raftOutInv_insert`'s premise, `entsPtsC`/`entsCut` (PbSized), `StorNames.sz`, `isStorageP`/
  `isStorageWith` with `sz` and the cut, `isStorage` at `γ.maxData.isSome`, `certLink`'s pin
  `sn.sz = γ.maxData.isSome`, `MemStorNames.sz`, `NewMemoryStorage`/`Append`/`Entries` specs,
  `memStorage_isStorage`'s `hsz`, `isRNMemStor` over `entsROz true`. Builds: the raft API closure
  (`MemstorageApi InvNodeRule MsgOutIns InvApi` + the specs); `isRNMemStor` checked in a scratch
  module (`/shared/tmp/out-size/c2/scratch/RNCheck.lean`). Branch-only `sorry`s: `entsPtsC_entsPtsZ`,
  `entsPtsZ_entsPtsC`, `memStorage_isStorage`, the size fact at `entsOut_insert`/`msgOutR_intro`.

- **C2 review addressed**, 2026-11-12, commit `6465f380e0`: Freeze revision 2 (same path). `bootOk`
  (`InvBoot.lean`) and `NodeStartSpec`'s pre gain `⌜γs.sz = true⌝`; `srvMem_bootStorage` gains `hsz`
  (user-approved). `entsCutMax := 2^20`, `entBytesMax := 2^31` (`@[word_unfold]`, PbSized) in the
  contracts, `entSizeOk`, the starters' premise. `out_size`'s docstring rewritten. **C3 approved to
  start** (raft fully proved, P2-P6): next checkpoint C3. NodeStart and InvBoot may be edited; tell
  etcd-grove-81 before touching anything else outside raft.

- **C3 in progress**, 2026-11-12 (commits `18142fa3a5`, then the P2 commit after it):
  - `PbSized`: the bridges `entsPtsC_entsPtsZ`/`entsPtsZ_entsPtsC` proved; `entRZ_of_struct` (a fresh
    entry with no unknown fields, frozen sized: use it for every entry raft allocates); the
    `entsBigC_*` list laws; `entsPts_entsPtsC`/`entsPtsC_entsPts` (unsized bridges for callers).
  - `InvStorage`: `isStorageP_unsize`, `entsPtsC_unsize`; `memStorage_isStorage` proved.
  - MemoryStorage: `memstorageFields ms sz σ` holds `entsROz sz` (helper specs `{first,last}Index`
    take `∀ sz`); all its proofs and `NewMemoryStorage` (`γs.sz` the caller's) check.
  - **B1 done** (decided by etcd-grove-81): `Proof/go_etcd_io/raft/v3/PbEntryType.lean` holds
    `entDecode`/`EntWireOk`/`pbEntry` (from rafthttp `PbMessage`), all of rafthttp's
    `PerTypeEntry.lean` (deleted) and the `pbEntryC_*` simp lemmas (from `PerTypeMessage`); texts
    unchanged, `pbEntryC_reg` still at `HasLC.hasLC`.
  - rafthttp `Net.lean`'s pure `sizePure` section (varint/entry/message size lemmas) moved to
    `MsgOut.lean` (needed by raft's cut); new `entrySize_lt_of_ok`. `msgSizeOk`'s `2^31`s are
    `entBytesMax` (decided).
  - `limitSize`/`entsSize`: specs at contents (`entsPtsC sz`), `limitSize` with the cut
    (`sz → maxSize ≤ entsCutMax → entsCut`), `entsSize` exact (`sz → sum < 2^64 → n = sum`); proofs on
    `proto.SizePb` at `pbEntryC`, at `HasLC.hasLC`. Helpers `w64_add_exact`,
    `entrySize_sum_take_succ` (limitSize.lean). Pitfall: `word` inside these proofs can produce a
    kernel "application type mismatch" (auxiliary-proof abstraction with an unused `sz`): move the
    arithmetic into a pure lemma.
  - `etc/link-lean-first-raft.txt`: `proto_SizePb` replaces `proto_SizeEntry`; server list
    `proto_SizePb: @`; both Links regenerated (17 raft results moved to the `HasLC.hasLC` section:
    acceptable, etcd-grove-81 asked to be told if it spread badly).
  - `MemoryStorage.Entries` (cut from `limitSize`) and `raftLog.slice` (unsized bridges) check.
  - **Build 1** (commit `5f2759dcb5`; raft Link + kv/kvreconf/kvdurable Links;
    `/shared/tmp/out-size/c3-build1.log`) fails in: `raftLog__firstIndex:36` (an `isStorageWith`
    use: pass `ls.sn.sz`), `raft__Step/MsgStorageApplyResp:252` (an `entsRO`/`entsPtsC` frame),
    `RawNode__acceptReady:668` (`entsSize` at contents: bridge as in `raftLog.slice`), `StartNode`
    and `RestartNode` (`certLink`'s new conjunct at :190/:204 and :210/:224, `storKeyNames`' tuple
    `sn.sz` at :451/:633, `isStorage` at `γ.maxData.isSome` at :467/:674: the C2 repairs),
    kv `KVStorageInstance`/`NewStorage`, kvreconf `KvrStorageApi`, kvdurable `KdStorageApi`/
    `newStorage`/`openStorage`/`Replica__run` (`hmd`; `NewMemoryStorage`'s new `∀ sz` and
    `⌜γs.sz = sz⌝`, pass `sz := false`; `Entries`' post at contents, `entsPtsC_entsPts`;
    `Append` at `entsPtsZ false`, `entsPts_entsPtsZ`). Everything else in raft built.
  - **Next:** fix those, then
    kv storage instances (`hmd`), `raft.Step`/`RawNode.acceptReady`'s `entsSize` calls (bridges as in
    `raftLog.slice`), `Results.lean`'s `#print axioms proto.wp_SizeEntry`; then delete
    `proto.SizeEntry` (Spec+Proof, D4) when no user is left; then P3 (outbox `msgQC`, `raft.send`
    and callers, `outSetR` premise discharge), P4 (`LogState.sz`, step pipeline, `appendEntry`
    onto `ClonePb` (`pbEntryC`), then delete `proto.CloneEntry`), P5 (proposals, ConfChange via
    the B2 instances), P6. `raftLog.slice`/`entries` must return `entsPtsC` sized and cut for the
    `MsgApp` bound: needs the unstable entries sized (`LogState.sz`, P4).
  - **B2 (approved by etcd-grove-81, hard stop before landing):** per-type `ConfChange` and
    `ConfChangeV2` instances in `PbEntryType`'s pattern (an opaque encoder, its Go-tested fact
    `proto.Size` = formula + round trip, a registration; each: about +4 axioms) and a pure lemma
    size ≤ `ccSize + 64`. Write them with the Go tests in a small Freeze package
    (`/shared/tmp/out-size/freeze-b2.md`) for etcd-grove-81's axiom review; P2-P4 go on meanwhile.

## P7 items (from the C2 review; resolve and re-review with the `axiom` skill before P7 lands)

freeze-c2.md §4: MAJ-1 (`walSaveOk` in `bootstrapRestartContract`'s premise), MAJ-2 (`srvDiskImage`'s
`srvFiles … true`, HardStop/restart specs' stronger post, `rnDurInv`/`walAsViewed` at `true`,
`wal.bootOk_start` no longer unsizing), MIN-3 (`srvFiles`' provenance docstring; `maxData = 2^30` rests
on the MaxRequestBytes config premise), MIN-5 (second restart: narrowing recorded), m4
(`bootstrappedWAL.MemoryStorage.spec` `∀ sz`), m5 (axiom review after P2's `memstorageFields`),
`NodeStart.lean:658`'s `hsz` from `bootOkR`.

## Next, in order (Scope §4)

C1 LANDED: lean `ec6fd114d2` (2026-11-12, gates all passed, with etcd-grove-81's `gates.sh` retry
commit `3a986545ae` cherry-picked; not pushed). The branch continues from there (merge lean first).

1. **C2, the statements Freeze (hard stop for etcd-grove-81's review).** Write the texts with the
   proofs left open (`sorry` on the branch only, never landed), and a Freeze package in
   `/shared/tmp/out-size/freeze-c2.md`. Design sketched at hand-off (not yet written in Lean):
   - `outSetR` (MsgOut): `ghostMapElem … ∗ ⌜∀ b, γ.maxData = some b → outSizeOk x⌝`; `out_size`
     proved by `unfold outSetR; iintro ⟨-, %H⟩; ipureintro; exact H _`; `raftOutInv_insert` takes
     `⌜∀ b, γ.maxData = some b → outSizeOk x⌝` (its callers `entsOut_insert`/`msgOuts_insert`,
     `InvApi.lean` ~2370-2470, then need the fact: P3).
   - Vocabulary for the cut (PbSized): a list form `entsPtsC sz s dq cs := ∃ ls, s ↦*{dq} ls ∗
     ([∗list] l;c ∈ ls;cs, entRoC l c) ∗ ⌜sz = true → ∀ c ∈ cs, entSizeOk c⌝`, bridges to/from
     `entsPtsZ sz s dq (cs.map EntryC.model)` (the back direction by induction, as
     `entsRO_entsRoC`), and `entsCut (maxSize : w64) cs := cs.length = 1 ∨ (cs.map entrySize).sum ≤
     uint.nat maxSize`.
   - Storage contract (`InvStorage`): a flag `sz : Bool` on `isStorageP` and `isStorageWith`;
     `#HEntries`' success post `∃ cs, entsPtsC sz s □ cs ∗ ⌜cs.map EntryC.model = es ∧ (sz = true →
     uint.nat maxSize ≤ 2^20 → entsCut maxSize cs)⌝` (at `sz = false` equivalent to today's
     `entsRO s es`). Proposal: the node API's `isStorage γ K st` (`InvNodeRule.lean:618`) passes
     `sz := γ.maxData.isSome`, so `StartNode`/`RestartNode`/`setupNode` keep their text and their
     meaning gains "sized when `maxData ≠ none`" (kv: `maxData = none`, no change); say so in the
     Freeze as the r3 §3/§5 starters' change.
   - `MemoryStorage`: `MemStorNames` gains `sz : Bool` (ghost, chosen at `NewMemoryStorage`, whose
     post then says `γs.sz = sz` for a caller-chosen `sz`); `MemoryStorage.Append.spec` takes and
     gives back `entsPtsZ γs.sz s dq es` (no cut needed on `Append`); `memStorInvP`'s `Hents`
     (`InvMemstorage.lean` ~590) holds `entsROz γs.sz`; `memStorage_isStorageP` at `sz := γs.sz`
     (Entries' cut through `limitSize`, whose spec gains the content cut onto `SizePb`: P2).
   - `isRNMemStor` (server `InvRaftNode.lean:1558`): `Append` takes `sl ↦*□ esL` with each entry at a
     content with `entSizeOk` (in place of `entriesAt esL es`); server file: tell etcd-grove-81 before
     editing.
   - The restart clause (D5, option B): write its text in the Freeze package only (P7 is sequenced
     after the next restart landing, D7; `InvRestart.lean` is the restart owner's), with the
     `axiom`-skill review there.
2. P2-P5 (raft), C3; P6, P7 (tell etcd-grove-81 before P7: D7), C4; C5. Known repairs from C2: the
   proofs building `StorNames`/the `storKeyNames` tuple (`StartNode.lean:447`, `RestartNode.lean:629`,
   and `certLink`'s new conjunct at `StartNode.lean:186`/`RestartNode.lean:200`), `NewMemoryStorage`'s
   anonymous `MemStorNames` constructor, `memstorageFields`' `Hents` (`entsROz γs.sz`, needs a `sz`
   argument), every `HEntries` reader (`raftLog__slice`, ...), kv's storage instances (`sz = false`),
   `isRNMemStor_of_memstorage` (`entsPtsZ_true`); the server's callers of the starters' premise now
   `≤ entsCutMax` (`word` unfolds it); server users of `entSizeOk` (`WalApi`, `WalRecs`, `InvBoot`,
   `InvRaftNode`) now see `entBytesMax`; `NewServer`'s proof passes `bootOk`'s `Hγsz` to
   `NodeStartSpec`; the `InvBoot`/`NodeStart` edits are not built yet (server).
   Suggested C3 order: P2 (`memstorageFields` `sz` + `Hents`, `MemoryStorage__{Append,Entries}`,
   `NewMemoryStorage`, `limitSize`/`entsSize` onto `SizePb` with the cut, the two `PbSized` bridges,
   `memStorage_isStorage`, kv instances with `hmd`), then a raft build to list the remaining breakage
   (`etc/importers.py --uses isStorageWith --uses HEntries ...`), P3-P5, P6.

## Pitfalls

- `notes/status-history.md` is append-only.
- Never `GOWORK=off` in the shell running `etc/land.sh`/`gates.sh`/`goose.py`.
- Python replace of a 4-space line also matches inside a 6-space one: anchor replacements.
