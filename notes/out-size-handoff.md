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
2. P2-P5 (raft), C3; P6, P7 (tell etcd-grove-81 before P7: D7), C4; C5.

## Pitfalls

- `notes/status-history.md` is append-only.
- Never `GOWORK=off` in the shell running `etc/land.sh`/`gates.sh`/`goose.py`.
- Python replace of a 4-space line also matches inside a 6-space one: anchor replacements.
