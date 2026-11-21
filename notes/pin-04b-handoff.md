# pin-04b handoff (2026-11-21) — STOPPED by the coordinator, not built

## START HERE

Stopped: the Perennial pin is a single-writer resource claimed elsewhere (GitHub issue mit-pdos/etcd-grove#9,
branch `pinbump/perennial-ncfupd-2026-11-21`, pinning `60800ea5e`; our `04b42a139` builds on it). Redo the
regenerated part on top of that branch once it lands; the hand-written part should carry over as is.

Task: move the pin `c8e356cb1` -> `04b42a139` (Perennial fix-semantics Cases 39/40: goose folds untyped-rune
constant expressions; `UntypedIntSemantics.convert_untyped_int_to_string`, `string(c)` is `go.runeString c`;
`string(b)` of a byte is `go.runeString b`) and delete the local class `UntypedRuneSemantics`.

**Nothing is built.** Not run: the full build, gates, tcb-report, gen-interface.

### Commit 1: hand-written (keep)
- `Proof/internal/filepathlite/UntypedRune.lean` deleted.
- `FromSlash.lean`, `Base.lean`, `path/filepath/join.lean`: no `[UntypedRuneSemantics]`, no import of it;
  `untypedRuneToString_ascii 47 ..` replaced by `(by decide : go.runeString 47 = [W8 47])` (`decide` and `rfl`
  checked against Perennial `04b42a139` with `lake env lean`; the proofs themselves not checked).
- etcdserver `RnNewStorageLinked.lean` (section variable), `Results.lean` (`new_storage_contract` loses the
  instance argument: a strengthening of a non-closed result; report it), `WalApi.lean` (doc), `etc/gen-link.py`
  (comment), `notes/perennial-changes.md` (entry marked DONE; `rnNewStorageOk` stays: what is left is `os`'s
  `fileStat`/`file` field assumptions; `bufio.opaqueInitsOk` stays: `errorRune`'s initializer is untranslated).
- `lakefile.toml`, `lake-manifest.json`: rev `04b42a1392a77e210f6031f02a05239c901648c2` (redo for the real pin).

### Commit 2: regenerated (redo on the new pin)
- `etc/goose.py --perennial /shared/perennial-04b42a139` (needs `PATH=/usr/local/go/bin:$PATH`): two lines changed,
  `Code/internal/filepathlite.lean` (`FromSlash`: `Separator == '/'` is `#true`) and
  `Net/Code/models_lab/jsoncodec.lean` (`lower`: `'a'-'A'` is `#(W8 32)`).
- `etc/gen-init.py`: 38 `PkgTable.lean` (Perennial's `strings` now imports `sync` and `io`).
- `etc/gen-link.py --walfs`, `--durable`, `--wal-tester` (written to their Links; `[UntypedRuneSemantics]` gone;
  the tester Link also gains `strings`/`io` `Assumptions` variables).
- `copy-part.py`, `gen-raft-tla.py`, `gen-specs-pkginit.py` `--check`: up to date.

### Next
Merge lean with the new pin, rerun the generators above, seed `.lake/build`, full build, gates, tcb
(`etc/tcb-baseline.txt` at 3ac6cb4031: 532 axioms, 0 sorries; expected unchanged: the class was a hypothesis,
not an axiom), STATUS "Last updated" entry (not yet written).
