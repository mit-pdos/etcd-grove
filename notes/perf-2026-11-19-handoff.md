# perf 2026-11-19: handoff

## START HERE

Branch `perf/2026-11-19` (worktree `/shared/etcd-grove-incomingof`), off lean `1e4cb38613`; a
proof-perf pass on the timed full build `20261119-034111-1643293` (no extra full build). Proof bodies
only, plus one module move; no statement, definition, axiom or `sorry` changed.

Done (each module measured alone with `lean --setup`, before/after):

- `cf058ff379` genFrom: the `Input` struct kept flat after each field store (`isimp only at «in»`):
  101s -> 64s.
- `d517045b53` genFrom: the update branch's tests and `withPre` in sequence instead of one
  `repeat' (first | ...)` loop whose last round failed on every leaf: 52s -> 42s.
- `53e31ef649` LeaseRenew: `wp_join` at `if s.isLeader()`, the forwarding proved once instead of
  four times: 118s -> 33s.
- `a6e73a127c` **module move (other branches may need to merge it)**: `named_blank_clear`, the
  `leadTimeP`/`bemuP` `Fractional` instances and `authHistTie_alloc` moved unchanged from
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean` to the new
  `NewServerShared.lean` (with NewServer's imports); `NewServer` and `NewServerR` import it and
  `NewServerR` no longer imports `NewServer`. A branch that edits those declarations (lines
  ~138-210 of the old `NewServer.lean`) or `NewServerR`'s import of `NewServer` must apply its edit
  to `NewServerShared.lean` instead. Effect: the two 3-minute modules compile side by side; the
  longest import chain ~12m14s -> ~9m.

Checked at the land stop: the targeted importers build (26 leaves, 152 modules, green); the
fingerprint against lean `1e4cb38613`'s (87697 lines, 0 changed); `etc/tcb-report.py --check` (882
axioms, 4 sorries); the 69 collections `--check --reuse`; `etc/tier-check.py --check`.

Not done (leads):

- `applyEntryNormal.wp_proofOn`: `tail_on` expanded 5 times (~7.5s each); a join after the
  `apply.Apply` call needs an assertion with ~40 of the context's hypotheses and per-branch terms
  (`sa'`, `lt'`): declined for ~30s.
- `repeat' (first | A | B)` loops whose last round fails on every leaf (50 sites, mostly rafthttp,
  already helped by `first_callee`): profile before changing.
- The full build is limited by `LEAN_NUM_THREADS=4` (at most 4 compiles at once), not by the
  dependency graph: see STATUS's entry.

Build command: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-f55.json build
$(etc/importers.py --leaves --git 1e4cb38613 | grep -E '^(Proof|Spec|Code|GeneratedProof)\.')`.
