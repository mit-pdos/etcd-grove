# The part `RaftNoAx/`: raft without hand-written axioms

Started 2026-11-17 (branch `raft-noax`). The goal (the user's): a closed theorem like
`raft_kvdurable_porcupine_safe` whose `#print axioms` shows only Lean's three axioms and the type
axioms Goose emits for untranslatable declarations, for a modified raft (the `proto.Clone/Size/
Marshal/Unmarshal` calls replaced by hand-written raftpb functions, `fmt.Errorf` by `errors.New`,
no `DescribeConfChange` in stepLeader: a fork branch) and a modified kvdurable
(`examples/raft/kvdurablenoax`, a Go module of its own). The etcd server keeps the real raft, so the
modified one lives in a part (module root) of its own, `RaftNoAx/`, as the witness experiment lives
in `RaftWitness/` (`notes/raft-witness.md`).

This file records how the part is made. Stage 1 (this one): the part as a faithful renamed copy of
the main tree, from the unmodified raft, giving the same theorem with the same axioms. Then the
modified code is swapped in.

## How the part is made

Four generators, each rerunnable (`--check` for each in CI or the gates):

1. **Translations** (`etc/goose.py`): project `raft-noax` (raft's packages and configuration, at
   `RAFT_NOAX_REV`, configured by `RaftNoAx/Code/go_etcd_io/raft/**.toml`), project
   `kvdurable-noax` (`KVDURABLE_NOAX_DIR`, Go package `KVDURABLE_NOAX_PKG`), and two parts of
   existing projects into `RaftNoAx`: kvreconf's store (project kvreconf: the kvdurable proofs use
   kvreconf's shared proofs, `Base`, `Defs`, ..., which name its translation, which imports raft) and
   `walpb` (project etcd: `Proof/google_golang_org/protobuf/proto/PbSchema.lean`, which raft's message
   invariant `InvPb` imports, names walpb's two registered types, and walpb's translation imports
   raftpb). Each is the main tree's translation with its imports of the part's modules prefixed
   (checked: identical up to `RaftNoAx.`).
2. **Copies** (`etc/copy-part.py`, new): the import closure of the main tree's
   `Proof/.../examples/raft/kvdurable/Results.lean`; every module of it that transitively imports a
   translation the part has (raft's, kvdurable's, kvreconf's, walpb's) is in the part, every other
   module is the main tree's, imported as it is. The script copies those that no other generator
   writes (the `Spec/`/`Proof/` modules, the `TrustedCode/`/`ManualProof/` of the translated
   packages, their `Code/**.toml`), prefixing the imports of the part's modules and adding a first
   line naming the source. A part file without that first line is the part's own (a copy that stopped
   following the main tree on purpose: delete the line when editing it); the script neither writes
   nor checks it. `--list` prints every module of the part with who writes it.
3. **Package initializers** (`etc/gen-init.py`): `PART_ROOT`/`PART_INITS` generalized to `PARTS`
   (part root -> its packages, and the module prefixes whose imports are the part's); RaftWitness's
   output unchanged (`--check`). RaftNoAx's: RaftWitness's list plus `durable` and `trusted_proph`,
   and `PkgInitExt`.
4. **Links** (`etc/gen-link.py`): `--raft-noax` and `--kvdurable-noax` (`PART_ALIASES`), which link
   as `--raft`/`--kvdurable` (every table of those modes), from `etc/link-lean-first-raft-noax.txt`
   and `-kvdurable-noax.txt` (for now copies of the main lists), with the part's specs in place of
   the main tree's. The outputs are the main Links up to the prefix and the header.

Also: `lakefile.toml` (lean_lib `RaftNoAx`, in `defaultTargets`), `etc/tcb-collections/raft-noax.txt`,
CI and `etc/gates.sh` (`etc/copy-part.py --check`). `etc/proof_roots.py` finds the part through
`etc/goose.py` (no change).

To regenerate after the main tree moves:

    etc/goose.py --project raft-noax --project kvdurable-noax --project kvreconf --project etcd
    etc/copy-part.py
    etc/gen-init.py
    etc/gen-link.py --raft-noax > RaftNoAx/Proof/go_etcd_io/raft/v3/Link.lean
    etc/gen-link.py --kvdurable-noax > RaftNoAx/Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/Link.lean

## What the part holds (stage 1, 2026-11-17)

The closure of kvdurable's `Results` has 1599 modules of this repository; 1255 of them reach a
translation the part has, so the part has them (the other 344 are the main tree's: lintest's and
porcupine's proofs, `durable`'s, `fmt`/`context` Links, `ProjSimps`, ...). 1261 files, 313k lines:

| written by | files | lines | what |
|---|---|---|---|
| etc/copy-part.py | 775 + 441 | 233.6k + 26.9k | `Proof/`, `Spec/`: raft's (603 + 321), kvdurable's (133 + 105), kvreconf's shared proofs (23), the `proto` trust boundary (10 + 9), and the few standard-library specs that reach raft (`slices.Sort`, `strings.Join`, `fmt.Sprintf`, `crypto/rand.Int`, `math/big`: the copies RaftWitness has too) |
| etc/copy-part.py | 2 + 2 + 5 | 0.3k | raft's and walpb's `TrustedCode`/`ManualProof`, the Goose configuration (raft's four `.toml`, walpb's) |
| etc/goose.py | 8 + 12 | 48.3k | `Code/`, `GeneratedProof/`: raft, kvdurable, kvreconf, walpb |
| etc/gen-init.py | 14 | 1.5k | the initializers of RaftWitness's list, `durable`'s, `trusted_proph`'s, `PkgInitExt` |
| etc/gen-link.py | 2 | 2.3k | raft's and kvdurable's `Link.lean` |

kvdurable's own `Init.lean` and `PkgTable.lean` (gen-init's in the main tree) are copies: correct
while the part's kvdurable imports the same packages (below).

**Built** (from a seeded `.lake` with the main tree up to date): `lake build
RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Results`, 3837 jobs, 12m22s
wall on the shared 24 cores, 7650 s of CPU, peak 2.9 GB per process; `.lake/build` grew by 3.2 GB
(2.0 GB `lib/lean/RaftNoAx`, 1.0 GB `ir/RaftNoAx`).

**The same theorem, the same axioms.** The `#print axioms` of all 17 results of the part's
`Results.lean` are those of the main tree's, constant for constant (328 for
`raft_kvdurable_porcupine_safe`: the 13 axioms of this repository, `DescribeConfChange.wp_proof`,
`ccDecodeV2_nil`, `entryEncC_ok`, `fmt.Errorf.wp_proof`, `pbEntryC_reg`, `proto.{CloneConfState,
ClonePb,CloneSnapshot,MarshalConfChange,MarshalConfChangeV2,SizePb,UnmarshalConfChange,
UnmarshalConfChangeV2}.wp_proof`; Perennial's `time.Now.wp_proof`; Lean's three; the rest Goose's type
axioms). The names are the same because the part's copies declare the main tree's names (the
theorem keeps its name, `Perennial.EtcdGrove.raft_kvdurable_porcupine_safe`; nothing imports both
trees). `etc/tcb-collections/raft-noax.txt`'s baseline is that list (written by hand: `tcb-report.py`
wants every root up to date, and the seed was stale in unrelated packages; rerun `--check --update`
after a full build).

## Switching to the modified code

**A new raft rev** (the fork's noax branch):
1. `RAFT_NOAX_REV` in `etc/goose.py` (and `GO_MOD_PINS` for `examples/raft/kvdurablenoax/go.mod`,
   which replaces raft by that rev: add the line, as kvwitness's);
2. `etc/goose.py --project raft-noax`; if the Goose configuration must change (a new raftpb function
   kept or trusted), edit `RaftNoAx/Code/go_etcd_io/raft/**.toml` and delete its first line (it is
   then the part's own);
3. the proofs: the files that change stop being copies (delete their first line, edit them); new
   specs and proofs (the hand-written raftpb functions') are the part's own files; the link list
   `etc/link-lean-first-raft-noax.txt` changes with the callees; regenerate the Link.

**The real kvdurablenoax module**:
1. in `etc/goose.py`, `KVDURABLE_NOAX_DIR = os.path.join("examples", "raft", "kvdurablenoax")`,
   `KVDURABLE_NOAX_PKG = "github.com/mit-pdos/etcd-grove/examples/raft/kvdurablenoax"` (its Go path);
2. `etc/goose.py --project kvdurable-noax`; delete the old `RaftNoAx/{Code,GeneratedProof}/.../kvdurable*`;
3. `etc/copy-part.py`: `RENAME` (from `KVDURABLE_NOAX_PKG`) then renames the copied kvdurable proofs'
   package (namespace `github_com.mit_pdos.etcd_grove.examples.raft.kvdurable` and its directory) to
   the new one, and deletes the stale copies; the proof namespace `raft_kvdurable` and the theorem's
   name are unchanged. No copy names the package by a short form (`kvdurable.X` after an
   `open ...examples.raft`; checked 2026-11-17: the 1030 mentions are all of the full path);
4. `etc/gen-init.py`'s `PARTS['RaftNoAx']` prefixes name kvdurable's paths: add kvdurablenoax's;
   kvdurable's `Init.lean`/`PkgTable.lean` are copies, right only if the new package imports the same
   packages: if not (e.g. `errors` for `fmt`), generate them from the part's translation as
   `wt_inits` does for `WalTester/`;
5. `etc/gen-link.py --kvdurable-noax`: its output path (the docstring line the gates read) moves to
   the new directory, the list may need the new package's names;
6. `etc/tcb-collections/raft-noax.txt`'s `roots` line: the new directory.
