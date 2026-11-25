# The part `RaftNoAx/`: raft without hand-written axioms

Started 2026-11-17 (branch `raft-noax`). The goal (the user's): a closed theorem like
`raft_kvdurable_porcupine_safe` whose `#print axioms` shows only Lean's three axioms and the type
axioms Goose emits for untranslatable declarations, for a modified raft (the `proto.Clone/Size/
Marshal/Unmarshal` calls replaced by hand-written raftpb functions, `fmt.Errorf` by `errors.New`,
no `DescribeConfChange` in stepLeader: a fork branch) and a modified kvdurable
(`examples/raft/kvdurablenoax`, a Go module of its own). The etcd server keeps the real raft, so the
modified one lives in a part (module root) of its own, `RaftNoAx/`, as the witness experiment lives
in `RaftWitness/` (`notes/raft-witness.md`).

**2026-11-24 (branch `raft-retire/2026-11-24`): kvdurablenoax retired.** kvraft_robust (KvRaft/, on
this part's raft) and kvraft-udp subsume `raft_kvdurable_porcupine_safe`/`robust` here; the part keeps only
raft (project raft-noax, and walpb's part of project etcd), rooted at raft's `Link` and the modules
etc/api/raft.txt lists as importable (etc/copy-part.py's `raftnoax_roots`), for KvRaft, which takes its
raft from it. Project kvdurable-noax, `examples/raft/kvdurablenoax`, the part's kvreconf translation and
the `--kvdurable-noax` Link are gone, and so is copy-part's `RENAME` (empty). What follows about
kvdurable is history.

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
    # (raft-noax: add --src raft-noax=DIR for a local checkout of the fork at RAFT_NOAX_REV)
    etc/copy-part.py
    etc/gen-init.py
    etc/gen-link.py --raft-noax > RaftNoAx/Proof/go_etcd_io/raft/v3/Link.lean
    etc/gen-link.py --kvdurable-noax > RaftNoAx/Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/Link.lean

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

## Stage 2 (2026-11-18): the part on the modified code

Commits `190bbe2d7f`..`5fcff196bc` (and the one recording this). The part is now the noax fork (`RAFT_NOAX_REV = 91e2ea7`) and
`examples/raft/kvdurablenoax` (`KVDURABLE_NOAX_DIR/PKG`; `GO_MOD_PINS` checks its go.mod's replace).
`lake build RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Results`
builds (3828 jobs). `etc/goose.py --check` (both part projects), `etc/copy-part.py --check`,
`etc/gen-init.py --check` and the two Links pass. The kvreconf and walpb pieces were not regenerated:
their translations name raft's types and functions only, which did not change.

**What the switch took** (beyond the steps above):
- `RaftNoAx/Code/go_etcd_io/raft/v3/raftpb.toml` is the part's own: its `imports` list (which overrides
  the package's real imports in the translation) gains `errors` (noax.go's `errDecodeConfChange =
  errors.New(...)`, a translated package variable) and loses `proto`.
- gen-init: kvdurablenoax's `Init.lean` and `PkgTable.lean` are generated from the part's translation
  (`noax_inits`, as `wt_inits`), since the part's raft imports other packages than the main one (no
  `proto`, raftpb imports `errors`); copy-part skips them (`NOAX_MAIN_PATHS`).
- The link lists name `kvdurablenoax_*` (the functions' package) and the new callees; `kvdurablenoax_withTimeout`
  replaces `context_WithTimeoutBackground`; `fmt_Errorf`, `fmt_Sprintf`, `strings_Join`, `DescribeConfChange` are gone.
- Hand fixes (the files are the part's own, first line removed): raft's `Base.lean` (imports protobuf's
  `proto` translation, which raft no longer does; raftpb's package fact also says `errDecodeConfChange`
  holds a non-`nil` error, for the decoders' error) and `Init.lean` (raftpb's initializer allocates and
  sets `errDecodeConfChange`; raft's import list lost `proto`); `MessageType__String` (the fact's first
  half); every `proto.*` caller re-pointed to the `raftpb.*` spec (the call no longer goes through an
  interface and a type assertion); `confchange.checkInvariants`/`Changer.apply` call `errors.New`
  (Perennial's `errors.wp_New`, a theorem); `newRaft` without the `nodesStrs` loop (`hexIDs`, lazy);
  `stepLeader`'s `MsgProp` with `failedCheck` an interface (`lazySprintf`), compared with `nil`, no
  `DescribeConfChange`; `bootMarshal` (`ApiVocab`) over `raftpb.MarshalConfChangeV1` (no error result);
  the kvdurable callers of `withTimeout` (it calls `context.Background` itself).
- New specs, the part's own (`RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/`): `CloneSnapshot`, `CloneConfState`,
  `MarshalConfChangeV1/V2`, `UnmarshalConfChangeV1/V2` are the `proto` trust-boundary specs they replace,
  verbatim but for the call (and `isPkgInit` of raftpb, no error result for the encoders).
  `CloneEntry` and `EntrySize` are `proto.ClonePb`/`SizePb` **at `Entry`'s instance `pbEntryC`**:
  `entRoC l c` in, `entPtsCC l' 1 c` / `entrySize c` out, with no registration premise
  (`pbModelOf … = some pbEntryC`), since the functions are `Entry`'s own; so `pbEntryC_reg` and
  `entryEncC_ok` are no longer reached (nothing else on the path used the registration).
- `withTimeout` (kvdurablenoax): spec = `context.WithTimeoutBackground.spec` at the new call;
  **proved** (Perennial's `wp_WithCancel_Background`, `time.wp_AfterFunc`).

**The inventory** (`#print axioms raft_kvdurable_porcupine_safe`: 316 constants, 328 in stage 1).
Gone: all 13 hand-written axioms but one (`DescribeConfChange.wp_proof`, `fmt.Errorf.wp_proof`, the
eight `proto.*.wp_proof`, `entryEncC_ok`, `pbEntryC_reg`) and Perennial's `time.Now.wp_proof`. Left:
Lean's three, Goose's type axioms (untranslatable protobuf/`fmt`/`os`/`strings`/`sync` types),
`ccDecodeV2_nil`, and `sorryAx` from exactly these eight proofs (each reached from
`raft_kvdurable_porcupine_safe`, chains by `AxPath2.lean`):

| obligation | reached through | difficulty, what it needs |
|---|---|---|
| `raftpb.CloneConfState.wp_proof` | `newReplica`, `Storage.InitialState`, `Replica.install`, `MemoryStorage.CreateSnapshot`, `ConfState.Equivalent` | easy-moderate: four `append(nil, s...)` slice copies, `cloneBool`, a fresh struct; `cloneUnknown` of the hidden `unknownFields` (see `pbMsg` below); the new `pbMsg` invariant allocated (`pbMsg_alloc`) |
| `raftpb.CloneSnapshot.wp_proof` (5 conjuncts) | `MemoryStorage.Snapshot/ApplySnapshot/CreateSnapshot`, `raftLog.snapshot`, `unstable.nextSnapshot/restore`, kvdurable `copyMsg`, `image.applySnapshot` | moderate: `cloneSnapshotMetadata` + `CloneConfState` + `cloneBytes`, one proof per ownership form (`ownSnapM/W/S/V`); share a core lemma |
| `raftpb.CloneEntry.wp_proof` | `raft.appendEntry` | easy-moderate: `entRoC` in, `entPtsCC` out; `cloneBytes` keeps nil vs non-nil (`bytesC`), cells fresh |
| `raftpb.EntrySize.wp_proof` | `entsSize`, `limitSize` | moderate: `sizeVarint` loop = `varintSize` (a pure lemma), the sign-extended enum, overflow only above `2^63` (the spec's premise) |
| `raftpb.MarshalConfChangeV1/V2.wp_proof` | `raftpb.MarshalConfChange` (`ProposeConfChange`) | hard: the round trip `ccDecodeV1 (bytes) = some m` needs `ccDecodeV1/V2` to be **definitions** (now `opaque` in `CCModel.lean`), mirroring the Go decoders; then a pure encode/decode round-trip theorem and the `appendVarint`/`appendBytes` loops; `ccLenMax` bound |
| `raftpb.UnmarshalConfChangeV1/V2.wp_proof` | kvdurable `Replica.applyEntry`, `stepLeader` | hard: same definitions; the Go decoder's loops (`consumeVarint`, field order) against the pure `ccDecodeV*`; the error is `errDecodeConfChange` (non-nil by raftpb's package fact, added this stage) |
| `ccDecodeV2_nil` (axiom) | `StepProof.isMessage_leave` | trivial once `ccDecodeV2` is a definition (empty input gives the empty message): a theorem by `rfl`/`simp` |

**`pbMsg` must change** (the question of the hidden fields): `pbMsg T l uf` is an invariant holding
`unknownFields ↦ us ∗ us ↦* uf` (full ownership of the bytes inside the invariant). The clones
`cloneUnknown(m.unknownFields)` = `append(nil, u...)`, which reads the bytes over several steps, so
the invariant cannot be kept open; and `EntrySize` reads only `len(u)` (one load, fine). So the
definition must change to `us ↦*□ uf` (the bytes persistent, read-only): no code of the closure
writes the bytes of a message's unknown fields once it is allocated (the `proto` axioms were the only
writers of the hidden fields: `sizeCache`). Affected: `InvPbCore.pbMsg` and `pbMsg_alloc`'s proof (its
statement can stay: it can persist the bytes under its update), raft's `Init.lean`/`Base.lean`
(`emptyState`'s invariant, `isInitialized`), `LemmasMiscR.emptyState_hsRO`. An alternative that keeps
`pbMsg`: none (a full points-to inside an invariant cannot be read over many steps).

**Not in the closure, still built**: `RawNode.Bootstrap`'s proof builds over the new `bootMarshal`
(`MarshalConfChangeV1`); `bootMarshal` stays a premise of `Bootstrap`/`StartNode` (kvdurable restarts,
`RestartNode`, so it is not on the path).

**Gates not yet updated**: `etc/tcb-collections/raft-noax.txt` has the new baseline (by hand: roots
the kvdurablenoax directory, `ccDecodeV2_nil` and the eight sorries); `etc/tcb-baseline.txt` (the
repository's axioms and sorries) has not been regenerated: it needs a full `lake build` and
`etc/tcb-report.py --check --update` (the part's eight new `sorry`s, and its stage-1 axiom copies gone).

## Stage 3a (2026-11-18): the clones and `EntrySize` proved

`raftpb.CloneConfState`, `CloneSnapshot` (all five conjuncts), `CloneEntry` and `EntrySize` are proved
(no `sorry`); their specs are unchanged (the stage-2 restatements of the old trust-boundary specs), and
their proofs still take no callee specs, so the link lists and Links are unchanged.

**`pbMsg` is frozen hidden fields, not an invariant** (`InvPbCore.lean`, now the part's own):
`pbMsg T l uf := (∃ st sc us, l.state ↦□ st ∗ l.sizeCache ↦□ sc ∗ l.unknownFields ↦□ us ∗ us ↦*□ uf)
∗ ⌜ufWire …⌝`. Stage 2's finding asked only for `us ↦*□ uf` inside the invariant; with every hidden
field read-only there is nothing left for an invariant to own (in the part nothing writes `state` or
`sizeCache` either: the `proto.*` axioms, protobuf's runtime, were the only writers), so the proofs
load `unknownFields` directly from `↦□` without opening anything. `pbMsg_persistent`, `pbMsg_ufWire`
and `pbMsg_alloc` keep their statements (`pbMsg_alloc` now persists the four points-tos under its
update); new: `pbMsg_uf` (the field and its bytes, read-only). `pbN` stays, unused. Knock-on edits, each
now the part's own: `Base.lean`'s `#emptyState` states `EtcdGrove.pbMsg raftpb.HardState es []` (Base
imports `InvPbCore`, which is below it) instead of the invariant spelled out; `Init.lean` makes it by
`pbMsg_alloc`; `LemmasMiscR.emptyState_hsRO` frames it. No other file of the part unfolds `pbMsg`; the
full part rebuilt unchanged (3828 jobs).

**The proofs** (`RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/`, outside the spec/proof discipline for the
unexported helpers):
- `CloneLeaf.lean`: the leaf helpers' triples: `cloneUint64`/`cloneBool` on `optCell` (a fresh frozen
  cell, `nil` for `nil`; `cellRO_optCell`/`optCell_cellRO`/`optCell_null` convert), `cloneUint64s`
  and `cloneUnknown` (`append(nil, s...)` by `wp_slice_append`), `cloneBytes` (`nil` stays `nil`, any
  other slice a fresh **non-`nil`** one: `wp_append_nonnil`, `append` onto the `[]byte{}` literal's
  non-null pointer, by `wp_slice_append_fits` when nothing is appended, which Perennial's
  `wp_slice_append` does not say), and `wp_cloneBytes_C` on `bytesC`.
- `CloneCS.lean`: `wp_CloneConfState_al`, at any `al` (a set `AutoLeave` stays set: `ownSnapS`'s
  `csSet` needs it, which `CloneConfState.spec`, `ownCSM` only, does not give), and the `nil` case;
  `CloneConfState.wp_proof` is it at `al = false`.
- `CloneSM.lean`: `cloneSnapshotMetadata`'s core on a non-`nil` metadata's fields with the conf state's
  clone a triple parameter (`R`/`Q`), its instances for the conf state's forms (`csOptA`: a frozen set
  one clones to an owned one, `csPts_weaken`; `csSet`), and the four metadata forms (`smOpt`, `smPtsW`,
  `smPtsS`, `smPtsV`).
- `CloneSnapshot.lean`: the same core for the snapshot (metadata clone a parameter) and the five
  conjuncts. `CloneEntry.lean`: direct.
- `SizeVarint.lean`: `varintSize` facts (`< 128`, `≥ 128`, `≤ 10` below `2^64`) and `wp_sizeVarint`
  (the loop, invariant `n + varintSize v = 1 + varintSize v₀`). `EntrySize.lean`: four `wp_join`s, the
  running sum kept as the word of the model's partial sum, so the result is `W64 (entrySize c)` and
  `sint.Z` of it is `entrySize c` below `2^63`; the enum's conversion is `W64 (sint.Z t)` as in
  `entrySize`.

Left in the part (`etc/tcb-collections/raft-noax.txt`): the conf-change codec (`MarshalConfChangeV1/V2`,
`UnmarshalConfChangeV1/V2`'s sorries, `ccDecodeV2_nil`), another track.

Checked (2026-11-18): `lake build RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Results`
(3832 jobs), `etc/copy-part.py --check` (0 differ); `#print axioms` of the four `wp_proof`s: Lean's
three and Goose's type axioms only, no `sorryAx`; `AxPath2` on `raft_kvdurable_porcupine_safe` reaches
`sorryAx` only through the codec (`MarshalConfChangeV1.wp_proof`, ...).

## The part declares no axiom (2026-11-20, prove-raftex)

Stage 3b left the closed theorem axiom-free, but the part still declared 13 axioms, none reached:
- 11 stage-1 copies (`proto.{CloneConfState,ClonePb,CloneSnapshot,MarshalConfChange,
  MarshalConfChangeV2,SizePb,UnmarshalConfChange,UnmarshalConfChangeV2}.wp_proof`,
  `DescribeConfChange.wp_proof`, and the axiom-free `fmt.Sprintf`, `strings.Join` proofs): modules of the
  main tree's closure that only the main versions of the part's own files import. `etc/copy-part.py`
  now drops the copies no module of the part imports (to a fixpoint; `Results`, `TopLevelRobustness`
  and `Link` modules are roots), so it deleted them and `--check` keeps them out;
- `entryEncC_ok` and `pbEntryC_reg` in `PbEntryTypeCore` (imported by `PbEntryType`, but nothing in the
  part names `entryEncC`, `pbEntryC` or its lemmas: the part's raft calls `raftpb.CloneEntry`/`EntrySize`,
  not `proto.ClonePb`/`SizePb` at the registered instance). The part's `PbEntryTypeCore` is now its own,
  without them (and without `entryEncC`, `pbEntryC` and its `simp` lemmas).

`grep -rn '^axiom' RaftNoAx` finds none. (The baseline `etc/tcb-baseline.txt` lists names, which the
main tree still declares, so it does not change.)
