# etcd-grove (Lean)

This branch verifies **etcd** — starting with its Raft implementation — in Lean,
using the Lean port of Perennial ([mit-pdos/perennial](https://github.com/mit-pdos/perennial),
branch `lean`), which is a Lake dependency (`lakefile.toml`, pinned in `lake-manifest.json`). Perennial has the
framework and the Goose translator; this repository has the Goose translation of
raft (v3.7) and of etcd (`Code/`, `GeneratedProof/`), and the proofs.
Every file is a module of Lean's module system (see "Modules" below).

It is a port of the Rocq development on branch `main` (`new/proof/go_etcd_io/raft/
election_proof/`). The Rocq notes on `main` (`notes/`) still describe the proof:
its design, the false statements found so far, what raft actually does. Read them
there (`git show main:notes/STATUS.md`); this branch's `notes/` only records what
is specific to the Lean port.

## Read the notes first

- `notes/STATUS.md` — where the port is.
- `notes/decisions.md` — how the Rocq structure maps to Lean, and why. Its entries are the
  reasoning at the time, not rules: many turned out wrong. Do not keep a worse spec or proof
  because an entry chose it; supersede the entry instead (its header says how).
- `notes/status-history.md` — STATUS.md's superseded sections, append-only (move a section there when it stops describing the current state).

Before you finish, update `notes/STATUS.md` if anything moved. Its "Last updated" line keeps the
ten newest dated entries: add yours at the front and move the oldest to the list at the end of
`notes/status-history.md`. In a merge conflict on that line, keep one copy of each entry (never
both sides' lines whole: merges that did grew the header to 1.1 MB). `etc/setup-merge-drivers.sh` (once per clone) configures
merge drivers (`etc/merge-status.py`, named in `.gitattributes`) that do both merges this way (where git
runs no history driver, the entries beyond ten stay on the line, for the next update to move); a clone
without them merges the two files as git always does.

## Branches

Land a branch on `lean` with `etc/land.sh` from its worktree (notes-only branches too): it takes the
landing lock, checks `lean` is merged, runs `etc/gates.sh` and fast-forwards `lean`, so no other
landing moves `lean` in between (`notes/spec-first-plan.md`, "Landing takes a lock"). Record your
session in `/shared/etcd-grove-sessions.md` (same file, "The session registry").

Delete a branch once its work is merged into `lean` (or wherever it was merged): the
local branch (`git branch -d <branch>`, which refuses one that is not merged), its remote
copy if it was pushed (`git push origin --delete <branch>`), and its worktree if it had
one (`git worktree remove <path>`). The same in a dependency's checkout (Perennial's
branches, under `.lake/packages/perennial` or a separate clone) once they have landed. A
session's own worktree branch goes when the worktree does, at the end of the session.
Delete only branches you created; leave other people's, merged or not.

## Layout

Files are laid out by kind, then by the Go package path (as in Perennial; module
names follow the paths, e.g. `Spec.go_etcd_io.raft.v3.tracker.NewInflights`):

- `Code/<pkg>.lean`, `GeneratedProof/<pkg>.lean`: the Goose translations (below);
- `TrustedCode/<pkg>.lean`: the hand-written models of the declarations a Goose configuration
  lists as `trusted` (a function's `X.impl`, a package variable's whole initializer `X.init`),
  which the translation imports, as in Perennial's `Perennial/TrustedCode`; each docstring says
  why the model is faithful. Part of the trust base. `ManualProof/<pkg>.lean` is the (empty)
  module the generated proof of such a package imports;
- `GooseLang/Ext/<Name>/{Impl,Specs}.lean`, `Proof/<Name>Prelude.lean`: this repository's own
  GooseLang extensions, as Perennial's (`Perennial/GooseLang/Ext/`): `Impl` the trusted semantics
  (the extension's `name` is the path of the Go package it implements), `Specs` the ghost state
  and WP specs, the proof prelude both. The package's `TrustedCode` models call the extension's
  operations by name (`ExternalOp E.name "Read"`); goose needs to know nothing of it.
  `durableExt` (`examples/lib/durable`, whole-file durable state) is the first.
  Every decision of an extension's trusted semantics (its `Impl`, and any trace-level assumption
  a theorem over it takes) has a Go example saying why, in the extension's semantics examples
  package (the Linux file extension `GooseLang/Ext/Fs`: `examples/osfs/semantics/`, indexed in
  its `doc.go`): the decision, the Lean names, the outcome allowed or excluded, and the evidence
  (measured, documented with a citation, or assumed). A change to the semantics adds or updates
  its example in the same commit. An extension of an OS interface claims one target configuration
  and nothing wider (the Linux file extension: configuration C, Linux 7.0 and ext4 with its
  defaults, `notes/axiom-review/fs-config/`); every kernel claim is tested on it, with its
  helper scripts (`mkfs-mount.sh`, `check.sh`);
- `Spec/<pkg>/<fn>.lean`: the one Hoare triple of a Go function of package `<pkg>`,
  as `def <fn>.spec : Prop` (`Spec/go_etcd_io/raft/v3/raft__Step.lean`,
  `Spec/strings/Join.lean`);
- `Proof/<pkg>/<fn>.lean`: `theorem <fn>.wp_proof (callee specs …) : <fn>.spec`
  (an `axiom` at the trust boundary, `sorry` if unfinished); it imports only the
  `Spec` files of its callees;
- `Proof/go_etcd_io/raft/v3/` also holds what mirrors the rest of the Rocq directory
  `new/proof/go_etcd_io/raft/election_proof/`: the shared definitions (`Protocol`,
  `Defs`, `Inv*`, `StepLemmas`), outside the spec/proof discipline (predicates, pure
  lemmas); `Link.lean` (generated by `etc/gen-link.py`), which links every proof to
  its callees' proofs (`theorem <T>.wp_<M> : <fn>.spec`); and `Results.lean`, the
  protocol-level results.
- `Proof/go_etcd_io/etcd/cache/v3/` holds the same for etcd's `cache` package: its
  shared definitions (`Base`, `Inv*`, `OnceFrame`, `Handoff`), `Link.lean`
  (generated by `etc/gen-link.py --cache` from `etc/link-lean-first-cache.txt`) and
  `Results.lean` (the exported results restated, with `#print axioms` of each).
- `Proof/k8s_io/utils/third_party/forked/golang/btree/` holds the same for the B-tree
  the cache uses (the k8s fork of google/btree): `Tree`/`Model` (pure), `Defs`
  (`ownBTree`), `NodeLemmas`, `Lemmas/` (the proofs' own lemmas), `Link.lean`
  (generated by `etc/gen-btree-link.py`) and `Results.lean` (`#print axioms` of every
  result); the cache sees it through `InvBtree.lean`.
- `Proof/go_etcd_io/etcd/server/v3/etcdserver/` holds the same for etcd's server (the
  consistent index and the apply thread): its shared definitions (`Base*`, `Inv*`) and
  `Link.lean` (generated by `etc/gen-link.py --server` from
  `etc/link-lean-first-server.txt`); the specs of its callees are in their packages
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/cindex/`, `Spec/go_uber_org/zap/`, ...).
- `Proof/go_etcd_io/etcd/server/v3/etcdserver/read/` holds the same for the server's read-index
  loop: `Link.lean` (generated by `etc/gen-link.py --read` from `etc/link-lean-first-read.txt`)
  and `Results.lean`; `Proof/go_etcd_io/etcd/pkg/v3/{wait,idutil,notify}/` hold the request
  path's wait registry, id generator and notifier (`Defs.lean` and the proofs), linked in the
  server's `Link.lean`.
- `Proof/<pkg>/Init.lean` (`bbolt/internal/common`: `Initialize.lean`): a package's
  `<pkg>.wp_initialize'` (its initializer gives its `isPkgInit`), with the trust-boundary
  axioms on its untranslated variable initializers (split, when the proof applies other proofs, into
  `Init.lean`, the facts and axioms, and `InitLinked.lean`, the `wp_initialize'`: "Import tiers");
  generated by `etc/gen-init.py` (the
  packages with facts or translated initializers are configured in its `SPECIAL`;
  `--check` exits 1 if a file differs). Never edit them by hand: change the script.
- There is no `Proof/Lib/`: a fact about Perennial's, Iris's or Lean's own definitions that
  belongs to no Go package (fractions, `Fractional`, ghost state, `ownMap`, `GoStringLt`, lists)
  goes to Perennial (a branch off its `lean`, "Changes to Perennial" below), so that packages
  share one lemma instead of each proving a copy (`notes/decisions.md`, "Proof/Lib: facts that
  belong to no Go package").
- A project translated into a module root of its own (`<root>/{Code,GeneratedProof,Spec,Proof}/`,
  a part: `etc/goose.py`, `etc/proof_roots.py`): until stage R6
  of the raft v3.7 retarget (2026-10-16, `notes/raft-retarget-plan.md`) `EtcdDeps/` held etcd's
  raft dependency names-only for the server and `Raft37/` the parallel tree the Raft proof was
  ported into; the swap made the latter the raft tree and the server imports it. The
  trust-boundary specs of protobuf-go's `proto` the Raft proof rests on are in
  `Spec/google_golang_org/protobuf/proto/`.
- `RaftWitness/` is such a part: the witness experiment (`notes/raft-witness.md`; raft with
  witness support, a candidate implementation of etcd-io/raft#133, not merged upstream), a
  parallel tree with the main layout (`RaftWitness/{Code,TrustedCode,GeneratedProof,ManualProof,
  Spec,Proof}/`, modules `RaftWitness.*`): the raft of the fork's `raft-witness-goose-lean`
  (`99cb9e2d9`, project `raft-witness` of `etc/goose.py`) with its proof, and `examples/raft/kvwitness`
  (project `kvwitness`, the key-value store with a witness, `raft_kvwitness_porcupine_safe`). It
  imports the main tree but never the main raft or kv (its modules declare the same names), so
  it has its own copies of the main modules that reach them (raft's standard-library and `proto`
  specs, `Spec/slices/Sort`, ...; the generated package initializers and `PkgInitExt`,
  `etc/gen-init.py`'s `PART_INITS`); nothing outside it imports it. Links: `etc/gen-link.py
  --raft-witness`/`--kvwitness`; trust base: `etc/tcb-collections/raft-witness.txt`.
- `RaftTla/` is another: raft's `with_tla` build (`state_trace.go`: the trace hooks with their
  bodies), for raft's TLA+ trace validation (`examples/raft/tracecheck`) and nothing else. The main
  tree translates and verifies raft WITHOUT the tag (the build etcd ships, `state_trace_nop.go`:
  empty hooks), and every theorem outside `RaftTla/` is about that build. `RaftTla/{Code,
  GeneratedProof}/` hold raft's own package translated with `-tags with_tla` (project `raft-tla`)
  and the trace check's harness (project `tracecheck`'s part). Its specs and proofs of raft are
  **generated copies** of the main tree's modules, imports redirected (`etc/gen-raft-tla.py`, files
  starting with its marker line; `--check` in `etc/gates.sh` and CI): one proof text, compiled
  against each build. Never edit a copy: edit the main tree's file and rerun the script. A raft file
  of the main tree must therefore compile in both trees (name nothing that only one build has, and
  do not unfold `isTraceLogger`). What differs between the builds is hand-written once per tree, at
  the same module path: `InvTraceLogger` (the logger's contract: nil only in the main tree, the
  `TraceEvent` method in `RaftTla/`), the eleven hooks' proofs (their specs are shared), raft's
  `Init`, and `Link` (`etc/gen-link.py --raft-tla`, list `etc/link-lean-first-raft-tla.txt`);
  `RaftTla/` alone has the hooks' helpers and the trace check's specs and proofs (its `Init` and
  `PkgTable` from `etc/gen-init.py`). Nothing outside it imports it; trust base:
  `etc/tcb-collections/tracecheck.txt` (`notes/decisions.md`, "One raft proof for both builds").
- `RaftNoAx/` is another: raft without hand-written axioms (`notes/raft-noax-part.md`), for a closed
  kvdurable theorem whose trust base has no axiom of this repository: raft of project `raft-noax` and
  kvdurable of project `kvdurable-noax` (`etc/goose.py`'s `RAFT_NOAX_REV`, `KVDURABLE_NOAX_*`; with
  kvreconf and walpb translated into it as parts of their projects), and copies of every main-tree
  module of kvdurable's `Results` closure that reaches them, written by `etc/copy-part.py` (a first
  line naming it; `--check` in CI; a file without that line is the part's own); its initializers
  from `etc/gen-init.py`'s `PARTS`, its Links from `etc/gen-link.py --raft-noax`/`--kvdurable-noax`.
  Nothing outside it imports it; trust base: `etc/tcb-collections/raft-noax.txt`.
- `Net/` is another: the net extension's `net` and the programs over it (`examples/net`, `examples/lib/remote`,
  the models' codecs and `net/{http,rpc}`). Since the net swap (etcd-dist D2, 2026-11-22) its `net` is also the
  main tree's (`net=Net` in every project; `Proof/net/InvNet.lean` defines the address predicates over it):
  the main tree imports `Net/`'s `net` modules, never the part's other modules.
- `KvNet/` is another: kvnet's proof (`notes/kvnet-part.md`), over raft-noax's raft, `Net/`'s `net` and
  `WalTester/`'s bodied `durable` in one closure: project `kvnet` and parts of projects raft-noax, net,
  durable and etcd translated into it, copies of those parts' (and the main tree's) modules its own
  modules reach written by `etc/copy-part.py --part KvNet` (sources `Net/`, `WalTester/`, `RaftNoAx/`,
  main), its initializers by `etc/gen-init.py` (`KVNET_INITS`). Nothing outside it imports it.
- `PorcupineDag/` is another: porcupine's unmerged PR #46 (the DAG search; `third_party/porcupine-dag`,
  project `porcupine-dag`), with v1.3.1's Go path, so its modules declare the main porcupine's names
  and nothing outside it imports it (`notes/porcupine-dag-plan.md`). Links: `etc/gen-link.py
  --porcupine-dag`; trust base: `etc/tcb-collections/porcupine-dag.txt`.
- `WalTester/` is another: etcd's WAL tester (`examples/etcd/wal`, project `etcd-wal`) and the library it
  keeps its oracle with, `examples/lib/durable` translated **with its bodies** (project `durable`'s part)
  and proved over the per-byte file extension `fsExt`, where the main tree keeps `durable` trusted over
  `durableExt` for kvdurable, kvfile and `etcdstart` (`notes/wal-lean-integration.md`, "`lib/durable`:
  two translations", decided 2026-11-15). Its modules declare the main `durable`'s names, so nothing outside it imports it;
  it imports the main tree's `os`, WAL, `fileutil` and raftpb. Temporary: it goes once kvdurable is
  ported onto the bodied `durable` and `durableExt` retires. Links: `etc/gen-link.py --durable`.
- `SpecPlan/` is another: the spec plan (`notes/specs-only/README.md`), intermediate specs for all of
  etcd (client, raft, server, apply/txn/lease/auth, mvcc, backend, bbolt and their trust boundaries)
  over opaque predicates, with no proofs: `SpecPlan/Spec/<pkg>/`, modules `SpecPlan.Spec.*`, one
  `def … .spec : Prop` per function and per law, no `theorem`/`axiom`/`sorry`; `SpecPlan/Spec/PkgInit/`
  is generated (`etc/gen-specs-pkginit.py`, `--check`). It builds (`etc/specs-build.sh`,
  `etc/specs-build-all.sh`), imports only the shared translations (`GeneratedProof`, `GooseLang`) and
  Perennial, and nothing outside it imports it (its namespaces are the main tree's). No `Link`/`Results`:
  the trust-base and verified-code scripts see nothing of it.
- `Robustness/` (lean_lib `Robustness`): the generic statement of robustness theorems, one
  definition (`Robust crashing stable g threads bound`: in every execution of Perennial's `DistCrashNstepsBelow`
  (fewer than `threads` live threads on every machine, fewer than `bound` steps) of programs on machines that crash and restart and programs on machines that never crash, with
  any extensions, no thread is stuck or has a top-level panic; a property such as linearizability
  is checked by a program of the deployment that panics, never stated over traces in Lean), and
  `examples/lib/robust` its Go test harness (machines as network namespaces, faults made by the
  kernel and the harness, never by the program): `notes/robustness.md`. Every example's top-level
  result is an instance, in two files named `TopLevelRobustness.lean`:
  `Spec/<example>/TopLevelRobustness.lean` states it (`def <name>.spec : Prop`, nothing else: the
  file to audit) and `Proof/<example>/TopLevelRobustness.lean` proves it (`theorem <name> :
  <name>.spec`, from the example's closed theorem); the program and the other definitions the
  statement names are in `Proof/<example>/TopLevelDefs.lean` (a defs module, so the Spec file
  imports no proof); a new example gets all three. (kvnet's statement,
  not proved yet: `Proof/.../examples/raft/kvnet/Robust.lean`.)
- `models/`: our trusted models of real libraries (executable stand-ins: verified where they are code,
  trusted only in their claim to behave like the library), the Go module `models.lab` (a path naming no
  project, as the part `Net/` is exported to dsverify-lab), each with its evidence (`models/README.md`):
  the codec helpers `pbcodec`, `jsoncodec` (translated into `Net/`, project `models`, proofs in
  `Net/Proof/models_lab/`) and the generators of the codecs that call them, `models/protobuf/pbgen.py`
  (trusted as a program: its core `pbgen_core.py`; inputs derived from the real descriptors by
  `models/pbdesc`) and `models/json/jsongen.py` (`notes/dsverify-net-port-plan.md`, phase 5).
- `old/<name>/`: old proofs kept for reference, not built (no `lean_lib` glob or `etc/` script
  reaches them), under their original paths: `old/bbolt/` (branch `bbolt`'s, `old/bbolt/README.md`), `old/dsverify/` (dsverify-lab's network
  harness at `348a866`, the reference for `notes/dsverify-net-port-plan.md`).

## Modules

Every file starts with `module`, imports with `public import` and opens
`@[expose] public section` after its imports, so every declaration is public and
every definition's body visible to importers, as before the module system; what
changes is that an importer loads only that public part (not proofs or private
declarations): importing Perennial's proof prelude takes half the memory and a
quarter less time, and a compile's peak memory is about a third lower (2.8 to 1.8
GiB, measured 2026-10-08; `notes/decisions.md`, "Lean's module system"). A
definition sealed inside its file (`ownRaftPhys`) is `@[no_expose]`. New files follow
the same pattern; Perennial's are modules too.

## Package APIs

Lean's visibility is per module (a declaration is `private`, or public to every importer) and
`import all` is unrestricted, so a package cannot hide the definitions its own files share. Two
pieces make a package's boundary checkable instead (`notes/decisions.md`, "Package APIs: an
importable list and a generated interface"):

- **The importable list**, `etc/api/<pkg>.txt`: the modules other directories may import.
  `etc/api-check.py etc/api/<pkg>.txt --check`: a module outside the package imports only listed
  modules (never with `import all`), and a listed module publicly imports only listed modules of
  the package (linking files, `Link`/`Results`/`Adequacy*`, are exempt; a non-linking module that
  imports one is a warning). Adding a module to the list is an API change.
- **Sealing**: an API module imports the package's internals non-publicly and marks what clients
  must not see inside `@[no_expose]`; the package's own proofs `import all` it. When a proof
  outside the package needs a fact of a sealed predicate, add a law to the API module; do not
  unseal it.

Raft is the first (2026-10-26): `etc/api/raft.txt`; `Spec/go_etcd_io/raft/v3/Api.lean` (the module a
client imports), `InvNode`/`InvNodeCtx` (the node API, sealed), `ApiVocab`/`ApiCtx` (the vocabulary
moved out of the internals), `Linked` (raft's linked results, `open RaftLink`, for the linking
modules of raft's clients: a proof or definition takes raft's specs instead, "Import tiers").

## Import tiers

Specs never import proofs. Every module is in one of five tiers, and imports only from its own tier
or lower (`etc/tier-check.py`; `notes/decisions.md`, "Import tiers"):

1. **base**: the translations and the framework (`Code/`, `GeneratedProof/`, `TrustedCode/`,
   `ManualProof/`, `GooseLang/`, Perennial, Iris), and every module outside the `Spec`/`Proof` roots;
2. **spec**: a module under `Spec/` (or a part's `<Part>/Spec/`);
3. **defs**: a module under `Proof/` that is neither of the two below: shared definitions,
   invariants, lemmas (`Defs`, `Inv*`, `Base`, `KeyOps`, ...). Specs and defs may import each other
   (defs are a spec's vocabulary);
4. **proof**: a `Proof/` module declaring `theorem`/`axiom <F>.wp_proof` or a variant of it
   (`wp_proofSnapM`, `wp_proof_crash`), one function's proof: it imports specs and defs only (its
   callees through their specs);
5. **linking**: `Link`, `Results`, `TopLevelRobustness` (under `Proof/`: the proofs of the
   top-level results), `*Linked` (`Linked`, `MainLinked`, `TracedLinked`, a split's
   `<Name>Linked`), `Adequacy*`, and the modules listed in `etc/tier-linking.txt` (each with why: it
   composes linked results under another name). Only a linking module imports a proof or linking
   module.

So a proof's edit rebuilds the linking modules above it and nothing else, and a spec's cone holds no
proof. A spec or a definition that needs something declared in a proof or linking module (a
definition, a pure lemma, an instance) gets it moved down into a defs module, the name and statement
unchanged (`client/v3/KeyOps.lean`: `putKeyOp`, out of `client/v3/Results.lean`); a module that
genuinely uses a linked result (a `wp_<M>` of a `Link`) is linking, and nothing below imports it: its
linked theorems go to a `<Name>Linked.lean` beside it (`NodeBridgeLinked`, `ServedLinked`), or the
module is listed. A proof file that needs a linked result takes it as a hypothesis of its
`wp_proof`, which the `Link` passes: the callee's `.spec` (an `@` callee), or, for a lemma proved over
linked results, its statement as `abbrev <lemma>.law : Prop` in a defs module beside it
(`client/v3/ClientCallLaws.lean`), proved by `<lemma>_law_holds` in the linking module and passed as an
`=<lemma>_law_holds` callee (`notes/decisions.md`, "Import tiers: a proof takes a linked lemma as a
law").
`etc/tier-check.py --check` (in `etc/gates.sh`) refuses a violation not in `etc/tier-baseline.txt`
(the ones left; `--check --update` only shrinks it); `--tier MODULE` prints a module's tier, its
importers and its cone (what an edit to it rebuilds, by tier).

## Issues in the verified code

When you find a bug in the Go code being verified (a reachable panic, a wrong result) or
in its documentation (a precondition the code needs that its API does not state, behavior
its documentation contradicts), record it, one file per finding, in the format of
`issues/README.md`: in `issues/` when it has a Go test that fails at an upstream commit and
reaches the bug the way etcd (or a documented user of a public package) uses the code, the
test in `issues/<slug>/` and the file written as the bug report we would file; otherwise in
`nonissues/` (found by code reading, a precondition etcd meets, documentation only), with its
reason. Each says whether it blocks the proof (`blocks-proof:`). Do this as soon as it is
found, including when a spec sidesteps it with a premise: the premise is where the proof
records it, `issues/` is where people find it. `etc/issues-status.py --index` regenerates the
indexes, `--check` checks the files. Bugs in this repository's own specs and proofs go in
`notes/` instead. A subagent that finds one says so in its report.

## Feedback on specs

The `spec` skill (`.claude/skills/spec/`) is where the repository keeps what makes a good spec:
`PRINCIPLES.md`, and `examples/` of specs the user reviewed. When the user critiques a spec
(yours, a reviewer's, or a candidate), make it learn from it, minimally: a new or sharpened
principle; and when the user approves a spec, an example (its first version, each critique with
what it changed, the approved spec). A fix to the spec itself is not enough.

## The spec plan and convergence

`SpecPlan/`'s specs are judged against the requirement snippets of `examples/specreq/` (Go: what a
caller relies on is a `panic` on its violation, and each snippet must be provable panic-free from the
specs), and the snippets against what the real code and its users do. New and reworked specs and
proofs in `Spec/`/`Proof/` converge toward `SpecPlan/`'s: take its statement (vocabulary, premises,
post) unless the proof shows it wrong. A spec defect a proof finds goes in the change ledger
`notes/specs-only/ledger.md` (date, spec, defect, evidence, proposed change, decision) before the spec
is edited, in `SpecPlan/` or in `Spec/`. `notes/specs-only/README.md` is the plan and its conventions,
`open-questions.md` its decisions.

## Bounds

Thread counts, `RWMutex` reader slots, lifetime counters and sizes are reasoned about where they
are owned (`notes/bounds-plan.md`): the adequacy theorem fixes the constants, the owner of a lock,
wait group or counter turns them into a protocol inside its invariant (a thread pool of reader
slots, a wait group backed by thread tokens, receipts), and a spec in between takes only its
`threadTok` and the owner's handle. `etc/bounds-check.py` counts what does
not yet follow this, per kind and package (`--kind KIND` lists the places); `--check` (in
`etc/gates.sh` and CI) refuses a count above `etc/bounds-baseline.txt`, and `--check --update`
records a decrease. An owner's own matches are listed in `etc/bounds-allow.txt`.

## Trust base

`etc/tcb-report.py` reports what the proof rests on (needs an up-to-date `lake
build`): the `sorry`s and axioms the results depend on, the exported results (linked
results no other proof uses), and the definitions their statements are written in
terms of. Run it when you need the report; don't commit its output (`-o` writes a
file), which goes stale as the proof changes. It never builds, nor does
`etc/verified-code.py`: both exit, asking for `lake build`, when `lake build
--no-build` finds the root modules out of date. `etc/tcb-report.py --check` exits 1 if
this repository's axioms or `sorry`s differ from `etc/tcb-baseline.txt`; when you add or remove one on
purpose, rerun with `--check --update`.

For some of the results only: `--roots PATTERN...` (regular expressions searched in a
root's name, its module's file and its spec's file: `'raft__Step'`,
`'^Spec/go_etcd_io/raft/'`) prints the axioms and `sorry`s those roots rest on and
which roots reach a `sorry` (`--per-root`: every root). A collection
(`etc/tcb-collections/*.txt`) keeps the patterns (`roots` lines) with their baseline
(`axiom`/`sorry` lines): `--collection etc/tcb-collections/raft.txt` reports on it,
`--check` compares, `--check --update` rewrites the baseline. Track a proof's progress
by adding a collection for it.

## How much is verified

`etc/verified-code.py` accounts for how much of the translated Go code is verified
(needs an up-to-date `lake build`, and `go`): every Go function is verified,
unfinished, assumed, translated or not translated, counted in functions and Go code
lines, per project, per module, per package and per file. It takes the projects from `etc/goose.py` (with the
Go modules counted, `counted_modules`) and reads the Go sources of the translated
projects (in `.lake/go-src/<project>`, cloned or fetched at the pinned revision), the
translations in `Code/`, and this repository's proofs (the linked results of every
`Link.lean`) from `.lake/tcb.json` (shared with `etc/tcb-report.py`; `--reuse` skips
re-running Lean). `--package PREFIX` adds a summary row for the packages below PREFIX
and narrows the by-file tables (and `--functions`, every function) to them. It prints
plain text (`--markdown` for Markdown; `-o FILE` writes Markdown if FILE ends in `.md`).
Like the TCB report, don't commit its output.

Both scripts are generic for a Goose project with this layout: they name no project.
Their roots are found by `etc/proof_roots.py` (every `Link.lean`/`MainLinked.lean`/`Results.lean` under
`Proof/` and a part's `<root>/Proof/`; Lean runs grouped by the part roots a module
reaches; the namespace from the `Link.lean` files), and a `.lake/tcb.json` that is
not of the current roots (an interrupted run, a new package) is refused with `--reuse`.

**Per top-level theorem, without a build**: `etc/theorem-loc.py THEOREM...` (e.g.
`etcd_putget3_safe`) counts, read off the source text, the Lean lines the theorem trusts (its TCB:
the axioms of its `etc/tcb-collections` file and the definitions its statement and those axioms are
written in, split into premises and axioms) and the Go code lines its proof verifies (the functions
whose `wp_proof` theorems it reaches, outside this repository and in it). It approximates
`etc/tcb-report.lean` (see its `--help` for what it does not follow); its axioms are only as current
as the collection's baseline. `--list-tcb`/`--list-verified` list what it counted, `--json` keeps it.
`etc/theorem-tcb.py THEOREM... [-o DIR]` writes that TCB out to read (default: a fresh temporary
directory): `TCB.lean` in reading order (the statement, its premises, then each axiom with the
definitions it brings in), the same declarations in a trimmed copy of the tree, and a `README.md`
with the counts by part and file.

## Proof writing

Perennial's Lean docs (in the dependency, `.lake/packages/perennial/docs/`):
`PERENNIAL_PROOF_TUTORIAL.md`, `PERENNIAL_PROOF_REFERENCE.md`, `IRIS_PROOF_MODE.md`.

**Records.** A predicate takes its object's state as one record of pure values, holding
only what the specs on it need (`notes/decisions.md`, "Predicate indices"). In proofs:

- Keep a record a variable (`ls`, `σ`, `us`): do not destructure it with
  `intro ⟨a, b, c⟩`/`obtain`, and do not write a literal record where a variable will
  do. A projection of a literal record (`{ prev := p, … }.prev`) is an atom that
  `omega` and `rw` do not see through. (Exception: the proofs of an object's own methods may
  substitute a record defined from the Goose value, `subst Hring` with
  `r = inflightsRingOf iv buf`, and work on the value; the `proj_simps` lemmas of
  `inflightsRingOf` reduce what is left.)
- For arithmetic, use `word`, not `omega`: its preprocessing runs `simp`, which
  reduces projections of literal records and, through the `proj_simps` lemmas,
  projections of record-building functions (`(inflightsRingOf iv buf).buflen`).
- Before `rw`/`subst`/`obtain ⟨rfl, …⟩` on a hypothesis that mentions such a
  projection, `simp only at h` (no lemma needed for literals) — not a guessed
  `dsimp only [f] at h`.
- A new function that builds a record gets `proj_simps f` after it
  (`Proof/go_etcd_io/raft/v3/ProjSimps.lean`); the command refuses a function whose
  body branches.

**Large contexts.** Never use a bare `iframe` (or any search over the whole context) when a
goal or hypothesis holds a `[∗list]` over `List.replicate n` with a large `n`: the unifier
materializes the list (revoke-open, 2026-11-06: 80 GB). Don't `unfold` a definition across a
goal or context that size either; convert locally through a lemma. Frame explicitly
(`isplitl [H]` / `iexact`).

## The Goose translations

`Code/` and `GeneratedProof/` hold Goose translations by the pinned Perennial's
translator, each of a Go repository at the revision pinned in `etc/goose.py`. They are
generated: never edit the `.lean` files by hand.

- `{Code,GeneratedProof}/go_etcd_io/raft/`: raft v3.7.0 (etcd-io/raft `b867cf13`, the raft
  etcd's `go.mod` pins; protobuf-go v2 raftpb: messages, entries and snapshots are pointers
  read through getters) plus three fixes, the single-voter read-index shortcut
  (`issues/raft-readindex-singleton-stale.md`), the probe-to-replicate shortcut only at
  `pr.Next == pr.Match+1` (`issues/raft-stale-term-appresp-index-zero-ack.md`), and the
  configuration switched to a snapshot's when it is applied, not restored
  (`issues/raft-snapshot-during-apply-stale-confchange.md`): branch `raft37-goose-lean-a2` of the
  fork `upamanyus/etcd` (commit `565c2bd`, on `raft37-goose-lean-a1`), project `raft` of
  `etc/goose.py`; the same packages
  as before (`.`, `confchange`, `quorum`, `raftpb`, `tracker`), raftpb all but its protobuf
  plumbing (`ProtoReflect`, `Descriptor`, the file descriptor, ...); modules
  `Code.go_etcd_io.raft.v3`, .... (Until 2026-10-16 the verified raft was the fork's
  `raft-goose-lean`, upstream `40f8be7` plus the fix, the last commit before raftpb moved to
  protobuf-go v2, with gogoproto messages: `notes/raft-retarget-plan.md`.)
- `{Code,GeneratedProof}/{go_etcd_io/etcd,k8s_io,google_golang_org,go_uber_org}/`: etcd's
  `cache` package (the fork `upamanyus/etcd`, branch `goose-lean`; branch `goose` is the
  Rocq side's), with bodies, and the B-tree it uses
  (`k8s.io/utils/third_party/forked/golang/btree`), with bodies, and the types and names
  only of the other packages it uses (`client/v3` with the functions the cache's proofs
  call and the `Client` struct, `api/v3/{mvccpb,etcdserverpb,v3rpc/rpctypes}`, protobuf's
  `runtime/protoimpl`, `internal/impl` and `internal/pragma`, grpc's `codes` and `status`,
  and the packages of `Client`'s field types: `google.golang.org/grpc`,
  `grpc/credentials`, `client/v3/credentials`, `client/v3/internal/resolver`,
  `go.uber.org/zap`; modules `Code.go_etcd_io.etcd.cache.v3`, ...).
  Types Goose cannot translate are axiomatized, and their generated instances are
  `sorry -- axiomatized type`; no linked result reaches them (`etc/tcb-report.py`).
- From the same fork, etcd's server: `server/v3/etcdserver/cindex` and the apply thread
  of `server/v3/etcdserver` and `storage/schema` with bodies, and the packages their types
  name types- or names-only (zap, bbolt, `net/http`, ...); its raft dependency
  (`go.etcd.io/raft/v3` v3.7.0) is the raft above, which the etcd project does not translate
  (`-lean-root go.etcd.io/raft/v3=`).
- From the same fork (branch `goose-lean-walfs2`, the WAL's fixes 0001-0006 rebased onto `lean`'s etcd pin
  `6e8f0c004`, head `8c28a4296`: `notes/wal-fsext-fork/README.md`),
  etcd's real WAL with bodies over the per-byte file extension's `os`: `server/v3/storage/wal` (but
  `version.go`, `metrics.go`), `wal/walpb`, `client/pkg/v3/fileutil`, `pkg/v3/ioutil`, `pkg/v3/crc`, and
  the standard-library packages they call that Perennial does not translate (`bufio`'s `Reader`,
  `path/filepath`'s lexical functions over `internal/filepathlite`, `hash/crc32` names only); its proofs
  are `Proof/go_etcd_io/etcd/server/v3/storage/wal/` (`Link.lean`: `etc/gen-link.py --walfs`; trust
  base `etc/tcb-collections/wal-fsext.txt`). Until 2026-11-15 in the part `LinuxFs/`, with the main
  tree's names-only WAL beside it (`notes/wal-lean-integration.md`).
- `RaftWitness/{Code,GeneratedProof}/`: the witness experiment's raft (project `raft-witness`:
  the fork's branch `raft-witness-goose-lean`, commit `99cb9e2d9`, etcd-io/raft#168 rebased onto
  `raft37-goose-lean-a1` with fixes; the same packages and configuration as `raft`,
  `RaftWitness/Code/**.toml`) and `examples/raft/kvwitness` (project `kvwitness`, a Go module whose
  `go.mod` replaces raft by that commit), modules `RaftWitness.Code.go_etcd_io.raft.v3`, ....

A proof that needs a prophecy the Go code does not have gets it from a **prophecy patch**,
`etc/proph-patches/<project>/*.patch`, which `etc/goose.py` applies to a copy of the source before
translating (and `etc/verified-code.py` reads): it may only add `primitive.NewProph()`, its
`ResolveBool`/`ResolveU64` calls (which do nothing in Go) on read-only expressions, and `if`s on
read-only conditions holding only such statements. The rule widens (Upamanyu, #24):
- a patch may add prophecy-only declarations: a `ProphId` field or package variable initialized only by `NewProph`, and helper functions whose bodies hold only read-only computation plus `Resolve*`;
- it may add calls to them at statement level or inside `if`s on read-only conditions;
- `etc/prophcheck` checks that erasing every added declaration and call gives back the original files, and refuses an added field in a struct the program compares with `==`, uses as a map key, or reflects on.

A read-only expression may fail, which only adds failing behaviors the proof rules out. The exact
checks: `notes/proph-patch-rule.md` and `etc/prophcheck/main.go`'s doc comment. Never put anything
else in such a patch; a code change goes to the fork (`notes/decisions.md`, "Prophecies as patches
of the Go code").

goose's `-lean-root PKG=` maps every non-standard-library Go path a translation
reaches to the empty root (`Code.<pkg>`), keeping the modules out of the
`Perennial.*` names (which Lake resolves to the Perennial library);
standard-library packages are Perennial's.
`etc/goose.py` regenerates both (after bumping the Perennial or a project pin, or
editing the Goose configuration `Code/**/*.toml`; `--project NAME` for one);
`etc/goose.py --check` exits 1 if they differ from what the pinned translator
produces, or if the examples' Go modules (`examples/go.mod`, one for every example but
`examples/raft/kvwitness`, which has its own, and the driver `examples/lib/lintest`) replace etcd or raft by another revision than the
pins (bump both together), and CI runs that check before the build. `--src NAME=DIR` (or
`$ETCD_SRC`, `$ETCD_RAFT_SRC`) translates from a local checkout of the project instead
of cloning the pin, e.g. for a pinned revision not yet pushed; the output says so,
and `--check` then requires the checkout to be at the pinned revision. It runs `go` with
`GOTOOLCHAIN` set to its pinned `GO_TOOLCHAIN` (Go fetches it if absent): the standard-library
packages are translated from the toolchain's source, which differs between patch releases
(go1.27.1's `net/http` broke `--check` against go1.27.3's). To try a translator change before it is in Perennial,
`etc/goose.py --perennial ../perennial` regenerates with that checkout's translator, and
`lake build --packages=<file>` (a copy of `lake-manifest.json` whose `perennial` entry is
`{"type": "path", "name": "perennial", "dir": "../perennial", ...}`) builds against it
without touching `.lake/packages/perennial`, which other worktrees share;
`LAKE_OPTS=--packages=<file> etc/tcb-report.py` runs the TCB report the same way.

## Changes to Perennial

The pin follows Perennial's branch `lean`. A Perennial change this repository needs goes on
a branch off Perennial's `lean` and lands there by Perennial's own workflow (its
`AGENTS.md`, `etc/land.sh`); the pin then moves to it. Delete such branches once merged, as
above.

Perennial (the Go framework, its standard-library models and Goose) is a shared,
general-purpose dependency. Do not change it to unblock a particular proof: no model
assumption, axiom or spec added to Perennial because a proof here is stuck, and no
change shaped by one proof's needs. When a proof hits a limitation of Perennial (a missing
or too-weak spec, a translator gap, a tactic problem), record it (an entry in
`notes/perennial-changes.md`, the running list of the Perennial changes this repository
needs; `notes/STATUS.md`, and `notes/decisions.md` for the reasoning), work around it locally in this repository (a lemma,
a clearly marked trust-boundary axiom here, or a local override, like `stepLeader.lean`'s
`iframe ∗`), and propose the general fix as an independent Perennial change, designed and
reviewed on its own. Pin bumps that bring such general changes are fine. (The cautionary
case: Perennial `9092f8eaa` made `WaitGroup.Add`'s counter overflow a model assumption, which
was false; `105fb79f5` reverted it in favour of thread tokens. `notes/STATUS.md`, "The
wait-group counter and thread tokens".)

## Building

`lake build` (needs the `elan` toolchain in `lean-toolchain`).

`etc/timed-build.py [LAKE_ARGS…]` is `lake build LAKE_ARGS` that also records each
module compile's timing (`.lake/build-report/`); it leaves the same build behind and
exits with Lake's status. Only the modules it compiles are timed: one a plain `lake
build` compiled stays untimed until it changes. `etc/build-report.py` only reads:
it reports on the latest recorded build (`--build ID` another, `--list` lists them):
wall and CPU time, parallelism over time, the critical path (with Lake's idle time
per step), the unlimited-cores bound, the slowest modules and where the CPU went.
CI (`.github/workflows/lean.yml`) builds with `etc/timed-build.py` and puts the
report on the run's summary page.

## Checking a proof while editing it

`etc/lean-check.py FILE...` checks files through a Lean server it keeps running in the
background (`.lake/lean-check/`, started on the first check, gone after an hour unused), with
the files open: after an edit, Lean re-elaborates only from the first changed tactic on, as an
editor does, where `lake build` and `lake env lean` elaborate the whole file every time. It prints
the errors and warnings like `lake build` (`-q`: errors only) and exits 1 on an error. Use it
for the edit-check loop of a proof; `lake build` stays the check of record (and writes the
`.olean`s other files import).

- `--goal LINE[:COL]` prints the proof state there (the Iris context included), instead of
  inserting a `trace_state` or a deliberate error.
- A check returns at the first error in what the edit changed (from the first changed line to
  the end of its declaration), or once that declaration is elaborated without one, without
  waiting for the declarations after it, and says from which line the file is not yet checked;
  errors already elsewhere in the file are listed but do not stop it. The loop for a broken
  proof: fix the first error, check, fix the next. The edited proof re-runs from the fixed
  tactic: a tactic that fails stops the proof there, so a check costs the tactics up to the
  next failure (an error inside a term, `exact foo`, is admitted and elaboration goes on).
  Checking again without an edit, or `-a`, waits for the whole file: do it before relying on
  the file (an edited statement can break a later proof in it).
- `--fast` skips the kernel's check and the linters that walk the whole proof: for the loop
  only (a proof the elaborator accepts can still fail the kernel; `lake build` checks).
- `--split`, for the longest proofs: each `·` block of at least 20 lines (`--split-min N`) is
  proved as an auxiliary theorem when it ends (`Proof/AbstractBullets.lean`, option `abstractBullets`; the
  server's copy gets its import and option, the file does not), so that an edit does not redo
  the instantiation and checking of the other blocks. With `--fast`, an edit near the end of
  `watchGRPCStream.run` (3368 lines) took 54s of CPU instead of 100s; on a 760-line proof the
  gain is small.
- `--status` shows the open files (and the line being elaborated); `--stop` stops the server.

What an edit costs: the tactics from the edit on, plus the work done once per declaration when
its proof is complete, which no snapshot saves (instantiating the proof term, sharing, the
kernel's check, the linters); the latter grows with the length of the proof. Measured
2026-10-26, after an edit near the end of the proof: `lessor.sendKeepAliveLoop` (250 lines) 59s
fresh, 14s after the edit (wall time); `watchGRPCStream.serveSubstream` (760 lines) 114s of CPU
fresh, 53s after the edit (0.4s of it tactics, 18s the kernel), 24s with `--fast`;
`watchGRPCStream.run` (3368 lines) 230s fresh with `--fast`, 100s after the edit, 54s with
`--split`. A short proof re-checks in under a second.
An edit early in a proof re-runs everything after it, so check from the top of what you changed.

To find what a changed statement breaks, do not run a full `lake build` and read the failures:
`etc/importers.py --uses NAME FILE` lists the modules importing `FILE` (directly or not) that mention
`NAME`, `--files` as paths for `etc/lean-check.py`, `--leaves` as the short target list for `lake
build`, `--count` how much a change rebuilds (`notes/spec-first-plan.md`, "The build budget").

When a file an open file imports changes (its content: `touch` does not count), the next check
reopens the file: the server rebuilds the changed imports with Lake, then elaborates the file in
full. An edit to a proof in an imported module (its `Inv*` or lemma files) does not make the
modules importing it stale: Lake rebuilds an importer only when the imported module's public
`.olean` changes, and a proof's body is not part of it (measured: a proof edited, and lines
inserted above it, in `InvReadylog`, left its 60 importers up to date). Changing a statement or
a definition does rebuild the importers, and so does replacing a `sorry` by a proof: the public
`.olean` changes (the theorem no longer mentions `sorryAx`), unlike an edit to a finished proof.
