# Decisions (Lean port)

Why the Lean port is the way it is. Newest last. The design of the proof itself is
recorded on `main` (`notes/decisions.md`); this file only covers choices the port
had to make.

---

## The Rocq module discipline, in Lean

**2026-10-06 · accepted**

`main` gives every Go function four files (`spec_`/`postulates_`/`proof_`/`link_`)
and uses Rocq's module system for two guarantees (main's decisions.md,
2026-09-14 and 2026-09-18): one Hoare triple per Go function, a duplicate being a
build error (`Include` of two signatures with the same label), and a proof that sees
only the *specs* of its callees, never their proofs (opaque ascription), which also
keeps the proofs checking in parallel.

**Decision:** per Go function, `Spec/<fn>.lean` holds `def <fn>.spec : Prop` (the
triple, with its binders); `Proof/<fn>.lean` holds
`theorem <fn>.wp_proof (h₁ : <callee₁>.spec) … : <fn>.spec`, importing only its
callees' `Spec` files; `Link.lean` instantiates each proof with its callees'
results. Lean's global names make a second `<fn>.spec` a build error (the first
guarantee); taking the callees' specs as hypotheses, with only their `Spec` files
imported, is the second. The `postulates_` file becomes the hypothesis list.
Trust-boundary triples are `axiom <fn>.wp_proof : <fn>.spec` and unfinished ones
`sorry`, so `#print axioms` on a result separates them as `main` does with
`Axiom`/`Admitted`.

**Rejected — one file per function holding spec and proof.** Then a caller imports
its callees' proofs, which both exposes them and serializes the build.

## Build timing: a `lean` shim behind a copy of the toolchain

`etc/build-report.py` (the counterpart of `main`'s, which reads what `etc/rocqc.py`
records around each `rocq compile`) needs each module compile's start, end, CPU,
peak memory and exit status. Lake prints only a duration per job, after the fact,
and has no hook around the compiler; it runs `<sysroot>/bin/lean`, with the
sysroot from `LEAN_SYSROOT` when `LAKE_OVERRIDE_LEAN` is set.

**Decision:** `build-report.py build` makes `.lake/build-report/sysroot/`, symlinks
to the real toolchain except `bin/lean`, a shim that runs the real `lean` under
`wait4` and appends one JSON line per compile to `.lake/build-report/<build>.jsonl`;
then it runs `lake build` with those two variables set. Lake's traces do not
depend on the `lean` path (checked: an up-to-date build stays up to date under the
shim), so the shim changes timing only by Python's start-up per compile. The
imports come from the `.setup.json` Lake writes per module (`importArts`: the
transitive imports; the last of them to finish is always a direct one, so the
critical path and the unlimited-cores bound come out the same as with direct
imports).

**Rejected — timestamping Lake's output.** `✔ [n/m] Built M (12s)` gives an end
time (when the line is read) and a duration, but not CPU or memory, and the line
can lag the compile's end.

Lake runs at most one compile per core: in the first full build of this
repository's modules on 24 cores (2026-10-08), 46s ran exactly 24 compiles and
none ran more. So the report treats the cores as Lake's job slots ("all slots
busy"), and "idle" on the critical path is a wait for a free core, Lake's own
work between compiles, or its start-up. Lean also elaborates a module's
declarations in parallel, so the report charts cores busy (each compile's CPU
spread over its run) next to compiles running.

## Build speed: the Protocol umbrella imports only what `Defs` uses

**2026-10-08 · accepted**

`Defs` imported `Protocol`, which imported the whole protocol development, so
`Defs` and everything after it waited for `StepGhost` … `Facts` (the theorems,
`Refinement` alone 23s), which ran one at a time for the first 1m10s. Only
`Model`, `Ghost` and `GhostState` are used by `Defs`/`Inv*` (checked on the
elaborated environment: which modules' constants each module's constants use);
the theorems are used by four proofs (`RawNode__Ready`, `raftLog__commitTo`,
`raft__Step`, `raft__Step/Base`) and, through `Link`, by `Results`.

**Decision:** `Protocol.lean` imports the three, those four proofs import
`Protocol.Facts`. Full build on 24 cores: 3m40s → 3m01s. No definition, statement
or axiom changed: a hash of every root statement, trusted definition (type and
body, auxiliaries included) and axiom is the same before and after.

What limits the build now, measured on that build:

* **Queueing on the critical path (~50s).** Lake has no job limit or priority:
  a compile occupies one of Lean's worker threads (one per core), and the pool
  is FIFO. When `InvRaftPhys` finishes, ~150 specs become ready at once (started
  in reverse order of registration, i.e. of the root's import list), and the
  next module of a critical chain (`Spec.stepLeader`, `InvRawnode`, then their
  proofs) queues behind them and the proofs they release: `Proof.stepLeader`
  waited 36s. **Rejected — ordering `EtcdGrove.lean` by remaining chain
  length:** it does reorder siblings (tried: `stepLeader`'s callee specs ran
  first), but the FIFO wait comes back one step later; 3m06s.
* **The tail (~30s with ≤3 compiles):** `Proof.stepLeader` (66s, 3m14s CPU) and
  `Proof.RawNode__Ready` (52s), each bounded by its longest declaration
  (`wp_stepLeader_noop`/`appresp`/`prop` ~45–50s each; `RawNode.Ready.wp_proof`
  one theorem). Only splitting those proofs into lemmas Lean elaborates in
  parallel would shorten it.
* **CPU (~39 min; what a 4-core CI runner is bound by).** See the next two
  sections: imports and interpreted tactics.

## Build speed: importing (measured, not changed)

**2026-10-08 · measured**

Every module pays ~2s and ~2 GiB before elaborating anything (wall / user+sys,
a file with only the import, 24-core machine otherwise idle):

| imports | wall | CPU | peak memory |
|---|---|---|---|
| nothing (`Init`) | 0.46s | 0.78s | 469 MB |
| `Batteries` | 0.99s | 1.32s | 979 MB |
| `Lean` | 1.50s | 1.86s | 1568 MB |
| `Iris` | 1.68s | 2.02s | 1599 MB |
| `Perennial` | 1.92s | 2.22s | 1911 MB |
| `Proof.go_etcd_io.raft.v3.InvRawnode` | 2.08s | 2.44s | 1990 MB |

Most of it is Lean's own `Lean` package, which Iris's and Perennial's tactics
import. The `.olean` files are `mmap`ed, not copied, but a non-`module` file
(every file here and in Perennial) imports all three parts of each module built
with Lean's module system: core Lean's public `.olean`s are 356 MB, its
`.olean.private`s (proof bodies, private declarations) 1360 MB. A `module` file
imports only the public part: `module` + `import Lean` takes 0.9s and 705 MB,
`module` + `import Iris` (Iris is all `module`s) 1.22s and 861 MB. A `module`
cannot import a non-`module` (`cannot import non-module Perennial.Proof.ProofPrelude
from module`), so this needs Perennial on the module system first, then every
file here (a `module` header and `public`/`@[expose]` where another file needs a
declaration or a `def`'s body, the specs included).

## Build speed: precompiled tactics (measured, needs Perennial)

**2026-10-08 · measured**

Perennial's and Iris's tactics run in Lean's interpreter (`interpretation` in
`-Dprofiler`: 11.2s of `RawNode__Ready`'s ~50s). `precompileModules = true` in
this repository's lakefile fails: Lake then loads each dependency as one shared
library made of the library's roots and what they import, and Perennial's root
does not reach the Goose code (`undefined symbol:
initialize_perennial_Perennial_Code_go__etcd__io_raft_v3`).

Experiment (a copy with edited dependency lakefiles): Perennial's library with
`precompileModules = true` and globs covering the Perennial modules imported
here. Lake then also builds and loads Iris, Batteries and Qq as shared
libraries; precompiling those as well made no further difference (proofs 24m54s
vs 25m06s of CPU). Clean rebuild of this repository's 402 modules, quiet machine:

| | interpreted | precompiled |
|---|---|---|
| wall | 3m01s | 2m52s |
| CPU | 39m01s | 34m48s (−11%) |
| proofs / specs CPU | 28m19s / 6m45s | 24m54s / 6m20s |
| `Proof.RawNode__Ready` | 52s | 43.5s |
| `Proof.stepLeader` | 66s | 65s |

Interpretation drops to ~0 (16ms in `RawNode__Ready`), but part of what the
profiler had charged to it was nested work (IPM instance search went from 5.4s
to 12.2s), so the gain is the 11% measured, not the ~20% `interpretation`
suggested. The cost is native code for the dependencies: building them and this
repository from scratch went from 10m44s to 13m56s; CI caches the dependencies
per pin. To adopt it, Perennial's `lakefile.toml` needs `precompileModules = true`
and a library whose modules include everything downstream imports (e.g. globs
`["Perennial.+"]`: 481 modules, of which this repository builds 242).

---

## `confchange`: translated and proved, Lean-first

**2026-10-08 · accepted**

`confchange.Restore` and `raftpb.ConfState.Equivalent` were the two axioms about core
raft code (main's notes/STATUS.md, "The fourteen axioms"), stated because the code was
not translated. `confchange` is now translated in full
(`EtcdRaft/Code/go_etcd_io/raft/v3/confchange.toml`: `translate` unrestricted) and
`Restore` proved from its callees on the voters-only, non-joint path `newRaft` and
`raft.restore` take. `Restore.spec` is unchanged, so its callers are untouched.

**Decision:** the new functions get the same discipline as the ported ones
(`Spec/<fn>.lean`, `Proof/<fn>.lean`, linked in `Link.lean`), but have no Rocq
counterpart: they are **Lean-first**. `etc/gen-link.py` reads them from
`etc/link-lean-first.txt` (`<fn>: <callees in hypothesis order>`), so `Link.lean` can
still be regenerated. Shared vocabulary (`ConfigSimple`, `addNodeCC`, `opSpec`) is in
`InvConfchange.lean`, outside the discipline like the other `Inv*` files.

**`chain` is specified higher-order.** `chain(chg, ops...)` runs closures; its spec
takes an invariant `I : Nat → Config → Loc → IProp` on the (config, progress map) pair
and, for each `i`, the triple of op `i` from `I i` to `I (i+1)` (`opSpec`). `Restore`
instantiates `I` with "the first `i` voters are in, each with an owned `Progress`" and
proves each `chg.Simple(cc)` closure's triple from `Simple`'s spec. This keeps `chain`'s
proof independent of what the ops do.

**`checkAndCopy` consumes the originals' `Progress` ownership.** Its shallow copy
`ppr := *pr` shares the `Inflights` pointer, so the copies' `ownProgress` need the
originals' inflight rings; the originals come back as bare points-tos (dropped). On this
path they are garbage anyway (`chain` replaces them), except `MakeProgressTracker`'s
empty map, which has none to lose.

**Specs are stated for the case reached, not in general.** `joint` only for a `nil`
outgoing map, `nilAwareDelete` only for a `nil` map, `apply`/`Simple` only for
`[AddNode id]` with `id ≠ 0`, `symdiff` with a postcondition that says only "at most 1
under the two inclusions `Simple` establishes" (the exact count would need a bound on
the maps' sizes to rule out `n++` wrapping, which nothing on this path has). Widening
them is ordinary proof work when a reconfiguration path needs it.

**A Goose bug found on the way.** `cc := cc` (Go's loop-local-copy idiom, used twice in
`Restore`) was translated as "allocate a fresh zero `cc`, then read `cc`", i.e. the new
cell: `defineStmt` wrapped the allocations *around* the assignment it built, so a
right-hand side naming a defined variable read the fresh cell. Every closure would have
captured `NodeID = 0`, which `apply` skips, and `Restore` would have returned "removed
all voters" -- the spec was unprovable against the translation. Fixed in Perennial's
`goose/goose.go` (c35b7710d): every define statement now binds its right-hand sides
(`$r<i>`) first, then allocates the new variables, then stores, as Go evaluates the
right-hand sides before the new names are in scope. (A first fix, 43b7fc480, did this
only for right-hand sides naming a defined variable, via temporaries `$def<i>`.) The
uniform order reorders every `:=` in the translation; in the proofs a `wp_auto` (or a
`wp_pure` workaround) right after a call sometimes has nothing left to step, since the
call's `wp_apply` now also steps the allocation that follows it.

**Rejected -- requiring `voters.Nodup` in `Restore.spec`** to skip the repeated-voter
branch of `makeVoter`. The callers have it, but the spec's comment says it is not
needed and keeping the statement identical is what makes "axiom replaced by theorem"
auditable; the branch cost ~30 lines.

---

## `ConfState.Equivalent`: `reflect.DeepEqual` is the axiom, not the raft code

**2026-10-08 · accepted**

`Equivalent` (confstate.go) sorts copies of the four id slices of both `ConfState`s
and compares the results with `reflect.DeepEqual`. Goose has no model of reflection,
so the raft code is proved and `reflect.DeepEqual` on two `ConfState` values is the
axiom (`reflect` translated names-only in Perennial, like `crypto/rand`), stated as Go's
`DeepEqual` reads on this struct: fields one by one, a slice field equal iff both nil
or both non-nil with equal elements. The nil/non-nil distinction is why the proof
tracks nil-ness: `append([]uint64(nil), s...)` is `nil` for an empty `s`, so the six
empty slices come out `nil` on both sides whatever they were (`wp_slice_append_nil_empty`,
proved from Perennial's `append`/`copy` model without ownership of `s`, since the
callers only know the lengths). Sorted permutations being equal (`sorted_perm_eq`) is
what makes the voter copies `DeepEqual`.

**The closure is proved once.** `s := func(sl *[]uint64) {...}` is called eight times;
its body is copied verbatim from the translation into `sortCopyBody`, its triple proved
for a function value `f` *fixed by hypothesis* to that literal, and the stored closure is
`generalize`d to `f` before the loop, so that `wp_auto` cannot inline it. Two triples
(owned input, input only known empty) rather than one with a disjunction, so each
returns exactly what it took and the caller frames the original voter slice.

**Rejected -- strengthening the callers' premises to `= slice.nil`** for the six empty
slices (which would have let `wp_slice_append` be used). It would change `newRaft`'s
and `raft.restore`'s statements for a fact the proof can establish itself.

---

## `raftLog.slice`: the admission was the `append` model's own assumption

**2026-10-08 · accepted**

`extend` (util.go) computes `need := len(dst) + len(vals)` as a Go `int`, and its spec
required `|dst| + |vals| < 2^63`; `raftLog.slice` could not establish it (the stable
part is bounded by `2^61`, the unstable slice only by `2^63`) and admitted it, Rocq's one
`Admitted` on the election path, "the log fits in memory" (main's
notes/false-statements.md; `InvRaftlog.lean`'s `Hnowrap` comment).

**Decision:** drop the premise. When the sum reaches `2^63`, `need` wraps negative, so
`need <= cap(dst)` holds and the code takes the `append(dst, vals...)` branch; Goose's
model of `append` (`go.append`, `Perennial/Golang/Defn/Slice.lean`) begins with
`sumAssumeNoOverflowSigned`, an *assumption* that `len(dst) + len(vals)` does not
overflow -- Goose models Go's `growslice` "len out of range" panic as an assumption,
everywhere. The overflow case is therefore vacuous under the model, and the admitted
fact was that assumption restated for one call site. `extend.wp_proof` now steps into
`append` in that case and closes it from the assumption. Nothing new is trusted:
Perennial's Go semantics already were ("Not checked by Lean").

**Rejected -- carrying a `< 2^63` bound in `ownRaftLog`** (tried 2026-09-20): no
constant bound survives `appendEntry`'s `append`, for the same reason -- which is why
the model assumes it there too.
