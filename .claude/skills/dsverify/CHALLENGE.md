# The challenge: what is given, what is yours, what "done" means

## What you are given

A challenge is a tree (its layout: `SETUP.md`) holding one **kit**: a Go distributed
system deployed over the network, and the goal to prove about it. Its `CLAUDE.md` names the kit
`<kit>`, the goal theorem, and the files below.

- **The kit file** `etc/dsv/<kit>.py`: the kit's Goose project (`GOOSE`), its package initializers'
  configuration (`PKGS`, `PROGRAMS`, `HYP_INITS`, ...) and, if the kit uses the generator, its
  `KITGEN` section (`SETUP.md`). `etc/dsv/README.md` documents every name.
- **The Go program** under `examples/dsverify/<kit>/` (a Go module of its own): the system's code,
  and the kit package with its machines: a driver (`Orch`), client machines (`Client(c)`),
  server machines (`Server(id)`), each with a command `cmd/<machine>/main.go`. The driver
  drives the clients through `examples/lib/remote` and panics unless porcupine accepts the history
  (`NET.md`, `TESTING.md`).
- **The translation**: `Dsverify/Code/`, `Dsverify/GeneratedProof/` (Goose's output) and any
  `Dsverify/TrustedCode/` models, generated from the Go by `etc/goose.py`.
- **The environment**, proved and given: the part `Net/` (the net extension's `net`, its specs in
  `Net/Spec/net/`, the remote library's specs in `Net/Spec/.../examples/lib/remote/`, the codec
  helpers, the deployment statement `Net/Statement/`), `Robustness/Statement.lean` (the generic
  statement), the main tree's library specs (`Spec/`, `Proof/`) and Perennial's.
- **The goal**: `Dsverify/Spec/<kit package path>/TopLevelRobustness.lean`, `def <thm>.spec : Prop`
  (nothing else in the file: it is the file an auditor reads), over the definitions of
  `Dsverify/Proof/<kit package path>/TopLevelDefs.lean` (the machines' programs `system`, the
  addresses, the heaps the premises quantify over). You write
  `Dsverify/Proof/<kit package path>/TopLevelRobustness.lean`: `theorem <thm> : <thm>.spec`.
- **The library premise, yours to state**: `<thm>.spec` takes one premise,
  `(∀ G L, letI := heapAt G L; KitLibs remoteGF) →`, over a class `KitLibs` that **you** declare in
  `Dsverify/Spec/<kit package path>/KitLibs.lean` (shipped as an empty template): what the
  system's libraries do that the proof needs and the challenge does not prove. Beside the statement,
  `kitLibs.premise` is that premise on its own: the type of your **non-vacuity instance**
  (below). `etc/kitlibs-check.py` (`etc/dsv/<kit>-kitlibs-check.conf`) checks both; the rules are in "The
  premise rules".
- Possibly generated plumbing (`Mains.lean`, the top-level proof's skeleton, boot tables: files
  whose first line says which generator wrote them) and scaffolds to fill (`Start.lean`'s
  `kit_start`, `sorry`-stubbed).

## What is yours, and what is not

**Not yours** (never edit; a change here makes the result about something else):
- the statement file (with `kitLibs.premise`), `TopLevelDefs.lean`, every `InitHyp` class
  (`Dsverify/Proof/<pkg>/Init.lean`), the kitlibs-check configuration `etc/dsv/<kit>-kitlibs-check.conf`;
- the environment: `Net/`, `Robustness/`, the main tree, Perennial, `examples/lib/` (remote,
  lintest), the kit's driver, the driver's model and codec (what the statement's "porcupine accepts every
  history" means);
- `etc/` scripts other than the kit file (`etc/kitlibs-check.py` and `etc/KitLibsCheck.lean` among them); the
  kit file's statement and premise parts (`KITGEN`'s `statement`, `defs`, `HYP_INITS`).

**Yours**: `KitLibs.lean` (within the premise rules) and the non-vacuity module
`Dsverify/Proof/<kit package path>/KitLibsLinked.lean`; every other `Dsverify/Spec` and
`Dsverify/Proof` file of the kit (specs, invariants,
proofs, links), the kit file's other parts (`GOOSE`'s per-package configuration, `PKGS`, the
generator's proof parts), prophecy patches (below), notes, tests, and fixes to the system's code
under the rules of `TRUST.md` ("Findings") and the challenge's `CLAUDE.md` (which may forbid code
changes; then a bug is reported, not fixed).

## Done

The goal is proved when, from a clean build of the challenge:
1. `Dsverify/Proof/<kit package path>/TopLevelRobustness.lean` proves `theorem <thm> : <thm>.spec`,
   and the statement file is byte-identical to the challenge's (so are the definitions it names, but
   `KitLibs`, which is yours);
2. `#print axioms <thm>` lists `propext`, `Classical.choice` and `Quot.sound`, nothing else: no
   `sorryAx`, no axiom of yours, of a generator, or of the translation (an untranslated declaration
   the proof reaches shows here: `TRUST.md`);
3. `python3 etc/kitlibs-check.py etc/dsv/<kit>-kitlibs-check.conf` accepts: every field of `KitLibs` is a
   library premise, `KitLibs.lean` keeps to its file rules, and the non-vacuity module builds
   `theorem kitLibs_nonvacuity : kitLibs.premise`; it lists the instance's axioms, each of which
   the lab judges true of Go or not (an instance from proved specs needs none: prefer it);
4. the challenge's checks pass (its `CLAUDE.md` lists them: typically `etc/goose.py --check`,
   `etc/gen-init.py --check`, `etc/dsv/kitgen.py --check`, `etc/tier-check.py --check`).

A statement proved over a premise outside `KitLibs`, a `sorry` "to be filled later", or an axiom
outside the non-vacuity module is not done. Say what is left instead. The lab records the
`KitLibs` you end with: fewer and narrower premises are a better result (a field you can prove
from the translation is one you should not assume).

## The premise rules

`KitLibs` is the one place a library's behavior may be assumed; `etc/kitlibs-check.py` checks it
mechanically (its rules: `etc/KitLibsCheck.lean`'s header), and the lab judges what it lists.

- **What a field may be.** Each field of `KitLibs` is (1) a **library spec**: a Hoare triple, or a
  `∀`/`→`/`∧`/`∨`/`∃` of triples, or a definition or structure of them, about a function or method
  of a **library** package (not one of the system's packages, not the driver's, not `net`: its
  specs are proved, use them); (2) a library package's **`InitHyp`** (`Dsverify/Proof/<pkg>/Init.lean`:
  Go runs the package's untranslated initializer without panicking); or (3) **library data**: a
  predicate or type (an exclusive token `Loc → IProp GF`), or a structure of such data whose
  `Prop` fields are library specs. Abstract tokens are best packed as `∃ tok, Specs tok`.
- **What no field may mention.** The system's code, globals or package state (`pkg_id.<system>`),
  the kit's protocol or ghost state, the driver, `Robust`, `DistDeploy` or anything of the
  statement. One exception: a precondition may take a system global's points-to (`globalAddr X ↦
  v`), memory the caller gives up (a registration consuming the variable it registers).
- **The file.** `KitLibs.lean` holds only `def`/`abbrev`/`structure`/`class` declarations (with
  `namespace`, `section`, `open`, `variable`, `set_option linter.*`, `attribute [local instance]`):
  no `instance`, `axiom`, `theorem`, `macro`, `notation`, attribute or `deriving`. It imports only
  the challenge's own modules, never your other files: the lab rebuilds the statement with your
  `KitLibs.lean` alone, so write the library specs you need there (one canonical spec per function
  still: if the tree has a spec of the function, use it).
- **Premises carry Go's real preconditions.** A triple's precondition is what the real code
  needs: a non-`nil` receiver, an exclusive token where the code is not thread-safe, argument
  shapes, a call made once where a second call panics (registrations), the arguments it really
  accepts (a signal relay registers only the signals passed). A premise whose precondition is
  `True` for a function that panics on some input claims too much, and a proof over it proves
  nothing. A function Perennial already gives a body or a model for is never a premise: use its spec.
- **Visible, never an instance.** No `instance` of `KitLibs` (or of an `InitHyp`) may exist
  anywhere. Proofs take the premise from the statement's hypothesis and pass it down as an instance
  argument (`[KitLibs GF]`, a section variable), or its fields.
- **A true instance.** `KitLibsLinked.lean` proves `theorem kitLibs_nonvacuity : kitLibs.premise`
  and is imported by nothing: from proved specs where they exist, else from axioms declared in that
  module only, each one kitlibs-check accepts as a field (about one library function, preferably).
  kitlibs-check lists them; each is a claim about Go the lab reviews. A class nothing satisfies would
  make the statement vacuous.
- **Attack each field** (`TRUST.md`) before you rely on it: a false premise is a failed run, however
  good the proof above it.

## Prophecy patches

A proof that needs a prophecy variable the Go code does not have (an operation whose linearization
point a later event decides) gets it from a **prophecy patch**, `etc/proph-patches/<project>/*.patch`
(the project is the kit's `GOOSE` name, `dsv-<kit>`), which `etc/goose.py` applies to a copy of the
source before translating. Prophecy-only code, nothing else:

- it may add `primitive.NewProph()` and its `ResolveBool`/`ResolveU64`/... calls (which do nothing
  in Go) on read-only expressions, and `if`s on read-only conditions holding only such statements;
- it may add prophecy-only declarations: a `ProphId` field or package variable initialized only by
  `NewProph`, and helper functions whose bodies hold only read-only computation plus `Resolve*`;
  and calls to them at statement level or inside `if`s on read-only conditions;
- erasing every added declaration and call must give back the original files exactly; an added
  field may not be in a struct the program compares with `==`, uses as a map key, or reflects on.

`etc/prophcheck` (`etc/proph_patch.py` runs it) checks this; the challenge's checks run it. A
read-only expression may fail (a nil dereference), which only adds failing behaviors the proof must
rule out. Never put anything else in such a patch; a change to the code's behavior is a fix
(`TRUST.md`, "Findings").
