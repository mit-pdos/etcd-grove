# The challenge: what is given, what is yours, what "done" means

## What you are given

A challenge is a tree in etcd-grove's layout (`SETUP.md`) holding one **kit**: a Go distributed
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
- **The declared premises**: the hypotheses of `<thm>.spec`, each a `Prop`-valued class of a module
  the statement imports (`Dsverify/Proof/<pkg>/Init.lean`'s `InitHyp`, a library's `Hyps`, an
  environment assumption), and **their non-vacuity instances** (below), if the statement has any.
- Possibly generated plumbing (`Mains.lean`, the top-level proof's skeleton, boot tables: files
  whose first line says which generator wrote them) and scaffolds to fill (`Start.lean`'s
  `kit_start`, `sorry`-stubbed).

## What is yours, and what is not

**Not yours** (never edit; a change here makes the result about something else):
- the statement file, every premise class it names (its `class` and the definitions it is written
  in), `TopLevelDefs.lean`, the non-vacuity module;
- the environment: `Net/`, `Robustness/`, the main tree, Perennial, `examples/lib/` (remote,
  lintest), the kit's driver, the driver's model and codec (what the statement's "porcupine accepts every
  history" means);
- `etc/` scripts other than the kit file; the kit file's statement and premise parts
  (`KITGEN`'s `statement`, `defs`, `HYP_INITS`).

**Yours**: every other `Dsverify/Spec` and `Dsverify/Proof` file of the kit (specs, invariants,
proofs, links), the kit file's other parts (`GOOSE`'s per-package configuration, `PKGS`, the
generator's proof parts), prophecy patches (below), notes, tests, and fixes to the system's code
under the rules of `TRUST.md` ("Findings") and the challenge's `CLAUDE.md` (which may forbid code
changes; then a bug is reported, not fixed).

## Done

The goal is proved when, from a clean build of the challenge:
1. `Dsverify/Proof/<kit package path>/TopLevelRobustness.lean` proves `theorem <thm> : <thm>.spec`,
   and the statement file is byte-identical to the challenge's (so are the premise classes and the
   definitions the statement names);
2. `#print axioms <thm>` lists `propext`, `Classical.choice` and `Quot.sound`, nothing else: no
   `sorryAx`, no axiom of yours, of a generator, or of the translation (an untranslated declaration
   the proof reaches shows here: `TRUST.md`);
3. every premise class keeps its non-vacuity instance building, and no instance of a premise class
   exists anywhere else;
4. the challenge's checks pass (its `CLAUDE.md` lists them: typically `etc/goose.py --check`,
   `etc/gen-init.py --check`, `etc/dsv/kitgen.py --check`, `etc/tier-check.py --check`).

A statement proved over a premise you added, a `sorry` "to be filled later", or an axiom stated
"for the trust boundary" is not done. Say what is left instead.

## The premise rules

The declared premises are the challenge's; you rely on them as given. The rules below say what they
mean (so you use them correctly), and bind every hypothesis you introduce while working (`TRUST.md`).

- **Visible, never an instance.** A premise is a class the statement takes as a hypothesis
  (`(∀ G L, letI := heapAt G L; C remoteGF) →` for each machine's heap), so a reader sees every
  one. **No `instance` of a premise class may exist anywhere**: an instance would need an axiom,
  or be one in effect. A proof gets a premise from the statement's hypothesis and passes it down
  as an instance argument (`[C GF]`, a section variable).
- **`InitHyp`: the initializer runs.** A package translated names-only (its variables'
  initializers or `init` functions not translated) has a hand-written `Dsverify/Proof/<pkg>/Init.lean`
  declaring `class InitHyp GF : Prop` with its `wp_initialize'`. It asserts only that Go runs the
  package's initializer without panicking and establishes the package's `isPkgInit`. The kit file
  lists such packages in `HYP_INITS`, and `etc/gen-init.py` makes every generated `Init.lean` whose
  closure reaches one take `[<pkg>.InitHyp GF]`.
- **Premises carry Go's real preconditions.** A hypothesis about a library function is a triple
  whose precondition is what the real code needs: a non-`nil` receiver, an exclusive token where
  the code is not thread-safe, argument shapes, a call made once where a second call panics
  (registrations), the arguments it really accepts (a signal relay registers only the signals
  passed). A premise whose precondition is `True` for a function that panics on some input claims
  too much, and a statement over it is unsound. A function Perennial already gives a body or a model
  for is never a hypothesis: use its spec.
- **One canonical spec per function.** A function has one spec in the whole tree. Before declaring
  `<F>.spec`, search `Net/Spec/`, `Spec/`, `Dsverify/Spec/` and Perennial for it, and reuse the one
  that exists (the checks load every root together, and a second declaration of a name fails
  them). A special case is a one-line instance of the general spec, never a twin triple.
- **Every premise class has a true instance.** A class nothing satisfies makes the statement
  vacuous. So the challenge ships, for each premise class, a **non-vacuity instance**: a theorem in
  a test-only linking module (`NonVacuityLinked.lean` beside the statement's proof) that builds a
  value of the class from proved specs (or from the environment's models). It is built by the
  checks and imported by nothing. If you come to believe a declared premise is false of the real
  library, or has no instance, that is a finding: stop proving over it and report it with the
  evidence.

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
