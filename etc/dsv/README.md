# etc/dsv: one file per dsverify kit

Each kit ported into the part `Dsverify/` (notes/dsv-paxos.md) has one file here, `<kit>.py`
(`paxos.py`), and edits no shared script: `etc/goose.py` and `etc/gen-init.py` load every `*.py`
here (`goose.dsv_kits()`, in name order; files starting with `_`, and the generator `kitgen.py`, are skipped). The `Dsverify` lib's
glob in `lakefile.toml` (`Dsverify.+`) already covers every kit's modules, and a kit's trust base is
its own `etc/tcb-collections/dsv-<kit>.txt` (the gates glob that directory).

A kit file is a plain Python module (it may `import os`; it must not import the scripts). Every
name is optional; a kit without `GOOSE` has no goose project.

| name | read by | meaning |
|---|---|---|
| `GOOSE` | goose.py | the kit's project: a dict of `Project`'s fields (`name="dsv-<kit>"`, `local`, `root="Dsverify"`, `lean_roots`, `packages`, `owned`, `std_models`, `module_models`, `expand_comment_tabs`, ...), placed before project `models-net` |
| `PKGS` | gen-init.py | the packages whose `Init.lean` is generated into `Dsverify/Proof/` (those with a `Dsverify/Code/<pkg>.lean`; a `HYP_INITS` package never) |
| `PROGRAMS` | gen-init.py | program package -> its `PkgTable.lean` path, relative to `Dsverify/` |
| `HYP_INITS` | gen-init.py | the packages whose `wp_initialize'` is a hypothesis (the class `InitHyp` of their hand-written `Dsverify/Proof/<pkg>/Init.lean`): external here, and every generated file of the kit whose package's closure holds one imports that `Init` and takes `[<pkg>.InitHyp GF]` as a section variable |
| `HYP_IMPORTS` | gen-init.py | the `HYP_INITS` packages' imports as the closure sees them: `'all'` (default), `'known'` (those in the inventory), `'none'` (none, and their `PkgInfo` imports none: programs' tables stop there); or a dict, package -> one of these (`'all'` for a package it does not list), for a kit whose hypothesis packages differ. `'none'` only for a package whose initializer runs no import's initializer (names only, `PkgInfo` imports `[]`): an `InitHyp` whose condition does not constrain a package the initializer reaches is false (that package is initialized after it, and `ownInitializing` then needs the table's fact for it; dsv-inithyp-fix: net/rpc's and net/http's now `build_get_is_pkg_init_wf`, `'all'`) |
| `MAIN` | gen-init.py | main-tree packages the kit's closure adds to `NET_MAIN` (always the main tree's inventory and instances, with those of their imports `Net/` lacks; not raft's `Init` if listed in `RAFT_INIT`) |
| `MAIN_GEN` | gen-init.py | the `MAIN` packages whose `Init.lean` is generated into the part (default: all of `MAIN`) |
| `OWN` | gen-init.py | the part's own translations of packages the main tree translates otherwise: the main tree's `SPECIAL` does not apply to them |
| `KITGEN` | etc/dsv/kitgen.py | the kit's generated plumbing (below, "Adding a kit"; notes/dsv-kitgen.md) |
| `special(g)` | gen-init.py | returns `{package: configuration}` for the kit's packages, added to `SPECIAL` (`g`: gen-init.py's globals, `g.newvars_cfg`, `g.FIN_PRE`, ...); a package configured twice is an error |

Each kit is generated in a context of its own (`gen-init.py`'s `dsv_kit_raw`): one kit's
`HYP_INITS`, `MAIN` and `OWN` never change another's files. Two kits that generate the same file
(`Dsverify/Proof/bufio/Init.lean`) must generate it identically, or gen-init stops.

Tabs: Lean rejects a tab in a doc comment goose copies from Go. Keep the fork's Go as it is and set
`expand_comment_tabs=True` in `GOOSE`: goose.py replaces the tabs in the translation's comments by
four spaces (a tab elsewhere is an error), in `--check` too.

## `InitHyp`: a visible premise, never an instance

A `HYP_INITS` package's `Dsverify/Proof/<pkg>/Init.lean` declares `class InitHyp GF : Prop` holding
that package's `wp_initialize'`. It asserts that **Go runs the package's untranslated initializers
without panicking** -- the same trust as gen-init's `opaqueInitsOk`/`initFuncsOk` axioms it replaces,
moved to where it can be seen. So (#24, upamanyus's condition for this mechanism):
- every `[<pkg>.InitHyp GF]` a kit needs is a **premise of its top-level statement**: it appears in
  the `.spec` of `Dsverify/Proof/<kit>/.../TopLevelRobustness.lean` (the file an auditor reads);
- **no `instance` of an `InitHyp` class may exist anywhere** (it would need an axiom, or be one in
  effect);
- `etc/theorem-loc.py`/`etc/theorem-tcb.py` count each as a statement premise (they follow the
  names the statement mentions); the first kit with a statement over an `InitHyp` confirms this in
  its notes.

Paxos needs none: its statement rests on Lean's three axioms with no hypotheses.

## Challenges: the dsverify skill and the challenge's `CLAUDE.md`

A kit is exported as a **challenge** (a self-contained tree without the kit's proofs, for an agent to
prove; `etc/dsv/kitgen.py --export-challenge KIT DIR`, branch dsv-kitgen) together with two files of
this repository (notes/dsv-skill.md):
- `.claude/skills/dsverify/`: the dsverify skill, the method given to the agent (moved here from
  dsverify-lab's `skill/`). Copied whole into the challenge's `.claude/skills/dsverify/`, or left
  out for a control arm. It must hold nothing an agent must not read: no kit's proofs, no kit's
  known bugs.
- `etc/dsv/challenge-CLAUDE.md`: the template of the challenge's `CLAUDE.md` (the goal, what not to
  edit, how to build and check, no network); its header lists the fields the export fills. The
  same with or without the skill.

## Adding a kit

1. Port the kit's Go into `examples/dsverify/<kit>/` (the fork as its own Go module, the kit package
   `examples/<kitpkg>` on `examples/lib/remote`: `kit.go` with `Orch()`, `Client(c)`, `Server(id)`).
2. Write `etc/dsv/<kit>.py`: `GOOSE`, `PKGS`, `PROGRAMS` (and the rest of the table above), then its
   `KITGEN` section (notes/dsv-kitgen.md, "Inputs"; `paxos.py` is the full example, `swiftpaxos.py`
   a kit adopting only the boot tables): the roles and their machines, the codecs, the statement
   (theorem name, addresses, step bound, premises), and the Lean templates of each role (its share,
   its `wp_main`, ...).
3. Run `etc/goose.py`, `etc/gen-init.py`, then `etc/dsv/kitgen.py <kit>`: the commands' mains,
   `kit_gen.go` (`go_consts`), the codecs (through `models/`'s generators), the statement
   `Dsverify/Spec/<pkg>/TopLevelRobustness.lean`, `TopLevelDefs.lean`, the statement's proof around
   the kit's lemmas, `Mains.lean`, the boot tables (`boot`). `kitgen.py --scaffold <kit>` writes
   the starting points of the hand-written `Start.lean` (`kit_start`) and, if the statement has
   premise classes, `NonVacuityLinked.lean` (one stub per class: the NON-VACUITY rule).
4. Write the proofs (`Kit.lean`, `KitProof.lean`, `Linked.lean`, the protocol's), the premise classes'
   content, and the non-vacuity instances. Never edit a generated file (its first line says it is);
   change the kit file and regenerate. `etc/gates.sh` runs `kitgen.py --check`.
5. Audit: `etc/dsv/kitgen.py --audit <kit>` prints what a reader must check (the statement file, the
   definitions it names, each premise class with its declaration's place and size).

The generator is untrusted: a reader reads the committed statement, not the script.

### Exporting a proving challenge

`etc/dsv/kitgen.py --export-challenge DIR <kit>` writes the kit as a challenge for an automatic-proving
run (the dsverify-lab harness runs agents in containers that cannot see etcd-grove; the interface is
notes/dsv-skill.md's, copied in notes/dsv-kitgen.md). From a clean work tree (`--allow-dirty` notes
a dirty one), `DIR` gets this repository's tracked files but:
- the kit's own Lean (`Dsverify/{Proof,Spec}/<proof_roots>/`) but what KITGEN's explicit
  `challenge_allow` lists: the statement, its definitions and addresses (`addrs_module`), the
  package facts, gen-init's `Init`/`PkgTable` (the challenge gives the driver
  and the theorem; the kit's client spec, protocol specs, start and proofs are the answers: the export
  stops if the statement's closure needs a module off the list, or the list names a proof); the goal's file `Proof/.../TopLevelRobustness.lean` is a `sorry` stub,
  and kitgen's other generated proofs (`Mains.lean`) are left out (`CHALLENGE.txt`'s `omitted:` lines,
  which `kitgen.py --check` in the challenge skips);
- other kits' Lean but what this kit's landed proof uses and what gen-init's generated files import;
- `notes/`, `CLAUDE.md`, `.claude/` but the dsverify skill, `old/dsverify/`, dsverify kits' issues,
  other kits' `etc/tcb-collections/dsv-*.txt`, `etc/kitlibs-check-test/` (its `rabia*` KitLibs are
  rabia's reference solution), the landed statement's premise classes nothing else shipped imports,
  the kit's `NonVacuityLinked.lean`, and every module importing a left-out one;
- **the library premise is the agent's** (notes/dsv-kitlibs-check.md): the statement
  `Spec/.../TopLevelRobustness.lean` is the KitLibs variant (`etc/kitlibs-check.py --variant`'s
  text, generated from KITGEN: the landed premises replaced by `(∀ G L, letI := heapAt G L; KitLibs
  remoteGF) →`, `kitLibs.premise` beside it); `Spec/.../KitLibs.lean` the empty class from
  `challenge-KitLibs.lean`; `Proof/.../KitLibsLinked.lean` a `sorry` stub of `kitLibs_nonvacuity`;
  `etc/dsv/<kit>-kitlibs-check.conf` (KITGEN's optional `kitlibs_check` dict sets `system`, `driver`,
  `model`, `global_addr`; defaults: the Go module's namespace, `examples/lib` and porcupine, `net`,
  `negative`) and `etc/dsv/<kit>-fixed-modules.txt` (the challenge's modules, the packages' and Lean's,
  but the agent's three files), and `python3 etc/kitlibs-check.py etc/dsv/<kit>-kitlibs-check.conf` among
  the checks;
- with the skill `.claude/skills/dsverify/` (or as of `--skill-from REV`; `--no-skill`: the control
  arm), `CLAUDE.md` filled from `challenge-CLAUDE.md` (identical in both arms; `--code-changes`), and
  `CHALLENGE.txt` (the source commit, the kit, the skill's tree hash or `none`, the CLAUDE.md's hash).

Beside it, `DIR.lab/` (outside the agent's tree): `comparator/{challenge.conf,Challenge.lean}` in the
lab's comparator conventions (`statement/comparator-check.sh`; plus `tree=` and `statement=`),
`MANIFEST.txt` (every module kept or left out, and why), `OFFLINE.txt` (the toolchains, the built
Perennial and the Go modules a run needs without network) and `kitlibs-check/` (the lab's own copies of
`kitlibs-check.py`, `KitLibsCheck.lean`, the conf and the fixed list, to run against the solution).

The export then runs the leak check (also `--leak-check DIR <kit>`, on any exported tree): nothing of
the kit's or other kits' Lean beyond the plan, no notes, `old/dsverify`, other `.claude` or other
kits' baselines or `etc/kitlibs-check-test/`, every import present, the statement the KitLibs
variant with its conf and fixed list present, and no `sorry` in the statement's closure but Goose's
instances of axiomatized types (`sorry -- axiomatized type`, counted).
