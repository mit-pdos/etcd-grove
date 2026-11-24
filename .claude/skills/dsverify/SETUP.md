# The challenge's layout, its generators, and how to build and check

The challenge is a Lean project (Lake) in the layout below, depending on Perennial (branch `lean`,
pinned in `lake-manifest.json`), with its dependencies already fetched and built: it needs no
network, and has none. Lean's toolchain is the one `lean-toolchain` names; Go is the toolchain
`etc/goose.py` pins (`GO_TOOLCHAIN`).

## Parts and layout

Files are laid out by kind, then by the Go package path; module names follow the paths. The tree has
several **parts** (module roots), each with the same layout inside:

| root | holds |
|---|---|
| `Dsverify/` | the kit: its translation and your specs and proofs (modules `Dsverify.*`) |
| `Net/` | the environment: `net` over the net extension, `examples/lib/remote`, the codec helpers, `net/rpc`, `net/http`, the deployment statement (`Net/Statement/`) |
| the main tree (no prefix) | the framework's extensions (`GooseLang/Ext/`), library specs and proofs shared by every part (`Spec/`, `Proof/`), lintest and porcupine |
| `Robustness/` | the generic statement |

Inside a part:

| path | holds |
|---|---|
| `Code/<pkg>.lean`, `GeneratedProof/<pkg>.lean` | Goose's output, with the configuration `Code/<pkg>.toml` (bodies, names-only, trusted declarations) |
| `TrustedCode/<pkg>.lean` | hand models of a configuration's `trusted` declarations (part of the trust base: you add none) |
| `Spec/<pkg>/<fn>.lean` | **one** Hoare triple: `def <fn>.spec : Prop` (methods: `<T>__<M>.lean`, `T.M.spec`) |
| `Proof/<pkg>/<fn>.lean` | `theorem <fn>.wp_proof (callee specs …) : <fn>.spec`, or `sorry` while unfinished; imports only its callees' `Spec` files |
| `Proof/<pkg>/Defs.lean`, `Base.lean`, `Inv*.lean`, … | the package's predicates, invariants and lemmas |
| `Proof/<pkg>/Init.lean` | the package initializer's theorem (generated: below) |
| `Proof/<pkg>/Link.lean`, `Results.lean`, `*Linked.lean` | linking: each proof applied to its callees' linked results (`theorem T.wp_M : T.M.spec`) |

Why one triple per file and proofs over callee *specs*: a proof depends only on the statements of what
it calls, so proofs are independent (parallel work, cheap rebuilds), and a spec change shows exactly
which proofs it touches. The linking files are where everything meets.

**Link naming.** Only the kit's top-level link file is named `Link.lean`, in namespace
`Perennial.EtcdGrove.dsv<kit>`; name other link files `Results.lean` or `<Name>Linked.lean`. The
trust-base scripts take the common prefix of every `Link` module's namespace, and one `Link` outside
`Perennial.EtcdGrove` renames every entry.

**Never redeclare a name.** The checks load every root together: a name declared twice (in your
files and in `Net/`, the main tree or Perennial) fails them. Search before you declare.

## The kit file `etc/dsv/<kit>.py`

The kit's whole configuration, in one Python file (`etc/dsv/README.md` documents every name);
`etc/goose.py` and `etc/gen-init.py` load it. Never edit those scripts: a kit owns only its file.

- `GOOSE`: the kit's Goose project (`name="dsv-<kit>"`, `local` the Go module's directory,
  `root="Dsverify"`, `lean_roots` the Go paths' Lean roots, `packages`, `owned`, ...).
- `PKGS`, `PROGRAMS`: the packages whose `Init.lean` and the programs whose `PkgTable.lean`
  `gen-init` writes.
- `HYP_INITS`, `HYP_IMPORTS`: the packages whose initializer is a premise (`InitHyp`,
  `CHALLENGE.md`); `MAIN`, `MAIN_GEN`, `OWN`, `special(g)`: the rest of gen-init's configuration.
- `KITGEN` (if present): the input of `etc/dsv/kitgen.py`, below.

## The generators (never edit their output by hand)

A generated file says so in its first line. Change the input and rerun the generator; each has
`--check` (exit 1 if a file differs), and the challenge's checks run them.

- **`etc/goose.py --project dsv-<kit>`**: retranslates the kit's Go (`Dsverify/Code/`,
  `Dsverify/GeneratedProof/`) from its local module, after a change to the Go, to a `Code/**.toml`
  configuration, or to a prophecy patch (`CHALLENGE.md`). Translate with bodies what you prove;
  names-only is for what the statement's premises cover. A Lean doc comment cannot hold a tab:
  `expand_comment_tabs=True` in `GOOSE`, never an edit of the Go.
- **`etc/gen-init.py`**: writes each package's `Init.lean` (`<pkg>.wp_initialize'`: running the
  package's initializer gives its `isPkgInit`) and each program's `PkgTable.lean`. An untranslated
  initializer becomes a trust-boundary axiom of the generated file (`opaqueInitsOk`, `initFuncsOk`)
  unless the package is a declared `InitHyp`: such an axiom in the goal's `#print axioms` means
  your closure reached a package the challenge did not plan for (translate it with bodies, or
  avoid it; `TRUST.md`). It may need to run twice (a part's `Init` depends on `Net/`'s).
- **`etc/dsv/kitgen.py <kit>`** (kits with `KITGEN`): writes the deployment's repetitive files from the
  kit file (each machine's `cmd/<n>/main.go`, `Mains.lean` with each command's `wp_main`, the
  top-level proof's skeleton: the start, each machine's share, one case per machine, the final
  split) and, with `--scaffold`, the hand-written files' starting points once (`Start.lean`'s
  `kit_start`). `--audit` prints what a reader must check of the statement and its premises.
- **Codec generators** (`models/net/rpc/rpcgen.py`, `models/json/jsongen.py`,
  `models/protobuf/pbgen.py`): a kit's codecs and their specs.

## Modules

Every file starts with `module`, imports with `public import`, and opens `@[expose] public section`
after its imports: declarations are public with bodies visible, but an importer loads only the
public part (much less memory and time). A definition sealed inside its file is `@[no_expose]`.

## Import tiers

Specs never import proofs. Every module is in one of five tiers and imports only from its own tier
or lower (`etc/tier-check.py`):

1. **base**: the translations and the framework (`Code/`, `GeneratedProof/`, `TrustedCode/`,
   `GooseLang/`, `Robustness/`, Perennial), every module outside a `Spec`/`Proof` root;
2. **spec**: a module under a `Spec` root;
3. **defs**: a `Proof` module that is neither of the two below (definitions, invariants, lemmas);
   specs and defs may import each other (defs are a spec's vocabulary);
4. **proof**: a `Proof` module declaring `theorem <F>.wp_proof` (one function's proof): it imports
   specs and defs only, its callees through their specs;
5. **linking**: `Link`, `Results`, `TopLevelRobustness` (under `Proof/`), `*Linked`, `Adequacy*`.
   Only a linking module imports a proof or linking module.

So a proof's edit rebuilds only the linking modules above it. A spec or definition that needs
something declared in a proof or linking module gets it moved down into a defs module, name and
statement unchanged. A proof that needs a linked lemma takes its statement as a hypothesis
(`abbrev <lemma>.law : Prop` in a defs module, proved in the linking module and passed by the
`Link`). Write files this way from the start: restructuring later costs a rebuild of everything.
`etc/tier-check.py --check` refuses a violation not in its baseline; `--tier MODULE` prints a
module's tier, its importers and what an edit to it rebuilds.

## Package APIs

Lean's visibility is per module, so a package cannot hide what its own files share. Make the
boundary checkable instead: an API module imports the package's internals non-publicly and marks
what clients must not see `@[no_expose]`; when a client needs a fact of a sealed predicate, add a
**law** to the API module (`PRINCIPLES.md`, "a client does not unfold"). Do this from the first
package that has a client; retrofitting it is expensive.

## Building and checking

- **Build**: `lake build <Module>` for what you changed (`etc/importers.py --leaves FILE...` gives
  the short list of targets a change rebuilds); the goal's module for the check of record. Never two
  large builds at once on one machine. The challenge's `CLAUDE.md` gives the exact commands and any
  memory cap.
- **The edit loop**: `etc/lean-check.py FILE` keeps a Lean server running with the file open: after
  an edit it re-elaborates from the first changed tactic, and returns at the first error
  (`--goal LINE` prints the proof state with the Iris context; `--fast` skips the kernel check for
  the loop). `lake build` stays the check of record.
- **The axioms**: a scratch file importing the goal's module with `#print axioms <thm>`, run with
  `lake env lean FILE`; the top-level proof file ends with the same line.
- **The checks**: the challenge's `CLAUDE.md` lists them (generators' `--check`, `tier-check`,
  `prophcheck`); run them before every merge to the main branch.

## Operating rules (for agents)

- **One stage, one branch, one worktree** (`git worktree add`). Never edit or build in the main
  checkout while agents run; merge a stage into the main branch only after its checks pass.
- **Seeding a worktree's build**: copy (`cp -a`, never hard links: Lake rewrites trace files in
  place) the `.lake/build` of a checkout whose build of a recent main branch just passed. A stale seed
  gives proof failures that are not real.
- **Temporary files on disk**, not a RAM-backed `/tmp`; clean up Go test temp directories.
- **No network**: every dependency is present; a command that tries to fetch (a Go module, a Lake
  package, a toolchain) is a sign it runs outside the challenge's configuration (wrong directory,
  `GOWORK`, `GOFLAGS`): fix that rather than fetch.
- **Commit often**; never push.
