# etc/dsv: one file per dsverify kit

Each kit ported into the part `Dsverify/` (notes/dsv-paxos.md) has one file here, `<kit>.py`
(`paxos.py`), and edits no shared script: `etc/goose.py` and `etc/gen-init.py` load every `*.py`
here (`goose.dsv_kits()`, in name order; files starting with `_`, the generator `kitgen.py` and the experiment scripts' `proxy.py` are skipped). The `Dsverify` lib's
glob in `lakefile.toml` (`Dsverify.+`) already covers every kit's modules, and a kit's trust base is
its own `etc/tcb-collections/dsv-<kit>.txt` (the gates glob that directory).

A kit file is a plain Python module (it may `import os`; it must not import the scripts). Every
name is optional; a kit without `GOOSE` has no goose project.

| name | read by | meaning |
|---|---|---|
| `GOOSE` | goose.py | the kit's project: a dict of `Project`'s fields (`name="dsv-<kit>"`, `local`, `root="Dsverify"`, `lean_roots`, `packages`, `owned`, `std_models`, `module_models`, `expand_comment_tabs`, ...), placed before project `models-net` |
| `PKGS` | gen-init.py | the packages whose `Init.lean` is generated into `Dsverify/Proof/` (those with a `Dsverify/Code/<pkg>.lean`; a `HYP_INITS` package never) |
| `PROGRAMS` | gen-init.py | program package -> its `PkgTable.lean` path, relative to `Dsverify/` |
| `HYP_INITS` | gen-init.py | the packages whose `wp_initialize'` is a trust-boundary axiom, or for gen-init's `DSV_PREMISE_INITS` a premise `InitHyp` (their hand-written `Dsverify/Proof/<pkg>/Init.lean`; "`HYP_INITS`: per-package `wp_initialize'` axioms" below): external here, and every generated file of the kit whose package's closure holds one imports that `Init` |
| `HYP_IMPORTS` | gen-init.py | the `HYP_INITS` packages' imports as the closure sees them: `'all'` (default), `'known'` (those in the inventory), `'none'` (none, and their `PkgInfo` imports none: programs' tables stop there); or a dict, package -> one of these (`'all'` for a package it does not list), for a kit whose hypothesis packages differ. `'none'` only for a package whose initializer runs no import's initializer (names only, `PkgInfo` imports `[]`): a `wp_initialize'` axiom whose condition does not constrain a package the initializer reaches is false (that package is initialized after it, and `ownInitializing` then needs the table's fact for it; dsv-inithyp-fix: net/rpc's and net/http's now `build_get_is_pkg_init_wf`, `'all'`) |
| `MAIN` | gen-init.py | main-tree packages the kit's closure adds to `NET_MAIN` (always the main tree's inventory and instances, with those of their imports `Net/` lacks; not raft's `Init` if listed in `RAFT_INIT`) |
| `MAIN_GEN` | gen-init.py | the `MAIN` packages whose `Init.lean` is generated into the part (default: all of `MAIN`) |
| `OWN` | gen-init.py | the part's own translations of packages the main tree translates otherwise: the main tree's `SPECIAL` does not apply to them |
| `KITGEN` | etc/dsv/kitgen.py | the kit's generated plumbing (below, "Adding a kit"; notes/dsv-kitgen.md), and its `prompt` (`system`, `check`: the system and what its driver checks, for the challenge's opening prompt, `challenge-prompt.txt`) |
| `special(g)` | gen-init.py | returns `{package: configuration}` for the kit's packages, added to `SPECIAL` (`g`: gen-init.py's globals, `g.newvars_cfg`, `g.FIN_PRE`, ...); a package configured twice is an error |

Each kit is generated in a context of its own (`gen-init.py`'s `dsv_kit_raw`): one kit's
`HYP_INITS`, `MAIN` and `OWN` never change another's files. Two kits that generate the same file
(`Dsverify/Proof/bufio/Init.lean`) must generate it identically, or gen-init stops.

Tabs: Lean rejects a tab in a doc comment goose copies from Go. Keep the fork's Go as it is and set
`expand_comment_tabs=True` in `GOOSE`: goose.py replaces the tabs in the translation's comments by
four spaces (a tab elsewhere is an error), in `--check` too.

## `HYP_INITS`: per-package `wp_initialize'` axioms

**Superseded rule** (until 2026-11-25: "`InitHyp`: a visible premise, never an instance"; superseded
by Upamanyu's decision, mit-pdos/etcd-grove#8, 2026-11-25T02:20:53Z: function contracts are
per-function axioms, not premises, and no Iris spec appears in a top-level statement, hidden ones
included; an `InitHyp` premise was such a hidden spec).

A `HYP_INITS` package's `Dsverify/Proof/<pkg>/Init.lean` declares its `wp_initialize'` as a
**trust-boundary axiom**: run once, from a table holding its imports' facts, the package's
initializer establishes its fact. It asserts that **Go runs the package's untranslated initializers
without panicking** -- the same trust as gen-init's `opaqueInitsOk`/`initFuncsOk` axioms. So:
- the axiom states exactly what the class `InitHyp` (the premise it replaces, deleted) stated,
  with the same post; it appears in no top-level statement;
- each axiom has an `axiom`-skill review (`notes/axiom-review/dsv-inits/`), and a package whose
  review refutes the axiom keeps its `InitHyp` premise (gen-init's `DSV_PREMISE_INITS`, whose
  generated sections take it as an instance; the statement's `NonVacuityLinked.lean` instantiates it
  through the test-only `Dsverify/Proof/<pkg>/InitInstancesLinked.lean`,
  `etc/dsv/tools/inithyp-instances.py`): go-redis v8 and grpc (dsv-fix3, 2026-11-25:
  `GODEBUG=fips140=bogus` panics in go-redis's `crypto/tls` closure; a program registering grpc's
  `binarylog.proto` first panics in grpc's initializer), until Upamanyu picks the fix;
- each is counted in the tcb collection of every kit whose programs initialize the package
  (`etc/tcb-collections/dsv-<kit>.txt`, `etc/tcb-report.py --collection ... --check --update`).

Paxos needs none: its statement rests on Lean's three axioms with no hypotheses.

## Per-function axioms (dsv-fix4)

The same rule for the libraries' functions (mit-pdos/etcd-grove#49 fix 4): a library class a kit's
statement took as a premise (`zerolog.Hyps`, `math.rand.Hyps`, `SwiftHyps`, `PbHyp`, ...) becomes
one **trust-boundary `axiom` per Go function**, in `Dsverify/Proof/<pkg>/<fn>.lean` (`<Type>__<Method>`
for a method), stating the class's field verbatim, over a **fixed vocabulary**: where the class was
quantified over predicates (a token, a wire format), they become `opaque` constants
(`math/rand/RngDefs.lean`'s `rngTok`, `encoding/gob/Vocab.lean`), and a pure law of them is an axiom
too. An environment claim (no SIGUSR1 is sent; no `GODEBUG=randseednop=0`) is stated in the axiom's docstring. The top-level proof builds the class
from the axioms (`letI`/`haveI`, or a `*HypsHoldLinked`/`RandsLinked` theorem; in a kitgen kit the
KITGEN statement key `discharged=[(class, term)]`), so the class stays the proofs' vocabulary and
leaves the statement. Each axiom:
- claims no more than the premise it replaces;
- has an `axiom`-skill review by a reviewer given only the axiom, its Go function and its callers
  (`notes/axiom-review/dsv-fix4/`, indexed in `notes/axiom-review/README.md`); **a refuted axiom
  stays a premise** until restated narrowly and reviewed again (dsv-fix6, `notes/dsv-fix6.md`): craq's
  `LogHyp` (`fmt` called an operand's `Format`/`GoString`, which `argOk` admitted) is restated as three
  axioms (`Craq/LogAx.lean`: `LogDefault`, `LoggerPrintf`, `LoggerPrintln`) over an opaque `StdLogger`
  from `log.Default`, a narrowed `argOk` (errors `errPlain`, `Net/Proof/models_lab/ErrFmt.lean`) and
  Go's directive grammar `FmtVerbsOk` (verbs `v s q x X d`), after four refuting rounds survives the
  fifth (`notes/axiom-review/dsv-fix6/log-logger-5.md`), and `craq_remote_robust` lost the premise
  (an open finding beside it: Net's trusted `(*OpError).Error` calls no field method,
  `notes/axiom-review/dsv-fix6/net-operr-error.md`); rabia's
  `zerolog.Hyps` (`Msg` called any writer's `Write`, which `New`'s spec admitted) is restated with
  `New` at the `nil` writer only and the level methods over a points-to of a logger `New(nil)` made
  (`loggerOk`), reviewed in `notes/axiom-review/dsv-fix6/zerolog.md` (survives), and is axioms
  again; quepaxa's `PbHyp` (the messages' representation admitted any value of protobuf's runtime
  fields `state`/`sizeCache`) is restated over a narrowed representation (an owned message's
  `state` unset or its type's own `MessageInfo`, a shared message's runtime fields in a sealed
  invariant) with each kind asking its declaring package's `isPkgInit`, reviewed in
  `notes/axiom-review/dsv-fix6/quepaxa-pb-2.md` (survives with a condition, checked by
  `etc/pb-init-check.py`), and is axioms again;
- is counted in its kits' tcb collections (`etc/tcb-collections/dsv-<kit>.txt`).
Where a pure fact the program could check is what the axiom needs, it goes into the Go code instead
(#49's bar): gryff's `sort.Slice.wp_proofInt32Lt` (retired 2026-11-25) had no length bound, and
pdqsort's heapsort fallback overflows `2*root+1` past `2^62` elements (#18), so `ShortCircuit` now
sorts with `slices.Sort` and short-circuits the reads only while `len(keys) <= maxShortReads`
(`1 << 20`; a read skipped completes by its own replies), proved over Perennial's `slices.wp_Sort`
and `cmp.Less` at `int32` (`Spec/cmp/Less.lean`).
Left premises: craq's `RpcHttpServe` (waits on S5), the go-redis and grpc `InitHyp`s, quepaxa's
`QpVocab`, `GrpcHyp`, `GrpcWorldHyp` (an allocation law of the ghost state) and `MapHyp` (its `ivt`
stands in for Perennial's `sorry` instances of `sync.Map`'s memory: a model fact).

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
run (etcd-grove's experiment scripts run agents in containers that cannot see etcd-grove; the interface is
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
  rabia's reference solution), the experiment scripts (kitgen's `EXPERIMENT`, `etc/dsv/statement/`)
  and the prompt's template `challenge-prompt.txt`, this README's section on them (stripped from
  the exported copy), the landed statement's premise classes nothing else shipped imports,
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
lab's comparator conventions (`etc/dsv/statement/comparator-check.sh`; plus `tree=` and `statement=`),
`MANIFEST.txt` (every module kept or left out, and why), `prompt.txt` (the run's opening prompt:
`challenge-prompt.txt` filled from KITGEN's `prompt`), `OFFLINE.txt` (the toolchains, the built
Perennial and the Go modules a run needs without network) and `kitlibs-check/` (the lab's own copies of
`kitlibs-check.py`, `KitLibsCheck.lean`, the conf and the fixed list, to run against the solution).

The export then runs the leak check (also `--leak-check DIR <kit>`, on any exported tree): nothing of
the kit's or other kits' Lean beyond the plan, no notes, `old/dsverify`, other `.claude` or other
kits' baselines or `etc/kitlibs-check-test/`, every import present, the statement the KitLibs
variant with its conf and fixed list present, and no `sorry` in the statement's closure but Goose's
instances of axiomatized types (`sorry -- axiomatized type`, counted).

## Running an experiment on a challenge

The experiment scripts run a fresh Claude Code agent on an exported challenge, in a container that
sees nothing of the host but the challenge and its prefetched dependencies, and check its result
independently. They are the lab's side of a run: the export leaves them out (and this section of the
README), and nothing of them is mounted in the agent's view but `inside.sh`, the proxy and the two
hooks. `sandbox.sh new` copies the scripts a container mounts into the run (`runs/RUN/etc/dsv/`;
`meta.txt` names the commit), so a change to the checkout (another branch) does not reach a live run;
`verify` and the generic check in `test1` mount the checked run's copy.

| file | what |
|---|---|
| `sandbox.sh` | everything below (`sandbox.sh --help`: its usage): mirrors, module caches, tools, the built Lake packages, runs, their containers and settings, `verify` |
| `challenge-prompt.txt` | the template of a run's opening prompt; `kitgen.py --export-challenge` fills it (KITGEN's `prompt`) into `DIR.lab/prompt.txt` |
| `run.sh` | `run.sh RUN [PROMPT]` (default: the challenge's `prompt.txt`): the token (asked for once), the container checks (`check-env.sh` in the throwaway run `test1`, then `check-env.sh --challenge` in the run's own view), then the agent; `run.sh RUN --continue` resumes |
| `experiment.sh` | unattended runs: `launch RUN [PROMPT]` (`run.sh` in a detached tmux session named RUN, with `loadlog.sh` and `snapshot.sh`), `wait RUN [HOURS] [--finish]`, `done RUN`, `resume RUN MESSAGE`, `finish RUN` (stop, tag the newest branch `final`, `sandbox.sh verify RUN final`) |
| `rundone.py` | whether a run's agent is done (`experiment.sh wait` and `done`): no Lean, Go or test process using the CPU, and either the goal looks proved (no `sorry` left in the stubs or the changed Lean files on the branch `finish` would tag, all committed) with the transcripts quiet for `GOAL_IDLE` minutes (default 10), or no tool call for `IDLE` minutes (default 20) |
| `proxy.py`, `inside.sh` | the allowlisting HTTPS proxy (`serve`, on the host; only `api.anthropic.com` and `platform.claude.com`, every request logged) and its bridge inside; `inside.sh` is the container's pid 2 (the bridge, then claude or a shell) |
| `ask-hook.sh`, `model-hook.sh`, `managed-settings.json` | the managed settings of every run (read-only at `/etc/claude-code/managed-settings.json`): every `AskUserQuestion` is answered "take the option you would recommend and record it as your decision"; every subagent runs on the run's `subagents` model (default opus); workflows disabled |
| `check-env.sh` | the environment and leak checks, in check views only: isolation, the proxy, the tools; with `--challenge`, the exported tree against `DIR.lab/MANIFEST.txt` (and no section of this README on the scripts), the skill's tree hash, `OFFLINE.txt`'s Go, the built packages and the checks `CLAUDE.md` lists (the kitlibs-check, on the tree as exported, refusing the template instance's `sorry` alone) |
| `verify.sh`, `statement/comparator-check.sh`, `statement/goal-check.sh` | the independent check of a result (below) |
| `statement/comparator-tools.sh` | builds the comparator, lean4export, landrun and nanoda into `cache/tools/comparator` |
| `loadlog.sh`, `snapshot.sh` | while a run's container runs, once a minute: the host's load (`load.log`), and the work tree with the agent's other checkouts (its worktrees, under `.lab-worktrees/NAME`) as a commit of `snapshots.git` when something changed (`snapshot.log`: every pass), outside the agent's view |

### The host

- Linux, as root (the commands that need it re-run themselves under `sudo`, keeping `DSV_LAB`, `DSV_TOKEN`, `IMAGE`,
  `LEAN_TOOLCHAIN`), with cgroup v2 and a `systemd-nspawn` that has idmapped bind mounts
  (`--bind=SRC:DST:idmap`; package `systemd-container`);
- `python3`, `git`, `rsync`, `tmux`, `curl`, `flock`, Go in `/usr/local/go` (for the prefetches),
  `elan` with the toolchain of `lean-toolchain`, the `claude` CLI;
- for `statement/comparator-tools.sh`, once, with network: Lean, Go, a C toolchain and `curl` (it
  installs rustup under `cache/tools/comparator` for nanoda); it builds landrun, which needs a kernel
  with Landlock;
- `IMAGE`: a root file system whose `/usr` every container mounts read-only and whose `/etc` each run
  copies (without ssh, sudoers, shadow or machine files), with Go at `/usr/local/go` (the version
  `OFFLINE.txt` names first is then the image's own), e.g.
  ```
  sudo mmdebstrap --variant=minbase --components=main,universe --include=bash,coreutils,git,python3,curl,\
  ca-certificates,build-essential,make,ripgrep,jq,less,procps,psmisc,file,unzip,zip,xz-utils,patch,diffutils,\
  findutils,gawk,sed,grep,tree,time,bc,nano,vim-tiny,locales,tzdata,iproute2,netbase,rsync \
    SUITE "$IMAGE" http://archive.ubuntu.com/ubuntu
  sudo cp -a /usr/local/go "$IMAGE/usr/local/go"
  ```

### The experiment directory

`DSV_LAB` (required) names a directory outside the repository that holds all state: `mirrors/` (bare
git mirrors; inside a run `https://github.com/...` resolves to them), `cache/` (`gomod-challenge`,
the Go module download cache served to a run as a file proxy; `tools`, the frozen
claude binary, elan and Lean toolchain, and the comparator's tools; `lean/lakepkgs-<key>`, the
challenge's Lake packages, built), `prompts/` (opening prompts, optional) and `runs/`. A run
`runs/RUN/` holds the container's root, its copy of the experiment scripts it mounts (`etc/dsv/`), `home/` (the agent's only writable tree: `home/work` is the
challenge's repository, `home/.claude/projects` the transcripts), `goal/` (the export's `DIR.lab`,
`CHALLENGE.txt` and the challenge commit: never in the agent's view), `meta.txt` (the challenge, the
`DIR.lab` files' sha256s, the packages' key, the claude, Lean and Go versions, every mirror's head,
each settings change), `config` (settings), `proxy.log`, `check*.log`, `interventions.log`,
`load.log`, `snapshots.git` (with `snapshot.log`) and `verify-TAG.log`.

### The token

A run authenticates with a `claude setup-token` token in a file of its own, `DSV_TOKEN` (default
`$DSV_LAB/token`, mode 600; `run.sh` asks for it the first time and checks it looks like `sk-ant-...`).
It is bound read-only into the container and exported there as `CLAUDE_CODE_OAUTH_TOKEN` (never on a
command line, never another config dir's credentials). At a usage limit, `experiment.sh wait` swaps in
a token staged beside it as `$DSV_TOKEN.next` (the spent one kept as `$DSV_TOKEN.spent-TIME`) and
resumes the run.

### The steps

```
export DSV_LAB=/path/to/experiments IMAGE=/path/to/image   # outside the repository
S=etc/dsv/sandbox.sh
# once (with network): the tools and the comparator's tools
$S tools                                     # CLAUDE_BIN, ELAN_HOME: where claude and elan are
etc/dsv/statement/comparator-tools.sh
# per challenge
etc/dsv/kitgen.py --export-challenge DIR KIT # DIR and DIR.lab (prompt.txt among it); --no-skill: the control arm
$S mirror https://github.com/OWNER/REPO      # with network: every package of DIR/lake-manifest.json (Perennial,
                                             #   iris-lean, batteries, quote4), holding its pin; tag Perennial's
                                             #   (refs/tags/lab-pin-<rev>) so that no later fetch loses it
$S prefetch --challenge DIR                  # with network: OFFLINE.txt's Go: modules, Perennial's, toolchains
$S lakepkgs DIR                              # offline: the Lake packages, built from the mirrors
$S new test1                                 # once, after the first prefetch: the throwaway run of the
                                             #   generic check and of verify
$S new RUN --challenge DIR                   # as root (sudo)
# the run
etc/dsv/experiment.sh launch RUN [PROMPT]    # default: the challenge's prompt.txt; PROMPT: a file, or NAME
                                             #   for $DSV_LAB/prompts/NAME.txt
etc/dsv/experiment.sh wait RUN               # DONE, TIMEOUT, EXITED or DIALOG (sudo tmux attach -t RUN);
                                             #   --finish: then finish (at DONE or EXITED)
etc/dsv/experiment.sh finish RUN             # tag final, verify: runs/RUN/verify-final.log
```

What a challenge needs offline is `DIR.lab/OFFLINE.txt`'s list, and each line has its step: the Lean
toolchain (`sandbox.sh tools`, checked against `lean-toolchain` by `new`), Perennial at its pin with
its packages (the mirrors at the manifest's pins, then `lakepkgs`), the Go toolchains and the Go
modules (`prefetch --challenge`, which also fetches what goose's build from Perennial's pin needs).
Nothing else is mirrored or prefetched: `test1`'s generic check covers isolation, the proxy and the
tools, and `check-env.sh --challenge` the rest, in the run's own view.

`new --challenge` refuses unless `DIR.lab` is beside `DIR`, the toolchain is the runs' (`LEAN_TOOLCHAIN`,
default this repository's `lean-toolchain`), the built packages exist and every Go need of
`OFFLINE.txt` resolves offline through the run's file proxy. It copies `DIR` as the work tree (so its
`CLAUDE.md` is the session's), moves the skill to the run's config dir (its tree hash checked against
`CHALLENGE.txt`), copies the built packages into `.lake/packages`, and makes the work tree a fresh
repository with one commit, the challenge as exported (tag `challenge`). A run half made is removed.

The opening prompt (`challenge-prompt.txt`, filled by the export) says where the challenge is
(`/home/agent/work`), to read its `CLAUDE.md` and the skill, what the goal is and which file is the
agent's, that the machine is offline, that nobody answers questions (each gets the automatic reply),
what the final check does, and to commit as it goes. Settings
of a run (`sandbox.sh set RUN KEY VALUE`, applied at every start): `cpus`, `memory` (a hard cap, no swap),
`model` (default opus), `subagents`, `fable`, `context`. To run two arms side by side, give each its
own CPUs and memory.

### What verify checks

`sandbox.sh verify RUN TAG` (`experiment.sh finish`: `final`, the newest branch) checks out the work
tree at TAG into the throwaway run (`VERIFY_RUN`, default `test1`), with the built packages and
`runs/RUN/goal` beside it as `.goal`, and runs `verify.sh` in its check view:
1. HEAD descends from the challenge commit;
2. `statement/comparator-check.sh` (its `tree=` mode): a fresh workspace from the challenge commit
   (`git archive`), the challenge module `DsvChallenge` (`DIR.lab/comparator/Challenge.lean`) built
   from exported files only; then the solution's files added: those the commit adds, changes or deletes
   under the kit's Lean trees (`Dsverify/{Spec,Proof,Code,GeneratedProof}/<the kit's Go module path>`),
   nothing else; a change to a fixed file (`CLAUDE.md`'s "Do not edit") or to a module of the
   statement's import closure is refused, but the `KitLibs` file when the challenge has a
   kitlibs-check. The comparator compares the theorem with the exported statement, permits Lean's three
   axioms only, and replays it in Lean's kernel and nanoda's; the kitlibs-check then runs in landrun.
   Output: PASS/FAIL lines and `RESULT {json}`;
3. `statement/goal-check.sh`, "done" as the challenge's `CHALLENGE.md` states it: the fixed files and
   the environment (`Net/`, `Robustness/`, `GooseLang/`, `examples/lib/`, `models/`, `Spec/`, `Proof/`,
   `etc/` but the kit file and its prophecy patches, the lakefile, manifest and toolchain) unchanged
   since the challenge commit; `lake build` of the goal's module; `#print axioms` Lean's three only;
   the non-vacuity module and the kitlibs-check, if any; every check `CLAUDE.md` lists.

The log ends with `verified` or `NOT verified`. The comparator's tools must be built on the machine that
verifies.

### Analyzing a run

Four scripts read a finished (or live, read-only) run: its transcripts (`home/.claude/projects`), the
work tree's git history, `snapshots.git`, `meta.txt`, `load.log` and `verify-*.log`. Each takes runs
by name (`$DSV_LAB/runs/RUN`) or by path (anything with a `/`), several side by side, and needs root
(the transcripts are the container's). Times are active minutes from the run's first transcript
line: a gap of 30 minutes with no transcript line anywhere (a usage limit, a stopped session) is a
pause and does not count.

```
sudo DSV_LAB=$DSV_LAB etc/dsv/tokens.py [--json] RUN...   # tokens per run: main session, subagents, all
                                                          #   (each API response once); --json adds active minutes and pauses
sudo DSV_LAB=$DSV_LAB etc/dsv/backtrack.py [-v] RUN...    # from snapshots.git: spec rewrites (late: a dependent proof
                                                          #   was finished), proof rewrites and regressions, invalidated
                                                          #   proofs, cascades, churn; -v lists them
sudo DSV_LAB=$DSV_LAB etc/dsv/parallel.py [-v] RUN...     # subagents running per minute (0 / 1 / 2-3 / 4+), the mean, and
                                                          #   the main session's idle polling; -v each subagent's spans
sudo DSV_LAB=$DSV_LAB etc/dsv/compare.py RUN...           # all of it side by side, with the git history's spec-first
                                                          #   phases (review, freeze, specs before proofs) and the verdict
```

`compare.py` imports `tokens` and `backtrack`; their definitions (what counts as a response, a pause,
a late rewrite, a cascade) are fixed, so that numbers stay comparable between runs. `compare.py`'s
`skill tree` is read from `meta.txt`'s `skill:` line (`tree X`).
