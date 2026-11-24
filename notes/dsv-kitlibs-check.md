# dsv-kitlibs-check (branch `dsv-premcheck`): agent-extensible library premises for dsverify challenges

Branch `dsv-premcheck` (off `lean` 2970851538; the tool was named premcheck until the user's rename to
`kitlibs-check`, 2026-11-24, following `etc/<thing>-check.py`; the branch keeps its name). The user's decision (option (b), for every case
study, since experiments are repeated): a challenge's fixed statement takes **one** premise over a
class the agent declares, `KitLibs`, and a mechanical checker, `etc/kitlibs-check`, constrains what the
class may say. The landed kits keep their own statements; the challenge statement is a generated
variant, and a landed kit's premises are one solution of it (a reference solution the export does
not ship).

## The statement (challenge variant)

```
def kitLibs.premise : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics] [<m>_sem : cmd.<m>.Assumptions]...
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj],
    ∀ G L, letI := heapAt G L; KitLibs remoteGF

def <thm>.spec : Prop :=
  ∀ [GoGlobalContext] ... [go.BasicIntoValInj],
    (∀ G L, letI := heapAt G L; KitLibs remoteGF) →
    ∀ (σ : Nat → state) (g : GlobalState) (threads : Nat),
    DistDeploy <addrs> (system σ) g →
    Robustness.Robust [] (system σ) g threads (2 ^ 63)
```

the binder block, `DistDeploy`/`Robust` lines and theorem name the landed statement's, its
premises replaced by the one `KitLibs` premise, `heapAt` defined in the statement file, the imports
the landed file's but the premise classes' (+ the remote counter's `Shared` for `remoteGF`, + the
KitLibs module). `etc/kitlibs-check.py --variant SPEC OUT --kitlibs-module M` writes it from a landed
statement file (tested on paxos and rabia: `etc/kitlibs-check-test/lean/KitLibsCheckTest/*/Statement.lean`;
for paxos the diff to the landed statement is the premise line alone). kitgen generates the same
text from `KITGEN` (below). `kitLibs.premise` is the non-vacuity instance's type; kitlibs-check checks
that `<thm>.spec`'s first premise after its instance binders is `kitLibs.premise`'s body (defeq).

`KitLibs` is declared in `Dsverify/Spec/<pkg>/KitLibs.lean` (spec tier; it may import
`Dsverify.Proof.<pkg>.TopLevelDefs`, defs tier), namespace `Perennial.<pkg>`, explicit argument `GF`
only (the statement writes `KitLibs remoteGF`; instance binders the agent's, resolved in the
statement's context). The export ships it as the empty template `etc/dsv/challenge-KitLibs.lean`
(`{{...}}` fields: `DEFS_MODULE`, `PKG`, `SYSTEM`, `KIT`, `SPEC_FILE`, `INSTANCE_FILE`). The
non-vacuity instance is `theorem kitLibs_nonvacuity : kitLibs.premise` in
`Dsverify/Proof/<pkg>/KitLibsLinked.lean` (linking tier, imported by nothing).

## etc/kitlibs-check: the rules

`etc/KitLibsCheck.lean` (Lean meta-programming: it must see the elaborated class, unfold the agent's
definitions and find the triples' subjects; Go would only see text) run by `etc/kitlibs-check.py CONF`,
which builds the statement, KitLibs and instance modules first. The full rules and approximations
are in `etc/KitLibsCheck.lean`'s header; in short:

**Each field** of `KitLibs` must be one of
1. a **library spec**: `∀`/`→`/`∧`/`∨`/`∃`(over data)/`True`, definitions and `Prop` structures
   (the agent's or the tree's, unfolded), down to Iris entailments whose conclusion is a WP (a
   triple) whose **subject** calls a function (`functions F _`, `@! F`) or method (`methods T m _`,
   `r @!! T @!! m`) with `F`/`T` declared in a Goose `Code` module of a package that is not a
   `system=`, `driver=` or `model=` package (`net`: its specs are proved, never assumed);
2. an **`InitHyp`** class of a library package (`<pkg>.InitHyp GF`);
3. **library data** (a non-`Prop` field: types, predicates; a structure of data whose `Prop`
   fields are library specs).

**Everywhere** in a field (and in the class's parameters), a constant not the agent's must not be
denied: by name (`Perennial.<pkg>...`, `Perennial.pkg_id.<pkg>...`) or by module
(`<root>.<tier>.<pkg>...`) of a system or driver package, or a module of the conclusion
(`Robustness.*`, `Net.Statement.*`). The one exception: `globalAddr X` of a system global at
**negative** polarity (a precondition giving memory up: rabia's landed gogo `proto.RegisterEnum`
consumes `message.MsgType_value`'s points-to). A positive WP nested in a postcondition may have a
variable subject (a closure the library returned); at a negative WP (a callback's spec) any subject.

**The file** `KitLibs.lean` (elaborated again over its own imports, so scoped notation parses as in
the build; an elaboration error refuses it; then each command is checked): only `namespace`/`section`(not `meta`)/`end`,
`open`, `variable`, `universe`, `set_option linter.*|maxHeartbeats|maxRecDepth|autoImplicit|
relaxedAutoImplicit`, `attribute [local instance] ...`, doc comments, and `def`/`abbrev`/
`structure`/`class` (attributes only `reducible`/`irreducible`/`expose`; no `deriving`, `unsafe`,
`partial`, `meta`). With `fixed=`, its imports must be modules of the challenge as exported (so the
lab can rebuild the statement with this one file swapped in). In the environment: the module
declares no axiom, opaque constant or instance; no instance of `KitLibs` exists anywhere.

**The instance**: `instance=` exists (built), its type is defeq to `premise=`, and its axioms
(`collectAxioms`) are listed: Lean's three; the instance module's, each of which must itself pass
rule 1 or 2 (listed with its type "to judge: true of Go?"); with `fixed=`, the fixed tree's (the
trust base, listed); anything else refused, `sorryAx`/`ofReduceBool`/`ofReduceNat`/`trustCompiler`
always. Each field is reported with what it is about (`field proto: premise; about [...RegisterEnum,
...]`), for the lab's record.

### Tests (`python3 etc/kitlibs-check.py --selftest`)

Over rabia's environment (`etc/kitlibs-check-test/selftest.modules`, `selftest.conf`: system `rabia`,
driver `examples/lib` and porcupine, model `net`):
- `fields.lean`, 23 cases, all pass. Accepted: the empty class; rabia's ten landed premises as
  fields (`okRabiaLanded`); the agent's own abbrev/structure/data token/`∃ tok, Specs tok`
  (`okOwnDefs`); two axioms (a library triple, an `InitHyp`). Refused (each with its expected
  reason): the conclusion (`rabia_remote_robust.spec`), the conclusion restated (`DistDeploy`), `Robust`,
  a triple about rabia's `config.getEnvInt`, a library triple with `isPkgInit pkg_id.rabia...` in its
  precondition, a system global's points-to in a postcondition, the driver's `remote.Check`, the net
  model's `net.Dial`, `False`, `1 = 2`, a ghost update with no triple, a triple about any function
  value, the agent's `opaque`, a system class parameter, data of a system type, a system state hidden
  in an agent abbrev; axioms `False` and a rabia function's triple.
- `file-*.lean`, 15 files: the template accepted; refused: `instance`, `axiom`, `theorem`, `opaque`,
  `inductive`, `macro`, `notation`, `@[simp]`, `attribute [instance]`, `deriving`,
  `set_option pp.all`, `#eval`, `unsafe`, `meta section`.

## Validation on paxos and rabia

`etc/kitlibs-check-test/lean/KitLibsCheckTest/` (lean_lib `KitLibsCheckTest`, srcDir there: not a default target,
outside the import tiers' tree, nothing imports it; its modules declare the kits' statement names):

| run | KitLibs | instance | kitlibs-check |
|---|---|---|---|
| `paxos.conf` | the template as exported (empty) | `exact ⟨⟩` | ACCEPTED, 3 axioms, Lean's |
| `rabia.conf` | the ten landed classes as fields (imports the landed library `Spec.lean`s) | 10 axioms, one per class | ACCEPTED, the 10 listed |
| `rabia.conf` + `fixed=` (every module of the closure but the 4 library `Spec.lean`s) | same | same | REFUSED: imports 4 modules not in the challenge |
| `rabiaself.conf` + `fixed=` | **self-contained**: the four `Spec.lean`s' definitions copied into KitLibs.lean (namespaces `zl`, `pb`, `rnd`, `sig`) | 10 axioms | ACCEPTED, the 10 listed |
| `rabiabad.conf` | rabia's + the conclusion restated (an agent def over `DistDeploy`/`Robust`) + a triple about `rabia.internal.config.getEnvInt` | + 2 axioms for them | REFUSED: both fields and both axioms |

### Results

All run on this host (2026-11-24) at d978562e6c+ (the validation lib built locally, Perennial
47ec64a9d, Lake artifact cache), `etc/kitlibs-check.py CONF --no-build` after the build:
- paxos: ACCEPTED (instance: Lean's 3 axioms).
- rabia (landed classes as fields): ACCEPTED; per field what it is about, e.g. `proto: about
  [RegisterEnum, RegisterType, RegisterFile]`, `zerolog: [Logger.ty, Event.ty, ParseLevel,
  SetGlobalLevel, New]`, `rand: [NewSource, New, Rand.ty, Intn]`, `no_signals: [os.signal.Notify]`,
  six `InitHyp`s; the instance's 10 axioms listed for review (13 with Lean's).
- rabia with `fixed=` (3839 modules: the closure minus the 4 library `Spec.lean`s): REFUSED, its four
  imports (the reference solution) are not challenge modules.
- rabiaself with the same `fixed=`: ACCEPTED, the same ten fields and subjects. Found on the way: the
  copied zerolog `New.spec` wrote `@! New`, which inside `rabia.examples.rabianet` resolved to the
  kit's own `rabianet.New`; kitlibs-check refused the field ("a function of the system package
  `rabia`"): exactly the confusion it exists to catch. Also fixed in kitlibs-check: proofs (`_proof_N`
  auxiliaries of an abbrev) are skipped (proof irrelevance), not refused.
- rabiabad: REFUSED for exactly the two bad fields (`concl`: `DistDeploy`, `Robust`; `getEnvInt`: a
  rabia function) and their two instance axioms; the ten good fields pass.
- `--selftest`: 23 field/axiom cases and 15 file cases, all pass.

Build note for the coordinator: `/shared/tmp/build-slot.sh` fails for this session at
`systemd-run --scope` ("Access denied ... interactive authentication"; the system manager via
polkit). I took slot 1's lock myself (`flock /shared/tmp/etcd-grove-build.lock`) and ran
`systemd-run --user --scope -p MemoryMax=45G lake build ...` with `LEAN_NUM_THREADS=8`, the slot's
limits. The script could fall back to `--user` scopes. (Fixed since: build-slot.sh falls back to a `--user` scope; the landing
builds below went through it.)

## Interfaces

### kitgen (implemented on this branch after `dsv-kitgen` landed on `lean` 54c7e5504e; see "Landing")

`--export-challenge KIT DIR`, for every kit:
1. **The statement**: write `Dsverify/Spec/<pkg>/TopLevelRobustness.lean` as the variant above
   (theorem name, binders, addresses and step bound from `KITGEN.statement`; `heap_at` always in the
   spec file; imports: `TopLevelDefs`, `Net.Statement.DistDeploy`, `Robustness.Statement`, the remote
   counter's `Shared`, `Dsverify.Spec.<pkg>.KitLibs`; no premise-class imports). `etc/kitlibs-check.py
   --variant` is the reference text (byte-compare against it in a test).
2. **KitLibs**: write `Dsverify/Spec/<pkg>/KitLibs.lean` from `etc/dsv/challenge-KitLibs.lean`
   (`DEFS_MODULE = Dsverify.Proof.<pkg>.TopLevelDefs`, `PKG`, `SYSTEM` the Go module path, `KIT`,
   `SPEC_FILE`, `INSTANCE_FILE = Dsverify/Proof/<pkg>/KitLibsLinked.lean`). Optionally a stub
   `KitLibsLinked.lean` (`theorem kitLibs_nonvacuity : kitLibs.premise := by sorry`: kitlibs-check refuses
   `sorryAx`, so a stub left is caught). It is NOT a fixed file; the statement is.
3. **The lists**: `etc/dsv/<kit>-kitlibs-check.conf` (keys: `etc/kitlibs-check.py`'s docstring):
   `statement_module`, `spec`, `premise`, `kitlibs`, `kitlibs_module`, `kitlibs_file`, `instance`,
   `instance_module`; `system=` the Lean namespace of the kit's Go module (`rabia`,
   `github_com.xiang90.paxos`, `github_com.imdea_software.swiftpaxos`, ...: goose's naming of the
   `go.mod` module path, every package below it denied), `driver=github_com.mit_pdos.etcd_grove.examples.lib`,
   `driver=github_com.anishathalye.porcupine`, `model=net`; `fixed=etc/dsv/<kit>-fixed-modules.txt`, the
   exported tree's Lean modules (`lean_modules(dest)`) minus the agent-owned `KitLibs`/`KitLibsLinked`.
4. **Checks**: add `python3 etc/kitlibs-check.py etc/dsv/<kit>-kitlibs-check.conf` to `{{CHECKS}}`; the
   CLAUDE.md template fields `KITLIBS_FILE`, `NONVACUITY_MODULE` (the skill patch below changes the
   template).
5. **Not shipped**: the landed statement's premise classes that nothing shipped imports are the
   reference solution: leave them out (kitgen's closure-under-imports rule does this once the
   statement no longer imports them; rabia's `proto/Spec.lean` stays, because gen-init's generated
   `message` init imports it and takes `[proto.Hyps GF]`: the agent's `KitLibs` then has a field
   `proto.Hyps GF`, which kitlibs-check accepts by unfolding it). Also leave out
   `etc/kitlibs-check-test/` (its `rabia*` KitLibs are rabia's reference solution); `etc/KitLibsCheck.lean`
   and `etc/kitlibs-check.py` ship. `FIXED_FILES` no longer lists premise class files (the `InitHyp`
   `Init.lean`s stay fixed), nor a `NonVacuityLinked.lean`.
6. **Offline**: nothing new (kitlibs-check runs `lake env lean --run` on the built tree).

**As implemented** (`etc/dsv/kitgen.py`, section "The challenge's library premise"):
- The statement: `kitlibs_spec_file` runs `etc/kitlibs-check.py`'s `variant_text` over kitgen's own
  `spec_file` (from KITGEN), so it is the reference text by construction (kitgen's header line
  aside); checked against the built and validated `KitLibsCheckTest/{paxos,rabia}/Statement.lean`
  (equal, the KitLibs module's name aside). `CHALLENGE.txt` says `statement: kitlibs`, and
  `kitgen --check` in a challenge then compares the statement with the variant.
- The challenge plan's statement closure is the variant's (its imports), so the landed premise
  classes are not "statement" modules; the kit's `NonVacuityLinked` is never on the allow-list; a
  landed premise class file that no shipped module but the statement imports is left out.
- The fixed list is the exported tree's modules plus the packages' and Lean's built modules (else
  `KitLibs.lean` could not import Perennial or Iris), minus `KitLibs`, `KitLibsLinked` AND the goal's
  proof module (an axiom there would otherwise pass as the fixed tree's).
- `DIR.lab/kitlibs-check/` holds the lab's copies of `kitlibs-check.py`, `KitLibsCheck.lean`, the conf
  and the fixed list. The leak check also requires the variant statement, the conf and the fixed
  list, and no `etc/kitlibs-check-test/`.

### The skill (`dsv-skill`)

`notes/dsv-kitlibs-check-skill.patch` (`git apply` at the root of dsv-skill 420debfa96; checked to apply):
`CHALLENGE.md` ("What you are given", "What is yours", "Done", a rewritten "The premise rules": the
three kinds of field, what none may mention, the file rules, real preconditions, never an instance,
the non-vacuity theorem and its axioms, attack each field), `TRUST.md` (the goal rests on Lean's
three and `KitLibs`; axioms only in the non-vacuity module; library behavior belongs in `KitLibs`,
other hypotheses are working ones to discharge; attack every field), `etc/dsv/challenge-CLAUDE.md`
(`KITLIBS_FILE`, the non-vacuity module, the kitlibs-check check, the "Do not edit" text).

### The lab (statement/comparator-check.sh; described, not edited)

The comparator compares every constant the theorem's type reaches by full `ConstantInfo`
equality, so `KitLibs` (and the definitions KitLibs.lean declares) must be the solution's in the
challenge build too. In the `tree=` mode kitgen's notes already ask for (the challenge workspace a
fresh copy of the exported tree):
1. **Vary exactly one file.** Copy the solution's `Dsverify/Spec/<pkg>/KitLibs.lean` (from the
   solution commit, `git show`) into the challenge copy before building it; nothing else of the
   solution. Its imports must already be challenge modules (kitlibs-check's `fixed=` rule; if one is not,
   the challenge build fails, which is a refusal). Every other constant the statement reaches is the
   challenge's, compared as before; the statement file itself is the challenge's.
2. **The instance module varies too, outside the comparison.** `KitLibsLinked.lean` is not in the
   goal's closure; the goal's permitted-axiom rule is unchanged (so an instance-module axiom the goal
   reached would fail the goal). Build it in the solution workspace (landrun's sandbox).
3. **Run kitlibs-check with the lab's copies**: `etc/KitLibsCheck.lean`, `etc/kitlibs-check.py`, the conf and
   the fixed list from `DIR.lab/` (not the run's tree: the agent could edit those), against the
   solution workspace's build (`lake env lean --run`); failure = the goal step fails ("premise
   refused").
4. **Record per run** `runs/RUN/goal/kitlibs/`: the solution's `KitLibs.lean` and `KitLibsLinked.lean`
   (with sha256), kitlibs-check's full output, and one JSON line for analysis: run, kit, statement
   commit, `fields` (name, kind premise/data, `about`: the library functions and `InitHyp`s, from the
   `field ...: ...; about [...]` lines), instance axioms (name, type, the lab's verdict to fill:
   true/false/unknown), whether the instance used only proved specs. A results table can then
   compare premise sets across runs and arms (e.g. rabia's ten landed premises as the baseline).

## Open questions

1. **OPEN (the user has not decided). The `globalAddr` exception** (rabia's landed `proto.RegisterEnum` takes
   `message.MsgType_value`'s points-to): allowed only at negative polarity. Alternative: refuse
   all system mentions and have rabia's premise use an abstract once-token; that changes a landed
   premise's shape. Default kept: the narrow exception. Configurable: the conf's `global_addr=`
   (`negative`, the default; `none`, the strict rule), which kitgen writes from KITGEN's optional
   `kitlibs_check=dict(global_addr=...)`.
2. **`net` as a model package**: a KitLibs triple cannot be about `net`'s functions, but may mention
   `net` types and Net's predicates (a library function taking a `net.Conn`, e.g. a codec over a
   connection, needs them). Should other proved packages the challenge ships (bufio, encoding/gob,
   the main tree's) be `model=` too, so an agent must use their proved specs instead of assuming?
   The rule "a function with a body or model is never a premise" is in the skill text, not checked.
   **OPEN (the user has not decided).** Default: `model=net` only. Configurable: KITGEN's optional
   `kitlibs_check=dict(model=[...])` (also `system`, `driver`) sets the conf's `model=` lines.
3. **Fixed definitions are atomic in scans**: kitlibs-check judges a tree constant by name and module,
   never its body (sound while no library module imports the system's; kitgen's export could check
   that).
4. **Truth is not checked**: kitlibs-check checks shape and vocabulary; whether an instance axiom is true
   of Go is the lab's review (kitlibs-check lists them). An instance from proved specs needs no review.
5. **Ordering of the comparator's build**: the lab must copy the solution's `KitLibs.lean` into the
   challenge before exporting it, which means building part of the challenge after seeing the
   solution; the statement file and everything else stays pinned, so the comparison is still
   against the challenge's statement, but the comparator's "challenge exported before the solution
   is compiled" order now holds only for the rest of the tree.
6. **Existing InitHyp rule** ("every `InitHyp` a visible premise of the statement"): in the variant,
   `InitHyp`s are inside `KitLibs` (visible in the agent's file, not the statement). The landed kits
   keep the rule.

## Landing (2026-11-24)

- Merged `origin/lean` 54c7e5504e (`dsv-kitgen` with the dsverify skill landed): clean, no conflicts.
- `notes/dsv-kitlibs-check-skill.patch` applied to the landed skill files with no drift
  (`git apply --check` clean); then renamed with the tool.
- Renamed premcheck to kitlibs-check (user decision): `etc/kitlibs-check.py`, `etc/KitLibsCheck.lean`,
  `etc/kitlibs-check-test/` (lean_lib `KitLibsCheckTest`), `etc/dsv/<kit>-kitlibs-check.conf`, these
  notes, the patch; every mention in the skill, the template, the README; output prefix
  `kitlibs-check:`, env `KITLIBS_CHECK_LAKE`. Branch name unchanged.
- The export wired (above); both open questions keep their defaults and are configurable.
- Results, this host (`/shared/tmp/build-slot.sh`, Lake artifact cache, Perennial 47ec64a9d):
  - paxos exported from 539fd0c862 (`/shared/tmp/kitlibs-export-paxos`): 37 kit modules, 235 of other
    kits', leak check ok (statement closure 116 modules); fixed list 28,239 modules; in the export
    `kitgen --check --no-codecs paxos`, `tier-check --check` (227 known), `gen-init --check` (273),
    `goose --check --project dsv-paxos` pass. `kitlibs-check.py etc/dsv/paxos-kitlibs-check.conf` in the
    export (2,492 jobs): the shipped `sorry` stub REFUSED (`sorryAx`); with the instance filled
    (`exact ⟨⟩`, as an agent would) ACCEPTED, Lean's 3 axioms, the empty KitLibs passing the `fixed=`
    import rule.
  - `--selftest`: 23 field/axiom and 15 file cases pass (the rename had turned the test namespace
    `premcheckTest` into an invalid identifier; now `kitlibsCheckTest`).
  - The validation lib rebuilt as `KitLibsCheckTest` (2,680 jobs): paxos, rabia, rabiaself ACCEPTED,
    rabiabad REFUSED for exactly its two bad fields and axioms, as before; rabia with `global_addr=none`
    REFUSED on `proto.RegisterEnum`'s `MsgType_value` (the strict rule works).

## Progress

- fk-lean1 was used only before the user's 02:00Z decision (read-only `lake env lean --run` in
  `wt/lean-warm` with scratch oleans in /tmp, since removed; the queued branch build was cancelled
  and the pushed ref deleted there).

- Head and checks: see the final report / git log. tier-check ok (227 known), gen-init --check (273
  files, with `PERENNIAL_DIR=/shared/perennial-47ec64a9d`), `proof_roots.namespace()` =
  `Perennial.EtcdGrove.`.
