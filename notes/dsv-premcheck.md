# dsv-premcheck: agent-extensible library premises for dsverify challenges

Branch `dsv-premcheck` (off `lean` 2970851538). The user's decision (option (b), for every case
study, since experiments are repeated): a challenge's fixed statement takes **one** premise over a
class the agent declares, `KitLibs`, and a mechanical checker, `etc/premcheck`, constrains what the
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
KitLibs module). `etc/premcheck.py --variant SPEC OUT --kitlibs-module M` writes it from a landed
statement file (tested on paxos and rabia: `etc/premcheck-test/lean/PremCheckTest/*/Statement.lean`;
for paxos the diff to the landed statement is the premise line alone). kitgen generates the same
text from `KITGEN` (below). `kitLibs.premise` is the non-vacuity instance's type; premcheck checks
that `<thm>.spec`'s first premise after its instance binders is `kitLibs.premise`'s body (defeq).

`KitLibs` is declared in `Dsverify/Spec/<pkg>/KitLibs.lean` (spec tier; it may import
`Dsverify.Proof.<pkg>.TopLevelDefs`, defs tier), namespace `Perennial.<pkg>`, explicit argument `GF`
only (the statement writes `KitLibs remoteGF`; instance binders the agent's, resolved in the
statement's context). The export ships it as the empty template `etc/dsv/challenge-KitLibs.lean`
(`{{...}}` fields: `DEFS_MODULE`, `PKG`, `SYSTEM`, `KIT`, `SPEC_FILE`, `INSTANCE_FILE`). The
non-vacuity instance is `theorem kitLibs_nonvacuity : kitLibs.premise` in
`Dsverify/Proof/<pkg>/KitLibsLinked.lean` (linking tier, imported by nothing).

## etc/premcheck: the rules

`etc/PremCheck.lean` (Lean meta-programming: it must see the elaborated class, unfold the agent's
definitions and find the triples' subjects; Go would only see text) run by `etc/premcheck.py CONF`,
which builds the statement, KitLibs and instance modules first. The full rules and approximations
are in `etc/PremCheck.lean`'s header; in short:

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

**The file** `KitLibs.lean` (parsed, not elaborated): only `namespace`/`section`(not `meta`)/`end`,
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

### Tests (`python3 etc/premcheck.py --selftest`)

Over rabia's environment (`etc/premcheck-test/selftest.modules`, `selftest.conf`: system `rabia`,
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

`etc/premcheck-test/lean/PremCheckTest/` (lean_lib `PremCheckTest`, srcDir there: not a default target,
outside the import tiers' tree, nothing imports it; its modules declare the kits' statement names):

| run | KitLibs | instance | premcheck |
|---|---|---|---|
| `paxos.conf` | the template as exported (empty) | `exact ⟨⟩` | ACCEPTED, 3 axioms, Lean's |
| `rabia.conf` | the ten landed classes as fields (imports the landed library `Spec.lean`s) | 10 axioms, one per class | ACCEPTED, the 10 listed |
| `rabia.conf` + `fixed=` (every module of the closure but the 4 library `Spec.lean`s) | same | same | REFUSED: imports 4 modules not in the challenge |
| `rabiaself.conf` | **self-contained**: the four `Spec.lean`s' definitions copied into KitLibs.lean (namespaces `zl`, `pb`, `rnd`, `sig`) | 10 axioms | see "Results" |
| `rabiabad.conf` | rabia's + the conclusion restated (an agent def over `DistDeploy`/`Robust`) + a triple about `rabia.internal.config.getEnvInt` | + 2 axioms for them | REFUSED: both fields and both axioms |

### Results

See "Progress" for where each was run.

## Interfaces

### kitgen (`dsv-kitgen`; the coordinator relays, not edited here)

`--export-challenge KIT DIR` should, for every kit:
1. **The statement**: write `Dsverify/Spec/<pkg>/TopLevelRobustness.lean` as the variant above
   (theorem name, binders, addresses and step bound from `KITGEN.statement`; `heap_at` always in the
   spec file; imports: `TopLevelDefs`, `Net.Statement.DistDeploy`, `Robustness.Statement`, the remote
   counter's `Shared`, `Dsverify.Spec.<pkg>.KitLibs`; no premise-class imports). `etc/premcheck.py
   --variant` is the reference text (byte-compare against it in a test).
2. **KitLibs**: write `Dsverify/Spec/<pkg>/KitLibs.lean` from `etc/dsv/challenge-KitLibs.lean`
   (`DEFS_MODULE = Dsverify.Proof.<pkg>.TopLevelDefs`, `PKG`, `SYSTEM` the Go module path, `KIT`,
   `SPEC_FILE`, `INSTANCE_FILE = Dsverify/Proof/<pkg>/KitLibsLinked.lean`). Optionally a stub
   `KitLibsLinked.lean` (`theorem kitLibs_nonvacuity : kitLibs.premise := by sorry`: premcheck refuses
   `sorryAx`, so a stub left is caught). It is NOT a fixed file; the statement is.
3. **The lists**: `etc/dsv/<kit>-premcheck.conf` (keys: `etc/premcheck.py`'s docstring):
   `statement_module`, `spec`, `premise`, `kitlibs`, `kitlibs_module`, `kitlibs_file`, `instance`,
   `instance_module`; `system=` the Lean namespace of the kit's Go module (`rabia`,
   `github_com.xiang90.paxos`, `github_com.imdea_software.swiftpaxos`, ...: goose's naming of the
   `go.mod` module path, every package below it denied), `driver=github_com.mit_pdos.etcd_grove.examples.lib`,
   `driver=github_com.anishathalye.porcupine`, `model=net`; `fixed=etc/dsv/<kit>-fixed-modules.txt`, the
   exported tree's Lean modules (`lean_modules(dest)`) minus the agent-owned `KitLibs`/`KitLibsLinked`.
4. **Checks**: add `python3 etc/premcheck.py etc/dsv/<kit>-premcheck.conf` to `{{CHECKS}}`; the
   CLAUDE.md template fields `KITLIBS_FILE`, `NONVACUITY_MODULE` (the skill patch below changes the
   template).
5. **Not shipped**: the landed statement's premise classes that nothing shipped imports are the
   reference solution: leave them out (kitgen's closure-under-imports rule does this once the
   statement no longer imports them; rabia's `proto/Spec.lean` stays, because gen-init's generated
   `message` init imports it and takes `[proto.Hyps GF]`: the agent's `KitLibs` then has a field
   `proto.Hyps GF`, which premcheck accepts by unfolding it). Also leave out
   `etc/premcheck-test/` (its `rabia*` KitLibs are rabia's reference solution); `etc/PremCheck.lean`
   and `etc/premcheck.py` ship. `FIXED_FILES` no longer lists premise class files (the `InitHyp`
   `Init.lean`s stay fixed), nor a `NonVacuityLinked.lean`.
6. **Offline**: nothing new (premcheck runs `lake env lean --run` on the built tree).

### The skill (`dsv-skill`)

`notes/dsv-premcheck-skill.patch` (`git apply` at the root of dsv-skill 420debfa96; checked to apply):
`CHALLENGE.md` ("What you are given", "What is yours", "Done", a rewritten "The premise rules": the
three kinds of field, what none may mention, the file rules, real preconditions, never an instance,
the non-vacuity theorem and its axioms, attack each field), `TRUST.md` (the goal rests on Lean's
three and `KitLibs`; axioms only in the non-vacuity module; library behavior belongs in `KitLibs`,
other hypotheses are working ones to discharge; attack every field), `etc/dsv/challenge-CLAUDE.md`
(`KITLIBS_FILE`, the non-vacuity module, the premcheck check, the "Do not edit" text).

### The lab (statement/comparator-check.sh; described, not edited)

The comparator compares every constant the theorem's type reaches by full `ConstantInfo`
equality, so `KitLibs` (and the definitions KitLibs.lean declares) must be the solution's in the
challenge build too. In the `tree=` mode kitgen's notes already ask for (the challenge workspace a
fresh copy of the exported tree):
1. **Vary exactly one file.** Copy the solution's `Dsverify/Spec/<pkg>/KitLibs.lean` (from the
   solution commit, `git show`) into the challenge copy before building it; nothing else of the
   solution. Its imports must already be challenge modules (premcheck's `fixed=` rule; if one is not,
   the challenge build fails, which is a refusal). Every other constant the statement reaches is the
   challenge's, compared as before; the statement file itself is the challenge's.
2. **The instance module varies too, outside the comparison.** `KitLibsLinked.lean` is not in the
   goal's closure; the goal's permitted-axiom rule is unchanged (so an instance-module axiom the goal
   reached would fail the goal). Build it in the solution workspace (landrun's sandbox).
3. **Run premcheck with the lab's copies**: `etc/PremCheck.lean`, `etc/premcheck.py`, the conf and
   the fixed list from `DIR.lab/` (not the run's tree: the agent could edit those), against the
   solution workspace's build (`lake env lean --run`); failure = the goal step fails ("premise
   refused").
4. **Record per run** `runs/RUN/goal/kitlibs/`: the solution's `KitLibs.lean` and `KitLibsLinked.lean`
   (with sha256), premcheck's full output, and one JSON line for analysis: run, kit, statement
   commit, `fields` (name, kind premise/data, `about`: the library functions and `InitHyp`s, from the
   `field ...: ...; about [...]` lines), instance axioms (name, type, the lab's verdict to fill:
   true/false/unknown), whether the instance used only proved specs. A results table can then
   compare premise sets across runs and arms (e.g. rabia's ten landed premises as the baseline).

## Open questions

1. **The `globalAddr` exception** (rabia's landed `proto.RegisterEnum` takes
   `message.MsgType_value`'s points-to): allowed only at negative polarity. Alternative: refuse
   all system mentions and have rabia's premise use an abstract once-token; that changes a landed
   premise's shape. Kept the exception; the user may prefer the strict rule.
2. **`net` as a model package**: a KitLibs triple cannot be about `net`'s functions, but may mention
   `net` types and Net's predicates (a library function taking a `net.Conn`, e.g. a codec over a
   connection, needs them). Should other proved packages the challenge ships (bufio, encoding/gob,
   the main tree's) be `model=` too, so an agent must use their proved specs instead of assuming?
   The rule "a function with a body or model is never a premise" is in the skill text, not checked.
3. **Fixed definitions are atomic in scans**: premcheck judges a tree constant by name and module,
   never its body (sound while no library module imports the system's; kitgen's export could check
   that).
4. **Truth is not checked**: premcheck checks shape and vocabulary; whether an instance axiom is true
   of Go is the lab's review (premcheck lists them). An instance from proved specs needs no review.
5. **Ordering of the comparator's build**: the lab must copy the solution's `KitLibs.lean` into the
   challenge before exporting it, which means building part of the challenge after seeing the
   solution; the statement file and everything else stays pinned, so the comparison is still
   against the challenge's statement, but the comparator's "challenge exported before the solution
   is compiled" order now holds only for the rest of the tree.
6. **Existing InitHyp rule** ("every `InitHyp` a visible premise of the statement"): in the variant,
   `InitHyp`s are inside `KitLibs` (visible in the agent's file, not the statement). The landed kits
   keep the rule.

## Progress

- Head and checks: see the final report / git log. tier-check ok (227 known), gen-init --check (273
  files, with `PERENNIAL_DIR=/shared/perennial-47ec64a9d`), `proof_roots.namespace()` =
  `Perennial.EtcdGrove.`.
