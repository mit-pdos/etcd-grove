# Challenge: {{TITLE}}

<!-- Template: etc/dsv/kitgen.py --export-challenge fills the {{...}} fields and writes this file as
the challenge's CLAUDE.md. It is identical with and without the dsverify skill (ablation arms),
so it names no skill. Fields:
  {{TITLE}}            the kit's prose name (KITGEN's `title`)
  {{KIT}}              the kit's name (`etc/dsv/<kit>.py`)
  {{GO_DIR}}           the kit's Go module (`examples/dsverify/<kit>`)
  {{THEOREM}}          the goal theorem's name
  {{SPEC_FILE}}        Dsverify/Spec/<kit package path>/TopLevelRobustness.lean
  {{PROOF_FILE}}       Dsverify/Proof/<kit package path>/TopLevelRobustness.lean
  {{PROOF_MODULE}}     the proof file's module name
  {{FIXED_FILES}}      one "- `path`" line per file the goal fixes (the statement, TopLevelDefs.lean,
                       the statement's other kit modules)
  {{KITLIBS_FILE}}      Dsverify/Spec/<kit package path>/KitLibs.lean (the agent's class; shipped empty)
  {{NONVACUITY_MODULE}} the non-vacuity module, Dsverify.Proof.<kit package path>.KitLibsLinked
  {{CHECKS}}           one "  - `command`" line per check the export keeps; by default
                         python3 etc/goose.py --check --project dsv-<kit>
                         python3 etc/proph_patch.py --project dsv-<kit>   (if the kit has patches)
                         python3 etc/gen-init.py --check
                         python3 etc/dsv/kitgen.py --check <kit>          (kits with KITGEN)
                         python3 etc/tier-check.py --check
                         python3 etc/kitlibs-check.py etc/dsv/<kit>-kitlibs-check.conf
  {{CODE_CHANGES}}     "allowed" or "not allowed"
  {{SOURCE}}           the etcd-grove commit the challenge was exported from
This comment is removed by the export. -->

This directory is a self-contained verification challenge. Its goal is one Lean theorem about a Go
distributed system: **{{TITLE}}**, the kit `{{KIT}}` (its Go in `{{GO_DIR}}`, its configuration in
`etc/dsv/{{KIT}}.py`).

## The goal

Prove `theorem {{THEOREM}} : {{THEOREM}}.spec` in `{{PROOF_FILE}}`. The statement,
`{{THEOREM}}.spec`, is in `{{SPEC_FILE}}`; its file header says what it means.

The goal is done when, from a clean build:
1. `lake build {{PROOF_MODULE}}` succeeds;
2. `#print axioms {{THEOREM}}` lists only `propext`, `Classical.choice` and `Quot.sound`;
3. the library premise is yours: declare `KitLibs` in `{{KITLIBS_FILE}}` (what the system's
   libraries do, nothing about the system itself; its header and `etc/KitLibsCheck.lean`'s say
   exactly what), and prove `kitLibs_nonvacuity : kitLibs.premise` in {{NONVACUITY_MODULE}};
   `etc/kitlibs-check.py` must accept both;
4. every check below passes;
5. the files below are unchanged.

## Do not edit

The statement is fixed (its premise `KitLibs` is yours, in `{{KITLIBS_FILE}}`). Do not edit, move or
shadow:
{{FIXED_FILES}}
- anything under `Net/`, `Robustness/`, `GooseLang/`, `examples/lib/`, `models/`, the main tree's
  `Spec/` and `Proof/`, `.lake/packages/`;
- the scripts under `etc/` (the kit file `etc/dsv/{{KIT}}.py` is yours except its statement and
  premise parts: `KITGEN`'s `statement` and `defs`, `HYP_INITS`).

Add no `axiom` (but in the non-vacuity module, each one a library premise), no `sorry` on the goal's
path, no `instance` of `KitLibs` or of an `InitHyp`, no `TrustedCode/`
model, and no `trusted` Goose declaration. If you believe the statement is false or a premise is
false of the real library, say so with the evidence (a failing Go test, a program the premise
proves safe that panics) instead of working around it.

Changes to the system's Go code under `{{GO_DIR}}`: {{CODE_CHANGES}}. Where allowed, each is a fix of a
bug the deployment's test can trigger, committed with a failing-then-passing Go test, and never a
change to the driver, the driver's model or the codec. Prophecy patches
(`etc/proph-patches/dsv-{{KIT}}/`) are allowed when they pass `etc/prophcheck`.

## Building and checking

There is no network. Every dependency is present and built.

- Build: `lake build <Module>` (`lake build {{PROOF_MODULE}}` for the goal).
- Check a file while editing: `etc/lean-check.py FILE` (`--goal LINE` prints the proof state).
- Axioms: a scratch file with `import {{PROOF_MODULE}}` and `#print axioms {{THEOREM}}`, run with
  `lake env lean FILE`.
- After a change to the Go or its Goose configuration: `python3 etc/goose.py --project dsv-{{KIT}}`,
  then `python3 etc/gen-init.py`.
- The checks (each exits 1 on failure):
{{CHECKS}}

Commit your work in this repository's git history as you go; do not push.

Exported from etcd-grove {{SOURCE}}.
