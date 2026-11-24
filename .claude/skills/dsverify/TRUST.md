# The trust base, hypotheses, findings and bounds

## What the goal may rest on

Lean's three axioms and the statement's declared premises (`CHALLENGE.md`), nothing else. The
environment's trusted definitions (the net extension's semantics, `DistDeploy`, Goose's translation
and Perennial's models) are the challenge's trust base, given: you add to none of them. So:

- **no `axiom`** in your files, and none that a generator writes on your behalf (`gen-init`'s
  `opaqueInitsOk`/`initFuncsOk` for an untranslated initializer your closure reaches: translate
  the package with bodies, or avoid the call; `SETUP.md`);
- **no `TrustedCode/` model** of your own, and no `trusted` entry in a Goose configuration;
- **no `sorry`** on the goal's path at the end.

## Hypotheses while you work

A library function the proof calls that has no spec yet, and that you will prove later (a codec
helper, a standard-library function with a body), may be a **named hypothesis** in the meantime:
a `Prop`-valued class (or a section variable) stating its spec, taken by the proofs that need it,
like a `sorry` that the trust-base report can count. Rules, the premise rules of `CHALLENGE.md`:

- **Visible**: a hypothesis is an argument, never an `instance` (an instance of a hypothesis class
  is an axiom in effect), and never an `axiom`.
- **True of the real code**: its precondition is what the Go needs (receivers non-`nil`, exclusive
  tokens where the code is not thread-safe, the arguments it really accepts, a call made once where
  a second panics). Read the code, and cite it in the docstring.
- **One canonical spec**: if the function already has a spec anywhere in the tree, use it.
- **Discharged before done**: each hypothesis is proved (an instance built in a linking module
  from the function's proved spec, passed to the goal's proof), or the goal is not done. Keep a list
  of the open ones in `notes/STATUS.md`; they count like `sorry`s.

## Attacking a hypothesis (before every freeze)

For each hypothesis a stage adds or restates, and for each declared premise the proof leans on in a
way you did not expect, try to **refute it**: write a concrete Go program using the library that
panics (or misbehaves) when really run, yet whose "no panic" triple is provable from the hypothesis.
Run the program. Typical successes:

- a spec that holds of each call alone but not of two calls interleaved;
- a postcondition that gives a resource out of nothing (a token, a fraction, a persistent fact the
  library never established);
- an antecedent that is satisfiable trivially (instantiate a predicate parameter with `False`);
- a fact that depends on configuration the spec does not mention.

A refuted hypothesis of yours is restated (narrower, or with the missing premise) and attacked
again. A refuted **declared** premise is a finding about the challenge: report it, with the program;
do not prove over it. Record each attack and its result in the stage's notes. Reviews against the Go
code do not find these: they judge the statement true of the code and miss that the logic lets a
client use it unsoundly.

## The trust-base report

`etc/tcb-report.py` (`TOOLS.md`), after a build, lists for the linked results the axioms and `sorry`s
they rest on and the definitions their statements use; `--roots PATTERN` narrows it to the kit's
results (`'^Dsverify/Proof/<kit path>/'`). Track the goal path's `sorry` count with it each round.
The final check is the goal's `#print axioms` (`CHALLENGE.md`, "Done").

## Findings in the target

When you find a bug in the Go code being verified (a reachable panic, a wrong result, a history
porcupine rejects) or in its documentation (a precondition the code needs that the API does not
state), record it **as soon as it is found**, one file per finding:

- `issues/<slug>.md` with a Go test in `issues/<slug>/` that fails on the challenge's code and reaches
  the bug the way the deployment does (**a bug is something the deployment's test can trigger**: a
  schedule, a fault the network model allows, a configuration the program can choose); the file is
  written as the bug report you would file upstream;
- `nonissues/<slug>.md` otherwise (found by reading; unreachable from the deployment; docs only),
  with the reason.

Each says whether it blocks the proof (`blocks-proof: yes/no`). A **fix** is separate from its bug:
one commit changing the system's code (never the driver, the driver's model, the codec or the
environment: `CHALLENGE.md`), with the finding's test passing after it and the translation
regenerated; record it under its own heading in the finding's file and in the report. When the
challenge's `CLAUDE.md` forbids code changes, a blocking bug is reported, and the proof stops at it.

## Bounds

Thread counts, lock reader slots, lifetime counters and sizes are reasoned about where they are owned
(`PRINCIPLES.md`, "A bound is reasoned about where it is owned"): the statement fixes the global
constants (the step bound, the threads); the owner of a bounded object turns them into a protocol of
unbounded use (a pool, tokens, receipts, the remote library's call units); specs in between take
tokens and the owner's handle, never the numbers. `etc/bounds-check.py` counts the places that do
not follow this.
