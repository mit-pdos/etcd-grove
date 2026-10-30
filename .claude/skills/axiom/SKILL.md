---
name: axiom
description: Review a trust-boundary axiom for soundness — given an Iris axiom of this repository or of Perennial (one Hoare triple, or several triples of a library that interact), try to exhibit a concrete Go program that uses the axiomatized library, panics when really run, and yet has a Hoare triple (no panic) provable from the axioms. Use when asked to review, audit, attack, refute or check the soundness of an axiom, a trust-boundary spec, or a library's axiomatized specs. Never pushes.
---

# Refuting an axiom with a counterexample program

Input: an axiom, or a set of them that describe one library together (`axiom
strings.SplitN.wp_proof`; "the `sync.WaitGroup` axioms"; "`Spec/go_uber_org/zap/`"). Output, for the
user to review:

1. a report, `notes/axiom-review/<slug>.md` (step 6), whatever the outcome;
2. when the axiom falls, the **counterexample**: a Go package that panics when run (a Go test shows
   it), its Goose translation, and a Lean proof, with no `sorry`, of a triple that says it does not
   panic, from the axioms under review;
3. a row update in `notes/audit.md`'s table (its verdict column), when the axiom is one of this
   repository's.

on a branch `axiom/<slug>` of this repository, in a worktree off `lean`. Commit there; push nothing
and change no axiom without the user's word (an axiom is a trusted statement: CLAUDE.md, the `spec`
skill's "Ask before changing a trusted statement").

**Why.** An axiom is a claim about Go code that nobody checked mechanically (`notes/audit.md`'s
opening). A WP proof means the program does not panic, get stuck or hit undefined behaviour, so a
program that does panic and still gets a proof is the definitive refutation: no argument about what
the axiom "means" survives it. Reading the axiom and the Go code side by side only gives a
suspicion; the job is to turn the suspicion into that program, or to say exactly why every attempt
failed. The canonical case: Perennial `9092f8eaa` made `WaitGroup.Add`'s counter overflow a model
assumption, which was false (CLAUDE.md, "Changes to Perennial"; `notes/STATUS.md`, "The wait-group
counter and thread tokens").

## Where things are

| What | Where |
|---|---|
| This repository's axioms | `etc/tcb-baseline.txt` (`axiom` lines); each in its `Proof/<pkg>/<fn>.lean`, its triple in `Spec/<pkg>/<fn>.lean`; package-initializer axioms in `Proof/<pkg>/Init.lean` (generated: `etc/gen-init.py`) |
| Perennial's | `.lake/packages/perennial/` (`grep -rn '^axiom'`), the extensions' specs in `GooseLang/Ext/*/Specs.lean`; this repository's own extensions in `GooseLang/Ext/` |
| Trusted models (not axioms, also trusted) | `TrustedCode/<pkg>.lean` (`X.impl`, `X.init`); an attack on one is in scope too when asked |
| Earlier verdicts | `notes/audit.md` (per axiom: ok / suspect / false, with the reason); `notes/axiom-review/` (this skill's reports) |
| The Go code the axiom describes | the pinned source: `.lake/go-src/<project>` or the clone `etc/goose.py` makes in `.lake/goose/<name>`; standard library: the pinned `GO_TOOLCHAIN`'s `$(go env GOROOT)/src` |
| What an axiom is used by | `etc/tcb-report.py --roots <pattern>` (needs an up-to-date `lake build`), `grep -rn '<name>.wp_proof'` |
| A program with a closed no-panic theorem | `examples/putget` (Go: `Main` panics unless the `Get` returned the `Put`'s value) and `Proof/github_com/mit_pdos/etcd_grove/examples/putget/` (`Results.lean`: the triple of `Main`; `Adequacy.lean`: the closed theorem over the operational semantics, from `Proof/runtime/Start.lean`) |
| Panics in the logic | `.lake/packages/perennial/docs/PERENNIAL_PROOF_REFERENCE.md`, "Panics": a panic is a value `PanicV p`; a triple `{{ P }} e {{ RET v; Q }}` excludes it; `wp_fork` requires the forked thread not to panic |

## What counts

- **The program** is ordinary Go in a package of this repository's examples module
  (`examples/axiomcx/<slug>/`, `examples/go.mod`), translated by the pinned Goose (`etc/goose.py`),
  never written in GooseLang by hand: the claim is about Go. It calls the axiomatized library through
  its real API, and nothing else it does needs an axiom (prefer plain Go: locals, slices, `if !c {
  panic(...) }`).
- **It panics when run**: a Go test (`examples/axiomcx/<slug>/<slug>_test.go`, run with
  `GOTOOLCHAIN=<GO_TOOLCHAIN of etc/goose.py>`, in the real library at the pinned revision) shows an
  unrecovered panic, a runtime error (nil dereference, index out of range, failed type assertion,
  closed-channel send, negative `WaitGroup` counter, `sync: unlock of unlocked mutex`), or a Go
  `fatal error` the model treats as undefined behaviour (`concurrent map writes`). Not a deadlock or
  non-termination (a WP is partial correctness: `all goroutines are asleep` is no counterexample),
  not a data race the detector reports without a crash, not an `os.Exit`. If the panic needs an
  interleaving, the test drives it (a loop, channels to force the order) and states how often it
  fires.
- **The proof**: `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/<slug>/Main.lean`, a theorem
  `{{ isPkgInit pkg_id.<pkg> }} @! <pkg>.Main #() {{ RET #(); True }}` (or the same of the panicking
  function), proved with Perennial's tactics and its proved specs, taking the axioms under review as
  hypotheses (their `.spec`s, as a `Proof/` file takes its callees' specs), then a corollary that
  instantiates them with the axioms, followed by `#print axioms` of it. The printed axioms must be
  the ones under review plus Lean's three and the generic ones every Perennial proof prints (compare
  with `#print axioms` of a small proved function); anything else (another library's axiom, a
  `sorry`) and the counterexample is not clean: remove it or say exactly what it adds. The closed
  form (an adequacy theorem like `putget_safe`: no thread ends in a panic) is the strongest
  statement; do it when the triple is done and the user wants it.
- **An inconsistent axiom** (one from which `⊢ False`, or `|==> False`, follows) refutes itself: then
  the program is a bare `panic("unreachable")` and the proof is `False.elim`; still give both.

## Steps

1. **Pin down the claim.** Read the axioms in full: every premise, every resource each consumes and
   returns, every persistent fact (`□`, `↦□`, `is_*` predicates), the postconditions' pure facts, the
   package-init facts it assumes, and the docstring's argument for why it is true. List the claims
   in plain words: "returns a fresh slice", "never panics", "the result is in range", "this token is
   exclusive", "`Close` may be called any number of times". Check `notes/audit.md` and
   `notes/axiom-review/` for an earlier verdict.
2. **Read the Go code at the pin**, not the documentation or memory of it: the function's body, every
   path to a `panic` or runtime error, what it aliases (does the result share memory with an
   argument or with state?), what it does when called concurrently, twice, after a close, on a zero
   value or `nil` receiver, at a boundary (`0`, negative, `MaxInt`, empty, overflow), in an
   unexpected order of the library's calls.
3. **Find a gap and its attack.** Each kind of false claim has a standard program shape:
   - *A false pure fact* (a value's range, an equality, "non-nil", "len = n"): call it so the fact
     fails, and check the fact in Go: `if !fact { panic("claim") }`. The proof discharges the `if`
     from the axiom; Go takes the branch.
   - *A missing premise* (the axiom says no panic where Go panics): call it in that case, with
     whatever the precondition asks satisfied. The proof is a `wp_apply` of the axiom.
   - *Too much ownership* (a "fresh" result that aliases, two exclusive tokens for one object,
     ownership of memory the library keeps writing, a resource returned twice): write through one
     handle and read through the other, then check the value the proof thinks unchanged; or race the
     library's writes against the program's under a proof that owns the memory.
   - *A too-strong persistent fact* (`↦□` of state that changes, an `is_*` that survives `Close`):
     change the state through the API (or wait for the library to), then check the old value.
   - *Interacting triples* (a protocol over several calls): find the order the axioms allow and Go
     does not (use after `Close`, double `Unlock`, `Add` after `Wait`, a callback re-entering the
     library), or a ghost step two triples both grant.
   - *A wrong package-init fact* (`opaqueInitsOk`, `*_init`): read the variable after init and check
     the claimed value.
   If no gap is found, try the claims one by one anyway: the axiom survives only the attacks tried.
4. **Make it real in Go first.** Write the package and the test; run it at the pinned toolchain and
   library revision; keep the output. If Go does not panic, the gap was not one: back to step 3.
5. **Prove it.** Add a temporary project to `etc/goose.py` for the package (on the branch only;
   model it on `putget`'s entry: `local=`, `lean_roots`, `packages`, `owned`), translate (`etc/goose.py
   --project <name>`), add the package's `Init.lean` the way the examples' are, and prove the
   theorem (`etc/lean-check.py` for the loop, `lake build` of the module as the check of record).
   A proof that gets stuck is information: is the gap not real in the model (the axiom is weaker than
   it read), or is a Perennial spec missing for the plain-Go part (then simplify the Go, or record
   the gap in `notes/perennial-changes.md`)? Never close the gap with a `sorry`, a new axiom or an
   extra hypothesis: the counterexample would prove nothing.
6. **Write the report**, `notes/axiom-review/<slug>.md` (an index row in `notes/axiom-review/README.md`):
   the axioms reviewed (names, files, the revision), the verdict, and:
   - **Refuted**: the claim that is false, the Go code that falsifies it (file:line at the pin), the
     program and the test's output, the theorem and its `#print axioms`, the results that rest on the
     axiom (`etc/tcb-report.py --roots`: which exported results are now unsupported), and a proposed
     true restatement (not applied: present it to the user);
   - **Survives**: every attack tried and why each failed (the Go code that blocks it, or the
     premise that excludes it), and what was not tried;
   - **Stuck**: a Go panic exists but the proof could not be finished, and why (which spec is
     missing, where the proof stopped).
   Update `notes/audit.md`'s row for the axiom (verdict and a pointer to the report). If the Go
   library's own documentation promises what the code does not do, that is a finding in the
   verified code too: an `issues/` file (CLAUDE.md, "Issues in the verified code"). The axiom's
   falsity is this repository's bug (`notes/`), or Perennial's (`notes/perennial-changes.md`, and a
   fix proposed on a Perennial branch by its own workflow).
7. **Hand over.** Commit on `axiom/<slug>`. The counterexample stays on that branch (its Goose
   project would add to CI) unless the user asks to keep it on `lean`; the report and the audit row
   can go to `lean` once the user has read them.

## Lessons

`LESSONS.md` keeps the user's critiques of past runs: read it before starting, and add an entry
(and the rule it became, here) when the user critiques a run.
