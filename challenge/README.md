# Comparator challenges: the trusted part of a theorem

`challenge/NAME/` is a Lake package of its own holding what one top-level theorem of this
repository asks you to trust: its statement, with its proof `sorry`, everything the statement is
written in terms of, and every axiom its proof uses, each declared as in the repository. With
[leanprover/comparator](https://github.com/leanprover/comparator)'s checks, it is checked against
the repository: the repository proves the statement this directory states, from the axioms this
directory names, and Lean's kernel accepts the proof.

| Challenge | Theorem | Statement's module |
|---|---|---|
| `mvccfull/` | `Perennial.EtcdGrove.mvccfull_safe` | `Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Results` |

## What is in a challenge

* **The repository's modules that declare what the comparator compares**, under their own names
  and paths, each a copy of the repository's file with every other declaration removed. The
  comparator (v4.34.0, `Compare.lean`) compares, name for name and value for value, every
  constant reached from the theorem's statement and from the statement of every permitted axiom,
  through statements, definitions' values, theorems' proofs, and inductive types' constructors and
  recursors. The axioms themselves are declared here too.
  Removing a declaration removes its docstring and attributes and a modifier line before it
  (`open X in`, `omit h in`); an `attribute [a] x y` line loses the removed names (and goes with
  none left); an `open` line loses a namespace left with no declaration. Notation, macros, syntax
  and elaborators stay, as do `variable`/`open`/`namespace`/`section` lines. A module none of
  whose declarations is kept goes, its importers importing what it imported instead.
* **Declarations kept for elaboration only** (`comparator-extra.txt`): what elaborating a kept
  declaration needs although its term does not mention it (an instance found during elaboration
  and unfolded away; a name in a `variable` line). The comparator does not compare them; a proof
  among them (or reached from them) is `sorry`, as no compared term holds it and elaboration does
  not unfold proofs. The few `sorry`s in the directory are these and the theorem's own proof,
  besides two the repository itself has in such declarations (`sorry -- axiomatized type`).
* **`Challenge.lean`**: the root: the statement's module and every module here that declares one
  of the axioms (the statement alone does not import them all).
* **`comparator.json`**: the comparator's configuration: the theorem, and every axiom it depends
  on as a permitted axiom: Lean's three, Perennial's and the repository's, found by the
  comparator's own walk of the proof (`checkAxioms`, which reaches a few more than Lean's
  `collectAxioms`).
* **`AXIOMS.md`**: those axioms, by the module that declares each: the repository's here, the
  dependencies' (Perennial's) at the revision `lakefile.toml` pins.
* **`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`**: the repository's toolchain,
  Perennial and Perennial's dependencies, at the revisions the repository pins.

The trusted base of the theorem is then: this directory, the dependencies at those revisions (in
particular Perennial's GooseLang semantics, which the statement is about, and the axioms
`AXIOMS.md` lists under them), Lean, and the comparator's checks.

## Generating

```
challenge/tools/gen.py NAME THEOREM MODULE [--solution DIR] [--packages-from DIR]
```

reads a built checkout (`DIR`, default this one; `lake build MODULE` first: it only reads it),
computes the comparator's closure (`tools/Closure.lean`, run with `lake env lean` in `DIR`),
writes `challenge/NAME/`, and builds it. While the build fails with an unknown name, an instance
not found, an unknown attribute or namespace, it keeps what provides it (`comparator-extra.txt`)
and regenerates. `--packages-from DIR` copies `DIR/.lake/packages` (built dependencies) into the
challenge's `.lake` when it has none, so the build does not rebuild Perennial.

Regenerate a challenge when the theorem's statement, what it is written in terms of, or its axioms
change: a stale challenge fails the check. `comparator-extra.txt` is reused; delete it to find the
smallest set again.

## Checking

```
challenge/check.sh NAME [SOLUTION]
```

builds the challenge, checks that the solution (this checkout, or `SOLUTION`) is built
(`lake build --no-build`; it never builds it), exports both with `lean4export`, each in its own
Lake workspace (the challenge's modules have the solution's names), and runs the comparator's
checks on the two exports (`tools/CompareExports.lean`: the comparator's `compareAt`,
`checkAxioms` and kernel replay; its header says why the comparator's executable, which takes one
workspace, is not used). It prints `Your solution is okay!` when the solution's theorem has the
challenge's statement, uses no axiom but the challenge's, and Lean's kernel accepts the solution's
export (the whole proof) on replay. The solution's export is large (2.3 GB for `mvccfull`).
