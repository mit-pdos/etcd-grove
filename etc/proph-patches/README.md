# Prophecy patches

`<project>/*.patch`: changes to a project's Go code (a project of `etc/goose.py`) that only add
prophecy variables and their resolutions, for proofs that need a prophecy the code does not have.
`etc/goose.py` applies them, in name order, to a copy of the project's source before translating
it (and `etc/verified-code.py` reads the same copy); the proofs are of the patched code.

A patch is a unified diff relative to the project's source root (the checkout's root, or the
example's directory for a project in this repository), such as `git diff` output. In Go files it
may only add prophecy statements: `NAME := primitive.NewProph()`, `NAME.ResolveBool(E)` /
`NAME.ResolveU64(E)`, and `if C { ... } else { ... }` holding only such statements, where `E` and `C`
are read-only expressions (field reads, dereferences, indexing, comparisons, arithmetic, `len`,
conversions; no calls, no channel operations, no assignments), plus the `primitive` import. A
read-only expression may fail (a nil dereference): the patched program then has a failing
behavior the original lacks, which its proof rules out, so a proof of the patched program still
covers every behavior of the original. `etc/prophcheck/main.go` checks this on syntax trees (the
patched file, its prophecy statements erased, must be the original) and gives the argument;
`etc/proph_patch.py` runs it. Run it alone with `etc/proph_patch.py [--project NAME]`. Name a patch after what it is for
(`01-store-get-revision.patch`), and say in a comment line of the patch's Go code which proof uses
the prophecy.

Why patches rather than commits of the fork, and why not prophecies added in Lean:
`notes/decisions.md`, "Prophecies as patches of the Go code".
