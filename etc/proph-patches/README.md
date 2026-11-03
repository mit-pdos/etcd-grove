# Prophecy patches

`<project>/*.patch`: changes to a project's Go code (a project of `etc/goose.py`) that only add
prophecy variables and their resolutions, for proofs that need a prophecy the code does not have.
`etc/goose.py` applies them, in name order, to a copy of the project's source before translating
it (and `etc/verified-code.py` reads the same copy); the proofs are of the patched code.

A patch is a unified diff relative to the project's source root (the checkout's root, or the
example's directory for a project in this repository), such as `git diff` output. It may only add
`primitive.NewProph()` declarations, `ResolveBool`/`ResolveU64` calls on them (with an identifier
or literal argument), the `primitive` import, blank lines and comments, so that it does not change
what the program does: `etc/proph_patch.py` (docstring) states the rules and checks them; run it
alone with `etc/proph_patch.py [--project NAME]`. Name a patch after what it is for
(`01-store-get-revision.patch`), and say in a comment line of the patch's Go code which proof uses
the prophecy.

Why patches rather than commits of the fork, and why not prophecies added in Lean:
`notes/decisions.md`, "Prophecies as patches of the Go code".
