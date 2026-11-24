# Prophecy patches

`<project>/*.patch`: changes to a project's Go code (a project of `etc/goose.py`) that only add
prophecy variables and their resolutions, for proofs that need a prophecy the code does not have.
`etc/goose.py` applies them, in name order, to a copy of the project's source before translating
it (and `etc/verified-code.py` reads the same copy); the proofs are of the patched code.

A patch is a unified diff relative to the project's source root (the checkout's root, or the
example's directory for a project in this repository), such as `git diff` output. In Go files it
may only add prophecy-only code (the rule as widened by Upamanyu, #24; the exact checks:
`notes/proph-patch-rule.md`). The prophecy package is Perennial's `github.com/mit-pdos/perennial/proph`
(`proph.NewProph`, `proph.ProphId`, `ResolveBool`, `ResolveU64` and `Resolve(any)`; new patches use it)
or goose's `github.com/goose-lang/primitive` (the same without `Resolve`); `primitive.` below stands
for either:
- prophecy-only declarations, with names the package does not use: a `primitive.ProphId` field (unexported, of a
  struct the program never compares with `==`, uses in a map key or reflects on) or package
  variable initialized only by `NewProph` (`var NAME = primitive.NewProph()`, or, as Goose needs,
  `var NAME primitive.ProphId` and `func init() { p := primitive.NewProph(); NAME = p }`), and helper functions (or unexported
  methods) without results whose bodies hold only read-only computation (locals, counted loops,
  `if`s) plus `ResolveBool`/`ResolveU64`/`Resolve` and calls of other helpers (not recursive);
- statements: `NAME := primitive.NewProph()`, resolutions of an added prophecy, calls of the
  helpers, `X.F = primitive.NewProph()` for a prophecy-only field (or `F: primitive.NewProph()` in a
  composite literal), and `if C { ... } else { ... }` holding only such statements;
- the import of the prophecy package (`proph` or `primitive`).

The arguments `E` of resolutions and calls and the conditions `C` are read-only expressions (field
reads, dereferences, indexing, `&` of a field or element, comparisons, arithmetic, `len`,
conversions; no calls, no channel operations, no assignments); `Resolve`'s argument (of type `any`)
may also be a conversion to `any` or a struct literal of such values (a struct type of the package
or a `struct{...}` type literal; no allocation, `append` or `make`). A read-only expression may fail (a nil
dereference): the patched program then has a failing behavior the original lacks, which its proof
rules out, so a proof of the patched program still covers every behavior of the original.
`etc/prophcheck/main.go` checks this on syntax trees (the patched files, their prophecy-only code erased,
must be the originals; a prophecy-only field's struct uses on the type-checked module) and gives the
argument; `etc/proph_patch.py` runs it. A patch creates no file: put helpers in an existing file
of the package that already has the imports they need (a patch adds no import but `proph` or
`primitive`). In `go.mod`/`go.sum` a patch may only add the prophecy package's lines.
Run it alone with `etc/proph_patch.py [--project NAME]`. Name a patch after what it is for
(`01-store-get-revision.patch`), and say in a comment line of the patch's Go code which proof uses
the prophecy.

Why patches rather than commits of the fork, and why not prophecies added in Lean:
`notes/decisions.md`, "Prophecies as patches of the Go code".
