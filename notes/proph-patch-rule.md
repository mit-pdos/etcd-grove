# The widened prophecy-patch rule and its checker (trusted-tool change)

Branch `proph-patch-rule` (2026-11-23). Upamanyu approved option (A) on #24 (after
issuecomment-7089862247):

> The rule widens:
> - a patch may add ghost-only declarations: a `ProphId` field or package variable initialized only by `NewProph`, and helper functions whose bodies hold only read-only computation plus `Resolve*`;
> - it may add calls to them at statement level or inside `if`s on read-only conditions;
> - `etc/prophcheck` checks that erasing every added declaration and call gives back the original files, and refuses an added field in a struct the program compares with `==`, uses as a map key, or reflects on.

`CLAUDE.md`'s rule text now holds those three bullets verbatim; `etc/prophcheck` (trusted: it is
what makes a patch's proof cover the original program) checks them, with the tests
`etc/prophcheck/main_test.go` (`cd etc/prophcheck && go test ./...`). `etc/proph_patch.py` runs it
as before (now with `GOTOOLCHAIN` set, for the type-checking below); the etcd and prophkv patches
still pass.

## The exact checks

prophcheck takes the pairs (ORIG, PATCHED) of every Go file the project's patches change. Files of
one directory are one package; a name is **fresh** if it occurs as an identifier in no Go file of
ORIG's directory (tests included).

**Ghost declarations** (top level of a PATCHED file; collected from all pairs of the package first):
1. A `var` spec whose name is fresh is a ghost variable. It must be alone in its spec and be
   `var NAME = primitive.NewProph()` (optionally typed `primitive.ProphId`), or `var NAME
   primitive.ProphId` with exactly one **ghost initializer**: an added `func init() { L :=
   primitive.NewProph(); NAME = L }` (or `func init() { NAME = primitive.NewProph() }`). Goose
   refuses the first form (its copy rule: "call primitive.NewProph() in the initializer of package
   variable ...: gc may inline it and build its result ... in place") and the one-statement
   initializer for the same reason, so a translated patch uses the two-statement initializer;
   it is how the variable is "initialized only by `NewProph`" in Goose. Both erased. (An init
   only allocates a prophecy and writes a ghost variable; where it runs among the package's
   inits does not matter.)
2. A field with a fresh name in a struct type declared in ORIG is a ghost field. It must be alone
   in its field declaration, of type `primitive.ProphId`, unexported, with no tag. Erased from the
   struct.
3. A `func` (or method) with a fresh name, other than `init`, is a ghost helper. It must have no
   results and no type parameters; a method must be unexported. Erased after its body is checked
   (below). An added `init` other than a ghost initializer is not erased, so it fails the
   comparison.
4. A `const` or `type` with a fresh name is refused.

**Helper bodies** hold only these statements (locals: the receiver, parameters and the locals the
helper defines in scope):
- `P.ResolveBool(E)` / `P.ResolveU64(E)`, P a ghost prophecy: a ghost variable (not shadowed by a
  local), `X.F` for a ghost field F and read-only X, or a local prophecy the patch declared;
- a call of a ghost helper, `H(E...)` or `X.H(E...)` (X, E read-only; no `...`); the package's
  helper call graph must have no cycle (a helper terminates);
- `NAME := E`, `NAME = E`, `NAME op= E` (single-valued, E read-only, NAME a local), `NAME++`,
  `NAME--` on a local;
- `if C { ... } else ...` with C read-only and no init statement;
- `for I := E; I < E2; I++ { ... }` exactly (E, E2 read-only), the body not assigning I (no
  `<=`, no `range`, no other loop: a counted loop run without interleaving reaches its bound);
- a block, `return` without results.
Everything else is refused: `go`, `defer`, sends, `select`, `switch`, `range`, closures, labels,
assignments to anything but the helper's locals.

**Ghost statements** (in any statement list of PATCHED outside the helpers; erased):
- `NAME := primitive.NewProph()` with NAME not in ORIG (the first rule's local prophecy);
- a resolution of a ghost prophecy (as above; a resolution of an identifier the patch has not
  declared is reported);
- a call of a ghost helper (as above);
- `X.F = primitive.NewProph()` for a ghost field F, X read-only;
- `if C { ... } else { ... }` (no init; else optional or an `else if` of the same kind) holding at least one statement and
  only ghost statements (an original `if` without statements, such as gryff's `if C { // ... }`, is not ghost code).
In a composite literal, a ghost field's keyed element `F: primitive.NewProph()` is erased.
The import of `github.com/goose-lang/primitive` (unnamed) is erased when ORIG lacks it, and ORIG
must then not use the name `primitive`; a file that declares local prophecies must import it.

**Read-only expressions**: identifiers, literals, parentheses, field selections, dereferences,
indexing, slicing, type assertions (not `.(type)`), `&` of a field selection or an indexing (new),
unary operations but `<-`, binary operations, and calls of `len`, `cap` and conversions to the
predeclared basic types that the package does not redeclare (nor a ghost helper or variable).

**Erasure**: PATCHED, its ghost declarations, fields, statements, literal elements and import
erased, must equal ORIG as a syntax tree (positions, comments, formatting and `ast.Object`s
ignored).

**Ghost fields' structs** (only when a patch adds a ghost field; `etc/prophcheck/uses.go`): `go
list -e -export -deps -json ./...` in the Go module holding the field's package (the patched
copy), and every package of that module type-checked from source (dependencies from export
data). With T the structs that have ghost fields, *contains* = T itself or an array or struct
(by value) with a containing element or field, and *reaches* = contains, also through pointers,
slices and maps. Refused:
- an operand of `==`/`!=`, a `switch` tag or case, whose type contains T;
- a map type (of any expression or declared object, looked into) whose key contains T;
- a conversion, explicit or implicit, of a value whose type reaches T to an interface type:
  assignments, typed `var`s, call arguments (variadic too), results, composite-literal elements
  (struct, slice, array, map keys and values), sends, map index keys, the other operand of an
  interface comparison, `panic`/`print`/`println`, `append`'s elements (an interface value can be
  compared, hashed and reflected on: reflect, fmt, encoders);
- a generic instantiation with a type argument that reaches T;
- `unsafe.Sizeof`/`Alignof`/`Offsetof` of a value that reaches T.
This is conservative (a `*T` passed as `any` is refused even if only its methods are used).

## Not admitted (interpretations of the rule)
- Constants and types (the rule lists variables, fields and helpers): inline constants.
- `init` functions other than a ghost initializer.
- New files (`etc/proph_patch.py` still refuses them) and imports other than `primitive` (an
  import can change package initialization): helpers go in an existing file that has the imports.
- Calls of another package's helpers (each package's helpers are its own).
- A ghost field initialized from anything but `NewProph` (e.g. a copy of a ghost variable).
- A ghost mutex, or any helper that blocks, allocates or writes the heap.

## Tests (`etc/prophcheck/main_test.go`)
Positive: the first rule's local prophecy with an `if`/`else`; a ghost variable with helpers (a
method calling a function, a counted loop, locals, `op=`, `++`, an `if`, `&` of a field) called at
statement level and inside an `if`; helpers in one file called from another; a ghost field with a
keyed literal initialization, a `X.F = NewProph()` statement and resolutions; a ghost variable
with a ghost initializer; a struct without
ghost fields used freely; an original `if` without statements kept (not erased).
Negative (each checks its message): a helper that writes the heap, calls a non-helper, returns a
value, recurses (through another helper), loops with `<=`, loops forever, assigns its counter,
ranges, starts a goroutine, defines a local from a call, is an exported method, receives from a
channel, or is called with a call argument; an added constant, type, non-`NewProph` variable,
`init`, non-`ProphId` field, exported field, changed statement, added non-ghost statement, a
function named like an original identifier, a resolution of an undeclared prophecy; a ghost
variable without initializer, with an initializer that does more, with two initializers; a ghost
field's struct compared (`==`, and `!=` on an array of it), a map key (directly, and an array of it in
a struct's field type), converted to `any` (as a result, an argument, a slice element), switched
on, a type argument, `unsafe.Sizeof`.

## Ports onto the rule

**gryff** (branch `dsv-gryff`): its trace prophecy is `etc/proph-patches/dsv-gryff/01-trace-prophecy.patch`
(the project's name is `dsv-gryff`, and patches are found by project name): a ghost variable
`traceProph` with its ghost initializer, 24 event helpers and 5 field helpers (methods of
`*Replica`, resolving `traceProph`; the lab's 24 `ev*` constants inlined as literals with the
name in a comment) at the end of `src/gryff/epaxosrmwhandler.go` (it has every import they need;
`proph.go` was a new file), and the 24 calls, one per event kind (23 in `epaxosrmwhandler.go`'s run loop, 1 in
`epaxos-exec.go`). What changed from the fork's ghost code to fit: no `Replica.proph` field (it
was a copy of `traceProph`, not initialized by `NewProph`: the resolutions read `traceProph`
directly; the proofs' `r.proph ↦□ p` became `globalAddr traceProph ↦□ p`), no constants, no new
file. The fork is the lab's minus the ghost code (`proph.go` deleted, 4 lines of `tupaq.go` and
the 24 call lines removed).

**swiftpaxos** (landed): its ghost code does not fit the widened rule, and stays in the fork
(`examples/dsverify/swiftpaxos/client/ghost.go`, `swift/ghost.go` and their 15 call lines):
- `client/ghost.go`: `type Ghost struct { mu sync.Mutex; p primitive.ProphId }` is a new type
  (the rule admits a `ProphId` field of an existing struct or a package variable);
  `var nodeGhost = NewGhost()` is a package variable initialized by another call; `NewGhost` and
  `theGhost` return values (and `NewGhost` allocates); and **`Invoke`, `Accept` and `Step` take
  and release the ghost mutex `g.mu`** around a multi-word resolution, which is neither read-only
  computation nor `Resolve*` (it blocks and writes the heap);
- `swift/ghost.go`: `ghostId`, `ghostIds`, `ghostCmd` return slices built with `append` and slice
  literals (allocation, results); every `ghost*` helper calls `client.GhostStep`, another
  package's helper;
- `client/buffer.go`: `g := theGhost()` defines a local from a call.
All but the mutex could be rewritten to fit (resolving words directly instead of building
slices; a ghost variable with an initializer; counted loops). The mutex cannot: a replica's
events are resolved from several goroutines (the run loop and descriptor goroutines, under
different locks: `ballotL`, `acceptL`, `execL`, `cntL`, `M`) and a client's from the caller and
the reply path, and the L2 proof (`client/Ghost.lean`, `GhostDefs.lean`, `L2Laws.lean`) relies on
each event's words being resolved atomically under it. Fitting it needs either a further
widening (a ghost `sync.Mutex` variable whose `Lock`/`Unlock` bracket only resolutions: such a
section terminates and has only ghost effects, so an execution of the original is one of the
patched program in which each section runs without interleaving) or a redesign of the L2 proof
(one event per resolution); a decision for Upamanyu / the coordinator.
