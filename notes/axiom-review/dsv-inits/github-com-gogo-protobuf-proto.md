# Axiom review: gogo/protobuf `proto`'s package initializer (dsverify rabia)

Reviewed 2026-11-25 by the `axiom` skill (independent reviewer), worktree `/shared/etcd-grove-mathrand`,
branch `dsv-fix3` at `23a50393f5`; Perennial `fce59af75`; Go source
`github.com/gogo/protobuf@v1.3.2/proto` (the version `examples/dsverify/rabia/go.mod` pins), checked at
go1.27.3.

## The axiom

`Perennial.github_com.gogo.protobuf.proto.wp_initialize'`
(`Dsverify/Proof/github_com/gogo/protobuf/proto/Init.lean`; the same statement is the field of the class
`InitHyp` there):

    GetIsPkgInitProp pkg_id.github_com.gogo.protobuf.proto get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} initialize' #()
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit pkg_id.github_com.gogo.protobuf.proto }}

Context:

- **The package fact** (`Base.lean`) is `True`. It hands over no variable, registry or points-to.
- **The imports.** The translation is names only, with `pkgImportedPkgs := []`. So
  `GetIsPkgInitProp` and `isPkgInitDeps` require no import, and `isPkgInit proto` is only the
  package's own (empty) entry.
- **`initialize'`** (`Dsverify/Code/github_com/gogo/protobuf/proto.lean:2126`) is
  `package.init pkg_id… (λ _, …)`. Its body runs, in order, the 51 opaque variable initializers
  `X.init` (`customType` … `timeType`) and then the three untranslated `init.«0..2»`. Perennial's
  `package.init` guards it, so it runs at most once.
- **The test-only derivation.** `InitInstancesLinked.lean` derives the statement (`initHyp_holds`)
  from two local axioms: every one of those `X.init` and `init.«k»` is
  `{{ True }} · #() {{ RET #(); True }}`. The axiom therefore claims nothing beyond "each initializer
  of the package returns without panicking".

## Verdict: **survives**

The real initializer makes no panicking call. The fact is `True`, so it claims no value and hands
over no ownership. The specs of the `Register*` calls are a separate premise, `Hyps`, and take nothing
from the fact. There is one side finding, on `Hyps` and not on this axiom: see the end of this
report.

## Attacks tried

1. **A false fact.** The fact is `True`, so there is no claimed value to check after init. No
   `↦□`, registry contents or error identity is asserted. The specs that use proto's registries are
   `Hyps.Register*` (`Spec.lean`), and they return only `ownGoState σ`: nothing to contradict.
2. **The initializer panics.** Every variable initializer at the pin, read in full (`grep` of the
   package's non-test files) is one of the following, none of which panics:
   - an `errors.New`;
   - `reflect.TypeOf((*T)(nil)).Elem()` of a fixed pointer type (`customType`, `durationType`,
     `timeType`, `textMarshalerType`, `protoMessageType`, `marshalerType`, `sizerType`, …), or
     `reflect.TypeOf((*int32)(nil))`;
   - `make(map…)` or a map literal (`propertiesMap`, `enumValueMaps`, `enumStringMaps`,
     `protoTypedNils`, `protoMapTypes`, `revProtoTypes`, `protoFiles`, `extensionMaps`, `defaults`,
     `discardInfoMap`, `marshalInfoMap`, `mergeInfoMap`, `unmarshalInfoMap`);
   - a byte-slice literal (`text.go:57-68`);
   - a struct literal (`extProp`, `defaultTextMarshaler`, `compactTextMarshaler`, `errInvalidUTF8`);
   - `unsafe.Sizeof` (`ptrSize`).

   The three `init`s (`duration_gogo.go:47`, `timestamp_gogo.go:47`, `wrappers_gogo.go:103`) call
   `RegisterType` with typed nil pointers under distinct fixed names. This takes the
   `v.Kind() == Ptr && v.Pointer() == 0` branch (`properties.go:552`), and a duplicate only logs.
   Measured: a test binary that imports `proto` starts, and `MessageType("gogo.protobuf.proto.DoubleValue")`
   is non-nil afterwards. (`pointer_reflect.go`'s initializers are excluded by its build tag, as in
   the translation.)
3. **Running twice.** Go runs a package's initializer once. In the model, `package.init` checks the
   package state (`ownInitializing`) and skips a second run. A second call only re-establishes
   `True`.
4. **A missing import in the precondition.** The real initializer uses `errors`, `reflect`, `log`,
   `unsafe`, and through `log` `fmt`/`os`. `GetIsPkgInitProp` requires none of these, because
   `pkgImportedPkgs` is empty. The gap is harmless:
   - In every Go program the imports are initialized before `proto`, so the case "proto without its
     imports" has no Go run.
   - The axiom's post mentions only `proto`, with fact `True`, so it gives nothing about an
     import that could be exploited.
   - In rabia's proofs, `message`'s `wp_initialize'_lb`
     (`Dsverify/Proof/rabia/internal/message/Init.lean:83-97`) initializes `reflect`, `math`,
     `strings`, … as well, and before `message`'s own body.
5. **Interaction with `Hyps` (`Register*`).** None of the three specs requires `isPkgInit proto`. In
   Go the calls happen in `message`'s `init`s. `message` imports `proto`, so `proto`'s maps exist.
   In the Lean walk, too, `proto`'s `wp_initialize'` (line 91) precedes `message`'s `init.«0»`.
   - `RegisterEnum`'s duplicate panic (`properties.go:519-525`; measured: a second registration
     panics) is excluded. The spec consumes `message`'s `MsgType_value` points-to, which only
     `message`'s initializer holds, and holds once. `proto`'s own `init`s register no enum, so the
     fact needs no "`message.MsgType` absent" claim, and `True` makes none.
   - `RegisterType`'s duplicate only logs, and `RegisterFile` overwrites.
   - The fact hands over no registry, so no spec can be fed a registry state that Go does not have.
6. **Inconsistency through the semantics instance.** The axiom quantifies over every `go.Semantics`,
   and so over every `functions` map (an untranslated `init.«k»` resolves through it), and over
   the opaque `X.init` values. With a `go.Semantics` instance where `functions "…proto.init.0" []`
   panics, the axiom would be false, and with adequacy `⊢ False`. Not tried:
   - No `go.Semantics` instance exists in Perennial or here (`grep`).
   - This shape is the documented trust taken by every names-only axiom: they are satisfiable only
     in the contexts where the names resolve to Go's code (`notes/dsv-instances.md:149-152`).

   It is not specific to this axiom.

Not tried: a Lean counterexample (no Go panic to build one on).

## Side finding: `Hyps.RegisterType` (a premise, not this axiom)

This is in `Dsverify/Proof/github_com/gogo/protobuf/proto/Spec.lean`. `Hyps.RegisterType` states
no panic for **every** `x : GoInterface`, the nil interface included. In Go,
`RegisterType(nil, name)` with a fresh `name` reaches `reflect.Zero(reflect.TypeOf(nil))`
(`properties.go:557`) and panics. Measured: `reflect: Zero(nil)`.

The consequences:

- rabia's three calls pass typed nil pointers, so the programs are unaffected.
- `Hyps` is a premise of rabia's statement (`etc/dsv/rabia.py`'s `premises`, `hph`). As stated, it
  is false of Go's semantics, which makes the statement vacuous rather than unsound.
- `NonVacuityLinked.lean` discharges it only from local axioms of the same shape.

Proposed restatement (not applied): add the premise "`x` is a non-nil interface", or state the spec
for `x` a nil pointer of a pointer type, which is generated code's call. Both are easily met at
rabia's calls. This is a statement defect for the owner of `Spec.lean`, and not an `issues/` entry:
gogo's documentation says generated code always passes a typed nil.

## Evidence

Go test: `examples`-free scratch module (outside the repository,
`/shared/tmp/claude-0/-shared-etcd-grove/7b886a2f-34a1-4069-98ad-c4f614dc605c/scratchpad/gogoproto-init/gogoinit_test.go`),
`GOTOOLCHAIN=go1.27.3 GOPROXY=off go test -v`:

    === RUN   TestInitRan
    2026/11/25 06:02:04 proto: duplicate proto type registered: message.Msg
        gogoinit_test.go:36: second RegisterEnum: proto: duplicate enum registered: message.MsgType
        gogoinit_test.go:39: RegisterType(nil interface): reflect: Zero(nil)
    --- PASS: TestInitRan (0.00s)

The test checks four things:

- the initializer ran (the binary started; `DoubleValue` registered);
- rabia's registration sequence after it (`RegisterEnum("message.MsgType")`, a `RegisterType` and its
  duplicate, `RegisterFile` twice) does not panic;
- a second `RegisterEnum` panics, which the spec excludes;
- `RegisterType(nil, …)` panics: the side finding.
