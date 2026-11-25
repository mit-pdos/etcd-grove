# Axiom review: gogo/protobuf `proto.RegisterEnum`/`RegisterType`/`RegisterFile` (dsverify rabia)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand`, branch `dsv-fix4` at `a28755b089`; Perennial `fce59af75`
(`/shared/perennial-fce59af75`); Go source `github.com/gogo/protobuf@v1.3.2/proto/properties.go`
(the version `examples/dsverify/rabia/go.mod` pins). Go runs at go1.27.1 (the local toolchain; the
pin is go1.27.3, whose `reflect`/`log` paths used here are the same).

## The axioms

All three in `Dsverify/Proof/github_com/gogo/protobuf/proto/`, each the field of the class `Hyps`
(`Spec.lean`) verbatim; `HypsHoldLinked.lean` builds `hyps_holds : Hyps GF` from them, used by
`rabia.internal.message.wp_initialize'_lb` (`Dsverify/Proof/rabia/internal/message/Init.lean`) and
so by every rabia program's initializer proof.

- `RegisterEnum.wp_proofMsgType`: for all `σ nameMap valueMap`,
  `{{ ownGoState σ ∗ globalAddr rabia.internal.message.MsgType_value ↦ valueMap }}
   RegisterEnum "message.MsgType" nameMap valueMap {{ RET #(); ownGoState σ }}`.
  The points-to is consumed, not returned.
- `RegisterType.wp_proof`: for all `σ x name`,
  `{{ ⌜x ≠ interface.nil⌝ ∗ ownGoState σ }} RegisterType x name {{ RET #(); ownGoState σ }}`.
- `RegisterFile.wp_proof`: for all `σ filename descriptor`,
  `{{ ownGoState σ }} RegisterFile filename descriptor {{ RET #(); ownGoState σ }}`.

Claims in plain words: no panic, no result, no effect on any resource the caller owns; `RegisterType`
on any non-nil interface; `RegisterEnum` only for the name `"message.MsgType"`, at most once per
execution (the points-to of `message`'s package variable is exclusive and consumed); all calls
serialized by the exclusive `ownGoState`.

## The Go code (gogo v1.3.2 `proto/properties.go`)

- `RegisterEnum` (518-527): panics if `typeName` is in `enumValueMaps`, writes it; then the same for
  `enumStringMaps` (the `Spec.lean` header mentions only `enumValueMaps`; both maps are written only
  here, together, so the second check never fires first: a documentation nit, not a gap).
- `RegisterType` (545-560): a duplicate name is logged (`log.Printf`) and returns; else
  `reflect.TypeOf(x)`; a nil pointer is stored as is, anything else as
  `reflect.Zero(t).Interface().(Message)`; `revProtoTypes[t] = name`.
- `RegisterFile` (605-607): `protoFiles[filename] = fileDescriptor`.
- The maps are `make`s of `proto`'s package variables (`proto`'s initializer, the reviewed
  `wp_initialize'` axiom).

Measured (a throwaway test in the rabia module, removed), after `message`'s own `init`s ran:

    typed nil dup:  <nil>   (log "proto: duplicate proto type registered: message.Msg")
    typed nil new:  <nil>
    non-nil ptr:    <nil>
    value type:     <nil>   (a struct with value-receiver Message methods)
    nil iface:      reflect: Zero(nil)
    file nil twice: <nil>
    enum again:     proto: duplicate enum registered: message.MsgType
    enum new name, nil maps: <nil>

So the only panics are a second `RegisterEnum` of a name and `RegisterType(nil, ·)`.

## Verdict: **survives**

## Attacks tried

1. **`RegisterType` of the nil interface.** Excluded by `⌜x ≠ interface.nil⌝`. A typed nil
   (`(*Command)(nil)`, rabia's calls) is `interface.mk` with a nil pointer, not `interface.nil`
   (the proof discharges the premise by `nofun`), and Go does not panic on it. Every other non-nil
   dynamic type implementing `Message` (pointer, value, map, func) goes through `reflect.Zero(t)`,
   which does not panic, and the assertion to `Message` succeeds because `t` implements it (the Go
   static type of the parameter guarantees this for any program Goose translates). Duplicates only log.
2. **A second `RegisterEnum("message.MsgType", …)`** (the only panicking case of the enum).
   The axiom needs the full points-to of `globalAddr rabia.internal.message.MsgType_value`:
   - It comes only from `wp_GlobalAlloc` (Perennial `Golang/Theory/PostLifting.lean:542`), which
     the generated `message.initialize'` runs inside `package.init` (once per execution), and the
     message proof consumes it at the first call. `message`'s package fact (`msgFact`) holds only
     `errFrameTooLarge`/`errFrameTooLong`; the `MsgType_name` points-to is dropped. Nothing else
     hands it out.
   - A plain allocation (`new(map[string]int32)`) that the proof case-splits on
     `l = globalAddr MsgType_value`: in the equal case the proof would hold the points-to, but the
     Go program must call `RegisterEnum` unconditionally to panic, and in the other case the proof
     has no points-to. A program that guards the call by `p == &message.MsgType_value` must import
     `message` (so it runs after the address is allocated, and the guard is false in Go: no panic).
     A package initialized before `message` cannot name the address at all. Before `message`'s
     `GlobalAlloc`, an earlier allocation landing on the address would make the later `GlobalAlloc`
     an `AngelicExit` in the model, but again the earlier call cannot be unconditional.
   - Another registrant of the name: `go list -deps ./...` in `examples/dsverify/rabia` (227
     packages) finds gogo `proto` imported only by `gogoproto`, gogo's `descriptor` (they register
     `google.protobuf.*` enums, not covered by this axiom, under their own initializer axioms) and
     `internal/message`. golang/protobuf / `google.golang.org/protobuf` are not in the closure, and
     gogo v1.3.2 keeps its own registry anyway, so no cross-registry conflict.
   - Machines that crash and restart start a fresh process (fresh registry, fresh heap and
     `GlobalAlloc`), so a restart is not a second registration in one registry.
3. **Concurrent registrations** (Go: `fatal error: concurrent map writes`). Every triple needs the
   exclusive `ownGoState σ` (half of a `ghost_var` plus the map's authority: Perennial
   `GooseLang/Lifting.lean:304`). It is not duplicable. An invariant cannot be opened around these
   calls because they are non-atomic expressions under mask `⊤`. Passing it to another goroutine
   needs real synchronization to get it back (channel, lock), which gives Go a happens-before edge.
   So the registrations are serialized. A goroutine started during `init` that reads the registries
   concurrently would race. But every other gogo `proto` function is names only with no spec here
   (`grep` over `Dsverify/Proof`, `Dsverify/Spec`: only these three and the initializer), and the
   translated `message.pb.go` functions that would reach the registries (`String` →
   `CompactTextString`, the `XXX_` methods → `InternalMessageInfo`) call unspecified functions,
   so no verified program can perform such a read.
4. **Calls after initialization.** If `ownGoState` is still held by `main` after the initializers,
   the axioms allow runtime calls. Go then logs duplicate types and overwrites files, with no panic,
   and a second `RegisterEnum` still needs the consumed points-to (attack 2).
5. **Calls before `proto`'s initializer** (`enumValueMaps` nil: a write to a nil map panics). The
   axioms do not require `isPkgInit proto`, but in Go only `proto`'s own (untranslated) initializers
   can run before its variables are made. Any package that calls `proto` imports it and is
   initialized after it. No Go program reaches this case.
6. **Cross-world check** (the skill's step 3). No left side is satisfiable by persistent cells:
   `ownGoState` and the full `↦` are exclusive, and no post states a pure fact about an opaque
   function. Not applicable.
7. **Arguments.** `nameMap`/`valueMap`/`descriptor`/`filename` are never dereferenced or validated
   by Go (nil maps and nil slices pass, measured). The registered `valueMap` need not be the map the
   variable holds, and nothing reads it back.

## Conditions (what the verdict rests on)

- `RegisterEnum`'s soundness rests on the full points-to of `MsgType_value` staying private to
  `message`'s initializer. A future change that put any part of it into `message`'s package fact
  (or a lemma that minted `globalAddr x ↦` from `isPkgInit`) would reopen attack 2.
- Attack 3 rests on gogo `proto` having no other spec in the repository. A spec for a registry
  reader (`EnumValueMap`, `MessageType`, `Marshal` through reflection) that did not also take
  `ownGoState` (or some other exclusion against these writers) would admit a concurrent
  read/write program that Go can kill with `concurrent map read and map write`.
- The "no other registrant of `message.MsgType`" fact is checked for rabia's dependency closure only.
  The axiom is stated for any program, but the points-to requirement already prevents a second call
  from any program.

## Not tried

No Lean counterexample was attempted, since no Go panic was found on a path the axioms admit. The
`notes/audit.md` row was not updated: the brief limited the review to writing this file.
No issue found in the verified Go code.
