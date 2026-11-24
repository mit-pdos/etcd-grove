# Handoff: reflection S0 / S0.5 (2026-11-24)

Self-contained: everything here is on GitHub (mit-pdos/perennial, mit-pdos/etcd-grove).

## Goal and Upamanyu's decisions

- Build a reflection semantics for Perennial from a few trusted primitives, plus Go models of `reflect` and
  `internal/reflectlite` (no `unsafe`), and prove etcd-grove's `examples/specreq/reflect` snippets with it.
- **Hard rule (Upamanyu):** nothing reflect-related merges anywhere without his explicit approval. That
  includes Perennial `lean`, etcd-grove `lean`, and the specreq coverage branch. Use branches and VM builds only.
- **Upamanyu (perennial#698, comment 7136196811):** no package-specific GooseLang instructions. Perennial's
  `AsAssign` (the reflection of `errors.As`, landed on Perennial lean in d840e4d7b) is to be retired in favour of
  `errors/wrap.go` over a `reflectlite` model built on the S0 primitives. That is S0.5, below.
- **The S0 review packet below has not been reviewed by Upamanyu yet.** S0 and S0.5 go to him together, as one
  trusted review.

## Branches

| repo | branch | head | state / purpose |
|---|---|---|---|
| perennial | `reflect-s0` | `31718fbea` | S0. The trusted part ends at 523339171 (full Perennial VM build green). The S0 proofs sit on top (no sorry; `#print axioms` clean). Base: Perennial lean 00b4280a9. |
| perennial | `reflect-s0-go`, `reflect-s0-ev` | `523339171`, `aa917f18c` | Already merged into reflect-s0 (the Go side and the evidence harness). Keep for history. |
| perennial | `reflect-s05` | `567b4226f` | S0.5 WIP (on merge `6a49ef67e` = reflect-s0 + origin/lean, conflicts resolved as unions). Go side done and tested; NO Lean build yet. |
| etcd-grove | `reflect-s0/2026-11-24` | this file's commit | The S0 retirements and snippet proofs. Pins Perennial reflect-s0 31718fbea. Stacked on `specreq-reflect-cov/2026-11-24` (731f616d58, held). Full VM build: 27,893 jobs, green at d78a216a43. VM gates at e3d0c9e62f: everything passed except `axiom-tok` (see below). The last two commits are a docstring and the WIP axiom-tok fix. |
| etcd-grove | `specreq-reflect-cov/2026-11-24` | `731f616d58` | The reflection requirement snippets (22 files): gates green, held for approval. |

The etcd-grove branch has not merged the newer origin/lean (lean has since moved: etcd_wal_safe, dsv tooling,
bootstrap/hash/grpc-tcb). Merge it before the next gates run.

## S0 review packet (trusted; for Upamanyu)

**Primitives** (Perennial `reflect-s0`):
- **Seven `GoInstruction`s** in `GooseLang/Lang.lean`, with their `Countable` instances: `FuncResolveAt shs f`,
  `ConvertAt`, `FieldRefAt`, `ArraySliceAt`, `EqNilAt`, `PointerOfAt`, `TypeQuery q`. The supporting types are
  `go.Shape` and `go.TypeQ`.
- **Thirteen step rules** in `Golang/Defn/Reflect.lean`'s `ReflectSemantics` (registered in `go.Semantics`):
  `func_resolve_at_step`, `convert_at_step`, `field_ref_at_step`, `array_slice_at_step`, `eq_nil_at_step`,
  `pointer_of_at_{ptr,unsafe,map,chan,slice_nil,slice}` and `type_query_step`. The last is over the function
  `typeQuery`, whose rows are kind, numTypeArgs, elem, key, len, chanDir, numField, field{Name,Type,Embedded},
  numIn/inType, numOut/outType, variadic and arrayOf.
- **Fifteen TrustedCode stubs** in `TrustedCode/internal/reflectcore.lean`, one line each:
  - `TokOf`, `Box`, `Load`, `Alloc`, `PtrTok` (via `FuncResolveAt` to the translated generic helpers);
  - `ConvertAt`, `FieldRefAt`, `ArraySliceAt`, `EqNilAt`, `PointerOfAt`;
  - `TypeKind`, `TypeElem`, `TypeLen`, `TypeNumField`, `TypeFieldType`.

**goose:**
- C0: `[model] names_only` (in `declfilter`, `util/model.go`).
- `layout.go`: refuses `unsafe.Sizeof`/`Alignof`/`Offsetof` of a type whose layout a model changes.
- A promoted method's `MethodUnfold` follows its declaring method's filter.

**Overlay Go (a translated model; trusted as a model):**
- `goose/model/overlay/internal/reflectcore/{core,helpers}.go`
- `goose/model/overlay/reflect/{type,value,map,makefunc,unmodelled}.go`
- configs `Code/reflect.toml` and `Code/internal/reflectcore.toml`

`etc/trusted-delta.py 00b4280a9..523339171` lists 53 tier-0 files, including the harness and the tests.

**Adversarial review** found six issues, all fixed:
1. `Sizeof` of a type whose layout a model changes;
2. reflection on reflect's own `rtype` values (now stuck);
3. `isDirectIface` (now go1.26 gc's rule: one pointer word);
4. `error` and `interface{ Error() string }` are one type (documented in KNOWN_LIMITATIONS);
5. `==` on reflect Values that hold a func or a map directly (documented in KNOWN_LIMITATIONS);
6. promoted-method unfolds.

**Known open items in the rules (evidence harness):** `convert_channel` has no direction premise, and
`convert_underlying` with `convert_pointer_same_underlying` is more defined than Go on named pointer types.
These are pre-existing Convert rules that `ConvertAt` reaches. The S0 model only calls `ConvertAt` on legal
pairs. They are a separate fix-semantics item.

**Trust delta in etcd-grove:**
- **Removed (-8):** `reflect.{ValueOf, Value.IsNil, Value.Kind, Value.Type, Value.Interface, Type.Elem}.wp_proof`,
  `reflectM.reflNew_pointsto`, and `reflect.TypeOf.wp_proof`.
- **Added (+1):** `reflect.rtype.String.wp_proof`:
  `∀ T, {{isPkgInit reflect}} (rtype.mk (go.tok T)).String() {{s, RET #s; True}}`.
- **Soundness finding behind the TypeOf change:** the old `TypeOf` axiom became false under the model, because
  the model is stuck on reflect's own rtype values. TypeOf is now a theorem with the premise `notRType x`; only
  the names-only `String` stays trusted.
- **rtype.String review:**
  - The coordinator's light review: survives.
  - An independent axiom-skill review: **sound**, minimal for its users, and `notRType` weakens no top-level
    theorem (all three users discharge it from a pointer: `notRType_ptr`).
  - The reviewer's caveat: the axiom holds only while `rtype.String` is names-only. The model's Go body is
    `gomodel.Stuck()`, so retire the axiom when that body is modelled. This is now in the axiom's docstring.
  - The S0 model mints type tokens only from the dynamic types of real values (`TokOf`) and from their
    components (`TypeElem`/`TypeFieldType`). `arrayOf` is unreachable in S0.
- **VM gates:** 59 collections matched the hand-edited baseline.

**Statement changes** (none weakens a top-level theorem):
- `txn.isNil.wp_proof` is now unconditional.
- `reflect.ValueOf.spec`'s `Elem` triple needs `∃ k, kindOf (underlying T) = some k`.
- The k8s `ObjSpec` gains `objTy_kind` (the driver proves it). `ObjSpec` and `StoreCfg` take `[HeapGS] [go.Semantics]`.
- `getTypeName.spec` and etcd3 `New.spec`: the premise `x ≠ nil` becomes `notRType x`.

**Snippets proved** (`specreq/reflect/Results.lean`): `wp_isNil`, `wp_typedNilString`, `wp_typedNilString_int`,
`wp_MustPanicIsNilZeroValue` and `wp_MustPanicIsNilStruct`. All have clean axioms.

**Decided overnight:**
- The TypeOf split above. The alternatives were to make rtype values non-stuck in the model (a larger trusted
  change), or to keep an axiom with a premise.
- `ValueOf` of structs and arrays is specified over a fuel-based `directIfaceN`, because the recursion goes
  through `underlying` and isn't structural.

## The axiom-tok gate: an open item, last commit on the etcd-grove branch, WIP

- **Failure:** the gates at e3d0c9e62f failed only `axiom-tok`, with "Truncations: reflect.New.wp_proof … stuck:
  Perennial.typedPointsto".
- **Cause:** `reflNew T p` is now Perennial's
  `∀ V (_ : ZeroVal V) (_ : TypedPointsto V) (_ : IntoValTyped V T), p ↦ zero_val V`, and the user-picked
  `TypedPointsto` instance under the Iris `∀` was walked as a user atom. Before S0, `reflNew` was opaque.
- **Fix (decided): the tool, not a `trunc` line,** because the allow file's ratchet says none may be added.
  `etc/AxiomTokCheck.lean`'s `lawBoundTP` makes such a binder `plain` when the same `∀` telescope binds
  `IntoValTyped` over it: `IntoValTyped.wp_alloc` makes its points-to what an allocation yields from `True`, so it
  holds no token and nothing the user chose. The selftest toy is `st_pass_typedpt`.
- **Not validated:** the file compiles, but `etc/axiom-tok-check.py --selftest` exited 1 on the VM, and the driver
  hides the Lean run's stderr. Next: run
  `vmlake env lean --run etc/AxiomTokCheck.lean --selftest=etc/axiom-tok-selftest/Selftest.lean Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt Perennial.ProgramLogic.Bounds`,
  read the error, fix it, then rerun the gates.
- This changes a soundness gate, so it is for review too.

## S0.5 plan (approved by the coordinator; trusted, for review with S0)

**`TypeQuery` rows** (with stubs `TypeUnderlying` and `TypeIdentByName`):
- `.underlying` → `tok (underlying t)`;
- `.identByName` → `identByName t`. This is the identity guard: token equality counts as Go identity only when
  `identByName`. S1's `typeident` shares it.

**`internal/reflectlite` overlay model** over S0:
- **`AssignableTo(V, T)`:**
  - `T` an interface: a translated helper `assertOk[T](x any) bool` on a boxed zero `V`. An interface `V` is Stuck.
  - `T` not an interface:
    - equal tokens: true if `identByName`, else Stuck;
    - different underlying tokens: false;
    - otherwise: Stuck.
- **`Implements`:** likewise, through `assertOk`.
- **`Set`:** through a translated helper `store[T](p, x any)`.

**`errors`:**
- Translate the real `wrap.go` with its bodies; remove the overlay's `asAssign` and the `errorType` skip.
- Retire the `AsAssign` constructor, its `Countable` entry, `as_assign_step` and `TrustedCode/errors.lean`.
- Re-prove Perennial's `errors.As` specs over the model, with the statements unchanged.

**Size:**
- 150–250 lines of Go model;
- trust: minus one instruction and its rule, minus one stub; plus two rows and two stubs;
- proofs: about 1–2 helper-days.

**State of `reflect-s05` @ `567b4226f` (WIP).**

Done:
- the rows `.underlying` and `.identByName` (encoded 23 and 24 in `Countable`);
- the stubs `TypeUnderlying`, `TypeIdentByName`, `Store` and `AssertOk`, with their TrustedCode impls and toml entries;
- the helpers `store[T]` (a nil `x` stores the zero `T`) and `assertOk[T]`;
- the `internal/reflectlite` overlay, with `names_only` for the rest;
- `errors` translates the real `As`, `as` and `errorType` (the overlay keeps only `Is`, because `Comparable` is
  not modelled);
- the `AsAssign` constructor, its rule and `TrustedCode/errors.lean` removed;
- the asAssign and asWalk spec and proof files deleted, and `errors.As.wp_proof` a marked `sorry`.

Tests:
- `go test ./goose/...` passes.
- The harness is green, including about 7,000 differential comparisons each of reflectlite against real reflect,
  and the real `errors.As` against `wrap.go` over the model, with no mismatches.
- `etc/model-tests.sh` passes; it now drops the reflectlite overlay.

Not done:
- No Lean build at all.
- `errors.initialize'.wp_proof` will break (`errorType` is now initialized through reflectlite).
- No specs or proofs for reflectlite or the four new stubs.
- `etc/trusted-delta.py origin/reflect-s0..HEAD --no-diff` has not been run.
- Regenerating with go1.26.11 changes `Code/strconv.lean`'s `IsPrint` tables; the helper reverted that file, so
  check that drift separately.

**Soundness findings (for the packet):**
1. **The retired `AsAssign` rule, and the current `errors.As` spec's `AsDecided`, are wrong for tagged structs.**
   Go returns true for `errors.As(tagSE{}, &struct{E2 `json:"t"`}{})`, but goose drops a defined struct's tags, so
   the old rule said false. The new model is stuck there (a harness test checks this). `AsDecided` must exclude
   the Struct, Chan and Func kinds.
2. **`directlyAssignable` is stuck for Chan, Func, Struct and Interface,** on purpose: reflectlite's
   bidirectional-channel case, its ignoring of whether a function is variadic, and the dropped tags.
3. **`isModelRType` is now a layout check** (a struct whose only field has type `any`). It also makes stuck any
   user error type with that layout. That over-approximates, but it is never more defined than Go.
4. **`.underlying` returns Lean's underlying type,** which for a defined struct is tagless and so not always Go's.
   Model code that uses it must allow for that.
5. **reflectlite's `rtype` lacks the `abi.Type` methods** the real one gets by embedding. No current caller can
   observe this.

**Next on S0.5:**
1. Run `vmlake build Perennial`; make `errors.initialize'` a marked `sorry` if it breaks.
2. Run the trusted-delta.
3. Strengthen `AsDecided` (point 1 above).
4. Write specs and proofs for reflectlite and the four stubs; re-prove `As`, `as` and `initialize'`.
5. Get an independent adversarial review of the new trusted text.

## Next steps

1. **etcd-grove:**
   - Validate or fix the axiom-tok change; merge origin/lean; rerun the VM gates (`vm-build:` request on
     etcd-grove#8).
   - Expect only `axiom-tok` to matter.
2. **Perennial `reflect-s05`:**
   - Finish the rows and stubs, the reflectlite model with its harness tests, `errors` over the model, and
     AsAssign's removal; regenerate.
   - Build the whole of Perennial on the VM.
   - Run `etc/trusted-delta.py`.
   - Get an independent adversarial review of the new trusted text (the fix-semantics skill).
3. **Re-prove** Perennial's `errors.As`/`asWalk` specs over the model (untrusted, a separate helper). Then
   repoint etcd-grove's pin to reflect-s05 and rebuild.
4. **Send Upamanyu ONE combined trusted packet (S0 + S0.5):** the primitives above, the two new rows, the
   overlays, goose C0/layout, the `rtype.String` axiom and the axiom-tok gate change. Use one item per message,
   each self-contained.
5. **Later stages** (S1 names/identity, S2 Set/Convert, S3 slices/maps/sort/errors): follow
   `plan-reflect.md` §E.

## Pitfalls

- `vmlake` sync directories can be garbage-collected mid-sync (rsync exit 23 or "VM unreachable"); just rerun.
  Always read the exit code and log before pushing.
- `etc/axiom-tok-check.py` hides the Lean run's stderr: run `AxiomTokCheck.lean` directly to see errors.
- The local machine is overloaded: build on the VM only.
- Generated files (`Code/`, `GeneratedProof/`, PkgTables, `SpecPlan/Spec/PkgInit`, the swiftnet `BootTable`
  via `etc/dsv/kitgen.py`) are regenerated, never edited. A Perennial pin that adds packages
  (`internal/gomodel`, `internal/reflectcore`) needs `etc/gen-init.py`, `etc/gen-specs-pkginit.py`
  (with `PERENNIAL_DIR`) and `kitgen` reruns. The hand-written `pkgInitTable` in `RaftWitness/.../kvwitness/Adequacy.lean`
  needs a manual edit.

## Pickup (etcd-grove handoff machine), 2026-11-24 later: state and decisions

Supersedes the "Branches" heads, "The axiom-tok gate" and "Next on S0.5" items 1–3 above.

| repo | branch | head | state |
|---|---|---|---|
| etcd-grove | `reflect-s0/2026-11-24` | see `git log` (merge 5b4fc914b4, regen ceb684d156, this note) | origin/lean merged; pins Perennial `reflect-s0-lean` 6a49ef67e. VM gates at ceb684d156 (with the `/shared` overrides below): build 28,148 jobs ok; tcb 324 axioms / 0 sorries, matches the baseline; axiom-tok ok; 61 collections match; goose/gen-init/kitgen/gen-specs-pkginit/links ok; premisefix and k8s tests ok. Only `merge-status` fails on the VM (the sync dir is not a git repo). |
| perennial | `reflect-s0-lean` | 6a49ef67e | NEW name for reflect-s05's first commit: reflect-s0 31718fbea + Perennial lean 2cadd30c2 (lean's tip), no S0.5. S0's trusted text unchanged. |
| perennial | `reflect-s05` | 3e1ac82bf | + AsDecided strengthened (eb9041388); reflectlite type functions proved, errors.initialize' re-proved (3e1ac82bf). errors.As.wp_proof is still the marked sorry. |

**axiom-tok (validated):** the WIP selftest failure was the toy itself (`st_pass_typedpt`'s post lacked
`reflNew`'s `iprop(...)`, so `TypedPointsto V` was a stuck instance problem). Fixed; added the control
`st_unknown_typedpt_nolaw` (no `IntoValTyped` law: the walk still truncates at `Perennial.typedPointsto`),
and the selftest driver now judges truncations (`st_pass_*` must not truncate, `st_unknown_*` must).
Selftest: 0 failures. The gates' axiom-tok passes with no `trunc` line (reflect.New.wp_proof walks clean).

**Decision: the pin after merging origin/lean.** lean pins Perennial 2cadd30c2; this branch pinned
reflect-s0 31718fbea, which lacks it. Options:
- (a) keep 31718fbea: lean's new proofs need 2cadd30c2's Perennial, so it would not build;
- (b) pin reflect-s05's head: the S0.5 WIP, unbuilt at the time, and it mixes S0.5 into the S0 branch;
- (c) pin 6a49ef67e = reflect-s0 + Perennial lean, already on GitHub as reflect-s05's first commit.

Chose (c) and named it `reflect-s0-lean`. Generated files took lean's side in the merge and were
regenerated at the new pin on the VM:
- goose: etcd's 4 etcdserver files;
- gen-init: the PkgTables gain internal/reflectcore;
- kitgen and gen-specs-pkginit reran; gen-link was unchanged.

The rename/rename conflict in SpecPlan/Spec/PkgInit had left conflict markers in two files; the regen
fixed them. In kvwitness's hand-written table, `internal.gomodel` was listed twice after the merge; one
copy was removed.

**S0.5 progress (Perennial reflect-s05):**
- `AsDecided` (Proof/errors/Base.lean): off the diagonal it now also needs `undecidedKind (underlying T) = false`
  (not struct/chan/func) or different kinds. That is exactly where reflectlite's `directlyAssignable` returns false.
  etcd-grove's `errors.asNoMatch_notAssignable` (Proof/errors/AsNoMatch.lean) will need that premise
  when etcd-grove pins reflect-s05. Its users have pointer `T`s, so it discharges.
- reflectlite: `TypeOf`, `isModelRType` (both for non-struct kinds only), `toRType`, `toType`, `elem`,
  `rtype.Elem`, `rtype.Kind` and `initialize'` are proved (ports of reflect's). `#print axioms`: Lean's three.
- errors: `isInit` gains `errorType ↦□ errorTypeVal`; `initialize'` is re-proved (Lean's three axioms);
  `As` is still a sorry.
- `etc/trusted-delta.py 6a49ef67e..HEAD` is the S0.5-only delta (origin/reflect-s0..HEAD mixes in
  Perennial lean's own changes).

**VM gotchas:**
- The VM sync dir's `.lake/packages/perennial` was a single-branch clone: fetch the new pin's branch by
  hand before regenerating.
- `vmlake build` of all ~2,500 Perennial modules exceeds ssh's 128 KB argument limit: build in chunks.
- `lake build Perennial` builds only the framework.
- `etc/gates.sh` on the VM needs `GATES_FAILFAST=0 GATES_GO_TMPDIR=$PWD/.lake/gt/gotest
  GATES_K8S_LOCK=$PWD/.lake/gt/k8s.lock TCB_CACHE=$PWD/.lake/gt/tcb-cache`, because `/shared/tmp` is not
  writable there.

**Next:**
1. Re-prove `errors.As`/`as` over reflectlite. Needed: specs for `ValueOf`, `Value.{Type,Kind,IsNil,Elem,Set}`,
   `rtype.{Implements,AssignableTo}`, `directlyAssignable`, `implements` and `isDefined`, plus the four new
   stubs `Store`, `AssertOk`, `TypeUnderlying` and `TypeIdentByName` (reflectcore spec files, as in S0).
   The old asWalk proof (deleted in 567b4226f) is the template for `as`'s walk.
2. Then repoint etcd-grove's pin to reflect-s05 (rerun gen-init etc.; AsNoMatch's new premise) and rebuild.
3. Get an independent adversarial review of the new trusted text (the S0.5 rows, stubs, reflectlite overlay
   and errors config) and of the axiom-tok change. Then send the ONE packet to Upamanyu; nothing merges before.

## Pickup, round 2 (2026-11-24 evening): review fixes F1/F2, stub specs, the errors.As blocker

**Review findings (independent adversarial review of S0.5 + axiom-tok, coordinator-run):**
- **F2 (gate, fixed here, etcd-grove 1ef6e8915a):** `lawBoundTP` accepted any `IntoValTyped` domain that
  merely *mentioned* the `TypedPointsto` binder. It now requires (`lawDomOk`):
  - the law's `TypedPointsto` argument IS the binder;
  - its `V` is the binder's `V`;
  - the domain has no loose bound variables;
  - its `GoSemanticsFunctions` argument is built only from the axiom's ambient binders (its
    instance-implicit and implicit Lean binders, tracked by `walkProp` in `WS.ambient`), with exactly
    one GSF source there, a `go.Semantics`.

  New negative selftest examples `st_unknown_typedpt_{const,tp2,gsf,gsf2}`. Selftest: 0 failures;
  `axiom-tok --check`: ok (304 walked, 0 unknown).
- **F1 (goose, fixed on Perennial reflect-s05 65768b53a):** a type declared in a func literal of a
  package-level `var` initializer was translated as the package-level type of the same name.
  `globalVarDecl` now refuses it. Negative tests: `localtype_varinit` and `localtype_varinit_fresh`.
  - No translated code hits it: an AST scan of goose/, Go's std, etcd-grove, its project clones and the
    VM module cache found such declarations only in tests, testdata, e2e and vendor files.
  - **Pre-existing on Perennial lean's goose too**: the fix should also go to lean (trusted change).
- F3 (anonymous structs with unexported fields of different packages are equal in Lean): coordinator's.

**reflectcore stubs (Perennial 2eeebdbfc):** specs and proofs of `TypeUnderlying`, `TypeIdentByName`,
`Store` (non-interface T with a T; interface T with an x in its type set) and `AssertOk` (interface T),
plus the helpers `store_` and `assertOk_`.

**etcd-grove `reflect-s05/2026-11-24`** (off reflect-s0/2026-11-24): pins Perennial reflect-s05 2eeebdbfc;
regenerated (gen-init: errors now imports internal/reflectlite and internal/abi; kitgen); kvwitness's
hand table gains both packages; `asNoMatchLeaf`/`asNoMatchWrap`/`asNoMatch_notAssignable` carry the
strengthened AsDecided (vacuous for its only user, k8s' interface `APIStatus`). Expected to fail
`tcb` (errors.As.wp_proof is a sorry at this pin, reached by k8s' `wp_As_plain`).

**errors.As: blocked on a statement decision (not decided here).** The model makes the current spec
unprovable without more premises:
- **Interface target T:** `AssignableTo` → `implements(T, ii.ty)` → `AssertOk(T, Load(Alloc(tok ii.ty)))`.
  `Alloc`/`Load` (and `ValueOf(err)`'s `Box`, for an indirect dynamic type) need a Lean representation
  `IntoValTyped V ii.ty` of every error the walk visits, which the spec does not give.
- **Every `TypeOf(err)`/`ValueOf(err)`:** `ii.ty` must not be an interface type, must have a defined
  `kindOf` and must not have the model rtype's layout (one field of type `any`: stuck), and for
  `ValueOf` its `directIfaceN` must be defined. Also `T`'s `kindOf` must be defined.

Options:
- (A) add these to `AsDecided` (per-error facts), plus a per-error Lean representation for interface
  targets, in `isErrorTree`'s node and `asNoMatch`. A spec change; etcd-grove's only user (k8s, `APIStatus`,
  leaves are pointer types) can discharge it.
- (B) a trusted model change: `implements` asks a new TypeQuery row (type-set membership of two tokens)
  instead of allocating a zero value. That removes the representation premise for the walk; the matched
  error still needs one if its dynamic type is indirect.

Either way the statement changes beyond the recorded AsDecided strengthening, so it needs the
coordinator's call. Then the proof is: ports of reflect's ValueOf/unpackEface/isDirectIface/
Value.{Type,Kind,IsNil,Elem}; new isDefined, directlyAssignable, implements, AssignableTo, Implements,
assignTo, Set and valueInterface/packEface; and `as`'s walk on the old asWalk template.

## Exact state at the stop (usage limit, 2026-11-24 late)

**F2 (axiom-tok gate): DONE, validated.** etcd-grove `reflect-s0/2026-11-24` 1ef6e8915a (also merged into
`reflect-s05/2026-11-24`).
- Selftest: 0 failures.
- `axiom-tok --check` over `.lake/tcb.json` on the VM: ok (304 walked, 0 unknown).

**F1 (goose): DONE.** Perennial `reflect-s05` 65768b53a. Negative tests pass. No translated code hits it
(AST scan). The fix is still needed on Perennial `lean` (the bug predates S0.5; trusted change).

**Perennial `reflect-s05` @ 2eeebdbfc:** F1 + reflectcore stub proofs.
- Its full build was last run at 3e1ac82bf (green).
- 2eeebdbfc's new modules built as `Perennial.Proof.internal.reflectcore.Link` (ok).
- `errors.As.wp_proof` is still the marked sorry.

**etcd-grove `reflect-s05/2026-11-24` @ 4337c89ef1** (pins Perennial 2eeebdbfc):
- The VM gate runs fixed, in turn: kvwitness table heartbeats; `AsLeafTy`'s premise (with `AsLeaf`
  deriving it); `ErrOk`'s `kErrOk_intro`.
- The targeted builds of every affected module passed: Proof.errors.{AsLeaf,AsNoMatch}, kvwitness
  Adequacy, k8s etcd3 Link, k8s all MainLinked, etcdserver Link, client-go cache Link, examples k8s
  etcd3 Link (12,455 jobs).
- The final full gate run at 4337c89ef1 was STOPPED (usage limit) before it finished. Rerun it with the
  `/shared` overrides.
- Expected: `tcb` and the collections differ, because Perennial's `errors.As.wp_proof` sorry is reached
  through k8s' `wp_As_plain`/`AsNoMatch`. Everything else should pass. Not for landing.

**Next steps:**
1. Rerun the gates on etcd-grove `reflect-s05/2026-11-24` (VM key 44b7416aff694723, origin
   `.../wt/ho-refl05`); record the tcb/sorry delta.
2. Coordinator decision on the errors.As statement (options A/B above). Then the proof (round-2 plan).
3. Port the F1 fix to Perennial lean (with review); the packet's items 3 (goose: + F1) and 7 (gate: the
   strict `lawDomOk`) are updated.
4. The full Perennial build at 2eeebdbfc (chunked: `bin/pfull.sh`-style, 3 chunks).

## Round 3 (pickup 2026-11-24 night): errors.As option (A), in progress

Decision: option (A) (posted for Upamanyu on #40; no reply yet, proceeding as instructed). Plan:
- Perennial reflect-s05: per-error premise `asModelled ii.ty` in `AsDecided` (non-interface, defined
  kind, not the model rtype's layout, `directIfaceN` defined) plus `T`'s kind defined; for an interface
  `T`, a per-error Lean representation (`IntoValTyped V ii.ty`) in `isErrorTree`'s node and `asNoMatch`.
- reflectlite specs/proofs: isZeroSize/isDirectIface (ports of reflect's), general isModelRType,
  unpackEface/ValueOf, Value.{Kind,Type,IsNil,Elem,Set}, packEface, valueInterface, assignTo,
  isDefined, directlyAssignable, implements, rtype.{Implements,AssignableTo}; then errors.as/As.
- F1 for Perennial lean: branch `goose-localtype-varinit` off origin/lean (a helper is doing it).

Round 3 progress (Perennial reflect-s05 worktree p-refl05, uncommitted until it builds):
- Shapes (`directIfaceN`, `zeroSizeN`, ...) moved from Proof/reflect/Base to Proof/internal/reflectcore/Base
  (namespace `reflect` kept) so reflectlite/errors can use them (reflect.Base imports strconv → errors: cycle).
- reflectlite: general `isModelRType` (`rtypeLayoutU`), `TypeOf` premise now `rtypeLayoutU u = false`;
  new specs/proofs isZeroSize, isDirectIface (ports), unpackEface/ValueOf (`valueOfRepr`), flag.kind,
  Value.{Kind,Type,IsNil,Elem,assignTo,Set}, packEface, valueInterface, isDefined (`isDefinedT`),
  directlyAssignable, implements, rtype.{Implements,AssignableTo}.
- reflectcore Load/Store (and load/store) interface conjuncts generalized to any Lean type V of T
  (`#x = #i`), needed to store into a `T'`-typed target.
- errors: `AsDecided` = `asModelled ii.ty` ∧ T has a kind ∧ T not untyped nil ∧ `AsDecidedTy` (the old
  condition); `asRepr` (Lean representation of an error's type, interface T only) added to As's
  conjuncts 1–2 and to `asNoMatch`; helpers `asModelled_pointer`, `asRepr_pointer` for pointer errors.
  New `errors.«as».spec` (Spec/errors/as_.lean) and its proof (port of the old asWalk); `As` via `wp_As_ok`.
- Decision: per-error premise kept general (struct/array errors allowed when not rtype-layout and
  directIfaceN defined), not "kind ∉ {array, struct}".
- F1 lean branch: Perennial `goose-localtype-varinit` a751ac526 (off origin/lean fce59af75); go test
  ./goose/... passes with go1.26.11 copied outside GOMODCACHE; regeneration: no translated-code diff
  (only the known strconv IsPrint drift, identical on plain lean; not committed).

### Exact state at round-3 checkpoint (context nearly full)

Coordinator-E confirmed option (A) on #40. The S0+S0.5 packet goes to Upamanyu ONLY once errors.As is
re-proved, as one complete packet, trimmed to trusted items (what/why sound/evidence, 3–5 lines each),
including the goose F1 fix for Perennial lean (branch `goose-localtype-varinit` a751ac526).

Perennial `reflect-s05` @ 722b4c490 (WIP, pushed; NOT building yet). Iteration loop:
`bash ~/.claude-D/jobs/43217da4/tmp/reflection/bin/bld.sh <tag> Perennial.Proof.errors.as_ Perennial.Proof.errors.As`
(builds all new reflectlite modules + errors; log `reflection/<tag>.log`; `bin/errs.py <log> 26` prints errors).
Generators (stale vs hand edits except mk_b4.py = Spec/Proof errors/as_.lean, mk_b5.py = Proof/errors/As.lean):
`reflection/bin/mk_b{1,2,3,3b,4,5}.py`. Edit the .lean files directly from now on (mk_b4 is current).

Built OK at b8: reflectlite Base, isZeroSize, isDirectIface, isModelRType, TypeOf, unpackEface, ValueOf,
packEface, valueInterface, flag.kind, Value.{Kind,Type,IsNil,Elem}, isDefined, implements,
rtype.{Implements,AssignableTo}; reflectcore Load/Store/load/store; errors Base, initialize; reflect Base.
Failing at b8 (fixes applied in 722b4c490, being tested by b9):
- Value__Set: method-call unfolding counts (`iterate 3 (try wp_meth1)` per ptr-receiver call; simp with
  flag_bits between); `Nat.cast_ofNat` unknown (no Mathlib).
- directlyAssignable: `rw [if_neg hneq]` after TypeUnderlying; indentation of 2nd branch.
- Value__assignTo: flag bit goal → `assign_flag_bits` (Base).
- errors/As: `swap` unknown → rotate_left; wp_As_ok uses `wp_func_call; wp_call` then wp_auto.
- errors/as_: MATCH block (`fin` indentation), `htyped := Htyped`, `wp_meth1` before `Value.Elem`
  (ptr receiver), `rw [if_pos (by simp)]` after `wp_for HI`, conj-3 wrapper `injection h; subst h`.
Tactic lessons: `wp_start` strips isPkgInit (don't bind it); kind compares show up as
`decide (W8 ↑k = W8 20)` (use `kne_20` etc. literal lemmas); ptr-receiver method = 2 `wp_meth1`
(+1 for promoted flag methods); avoid `by_contra`/`swap`/`Nat.cast_ofNat` (no Mathlib);
`underlying` is ambiguous inside `rtype.`/`Value.` namespaces → `GoSemanticsFunctions.underlying`.

etcd-grove `reflect-s05/2026-11-24` (ho-refl05): UNCOMMITTED edits for the new premises (commit them
with the pin bump once Perennial builds): Spec/errors/{AsNoMatch,AsLeafTy,AsLeaf}.lean (asModelled,
IsPointerError for interface T, T-kind premises), Proof/errors/{AsNoMatch,AsLeafTy,AsLeaf}.lean,
k8s View.lean (plainLeaf & .plain wrapper carry IsPointerError), Checks.lean, ErrViews.lean,
ErrOk.lean (kErrOk_intro gets `hmod : asModelled e.ty`; lemmas asModelled_etcdError,
asModelled_deadlineExceeded), rafthttp pipeline/snapshotHandler ServeHTTP (T-kind args). No top-level
statement changes. Then: bump lake-manifest Perennial rev to the built reflect-s05 head, regen (see
regen-vm.sh), build affected modules, rerun gates (VM key 44b7416aff694723) expecting the tcb delta to
lose errors.As's sorry.

Next after Perennial builds: gen-link (`python3 etc/gen-link.py internal/reflectlite internal/reflectcore errors`),
`#print axioms Perennial.errors.wp_As` (AxCheckRefl05.lean), commit; full Perennial build (bin/pfull.sh);
etcd-grove as above; then the packet.
