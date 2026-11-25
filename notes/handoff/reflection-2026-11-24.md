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

### State at b12 (Perennial reflect-s05 b8caa1ef9, pushed; stopped at the context limit)

All new reflectlite modules build EXCEPT `Value__Set`; errors `Base`/`initialize` build; `errors.as_` and
`errors.As` fail. Remaining failures (log `reflection/b12.log`, `bin/errs.py <log> 16`):
1. `Value__Set` (both conjuncts): `wp_apply wp_assignTo.{1,2}` does not find the call: execution is still in the
   `v.kind() == Interface` check / `v.typ()` call (method-unfold layer counting). Step once with `trace_state`
   to count `wp_meth1` layers per ptr-receiver call (mustBeAssignable/mustBeExported/kind are promoted from
   `flag`). NB `try a; b` parses as `try (a; b)`: always write `(try a); (try b)`.
2. `errors/As.lean:84`: `val.IsNil()` is a ptr-receiver call; the unfold at :83 does not fire (check receiver form).
3. `errors/as_.lean` conj 1, the `As(any) bool` join (:206): after `rw [errors.typeSetContains_method]` the join
   body is `if decide (methodSet ty !! "As" = some sig) = true then ...`: by_cases on that equation and simp, instead
   of the old `cases hAs : go.typeSetContains ...` (no longer syntactically present). :224/:251/:302 follow from it.
Built: the MATCH blocks (store through `Value.Set`) of conj 1/2 up to `wp_for_post`.

## Round 4 (pickup 2026-11-25): errors.As proved

Fixes on Perennial reflect-s05 (on top of b8caa1ef9), found with `vmlake env lean <file>` from the
p-refl05 worktree (single-file elaboration in its VM sync dir 2486aba726c40cb7, ~10 s per try, no slot;
much faster than `bld.sh` once the imports are built):
- `Value__Set`: one more `wp_meth1` before each `wp_apply wp_assignTo.{1,2}` (the call is `(&x).assignTo`,
  a ptr-receiver wrapper); conj 1 `unfold valueOfRepr` before `icases Hx`; conj 2's simp lists used
  projections `hb.2.2…` that no longer typecheck after `simp … at hb`, so the whole `try simp` silently
  failed: pass `hb` itself.
- `errors/As`: after `unfold go.tok` the Value literal is no longer `asTargetVal` syntactically: IsNil is
  applied to the explicit literal (flag `W64 ((22:Nat):Int)`); `kne_20` (not `kind_ne … 20`); fold
  `go.tok T` back before `wp_rtype_Implements`; before `wp_apply has`: `simp only [asTargetVal,
  asTargetType, go.tok] at has`, rewrite `W64 ↑22 = W64 22`, `unfold go.tok`.
- `errors/as_` conj 1: `by_cases` on `methodSet ty !! "As" = some sig` (simp with decide_true/false),
  and the join binds `at next 2` (the `x` store and the ok/if block), not `at next`.

### Exact state at stop (2026-11-25 ~00:50Z, usage limit; coordinator: push, no new builds)

Perennial `reflect-s05` @ **239c3b613** (pushed). Per-file state, each checked with
`vmlake env lean <file>` against the b12 oleans (key 2486aba726c40cb7):
- `Proof/internal/reflectlite/Value__Set.lean`: **elaborates, no errors** (warnings only).
- `Proof/errors/As.lean`: **elaborates, no errors**.
- `Proof/errors/as_.lean`: **elaborates, no errors** (all three conjuncts; conj 2/3 needed no change).
- `grep sorry` over Proof/errors and Proof/internal/reflectlite: none.
- `gen-link.py internal/reflectlite internal/reflectcore errors`: no change (the Links were current).
- No trusted text changed since 2eeebdbfc (`git diff --stat 2eeebdbfc..HEAD` over TrustedCode, Golang,
  GooseLang, goose, Code: empty). S0.5 delta `etc/trusted-delta.py 6a49ef67e..HEAD --no-diff`:
  `reflection/tdelta06.txt`.

**NOT yet done (in order):**
1. `vmlake build` (key 2486aba726c40cb7) `Perennial.Proof.errors.Link Perennial.Proof.internal.reflectlite.Link
   Perennial.Proof.internal.reflectcore.Link Perennial.Proof.errors Perennial.Proof.internal.reflectlite`
   (b13 was queued, then cancelled before it got a slot). Single-file `env lean` does not rule out the
   hidden-sorry `intro` bug (Value__Set conjuncts start with `intro`): so then run
   `vmlake env lean AxCheckRefl05.lean` (untracked file in p-refl05 root) and confirm `errors.wp_As`
   has only Lean's three axioms.
2. Full chunked Perennial build: `bin/pfull.sh` (3 chunks).
3. etcd-grove (this branch): bump lakefile.toml `rev` + lake-manifest.json `rev`/`inputRev` from 2eeebdbfc
   to the built head; `vmlake sh 'bash <regen-vm.sh>'` (fetches reflect-s05 into .lake/packages/perennial);
   build the affected modules (round-2 list: Proof.errors.{AsLeaf,AsLeafTy,AsNoMatch}, kvwitness Adequacy,
   k8s etcd3 Link, k8s MainLinked, etcdserver Link, client-go cache Link, examples k8s etcd3 Link, rafthttp);
   then gates (key 44b7416aff694723, with the `/shared` overrides). **Before** (gates05d at 4337c89ef1):
   build ok 28,182 jobs; tcb FAILED: NEW `sorry Perennial.errors.As.wp_proof`; collections 55 match /
   6 differ (clientgo-cache, etcd-all-single-process, k8s-all-single-process, k8s, leaseexpiryN-single-process,
   server); all else ok except merge-status (VM sync dir not a git repo). Expected after: that sorry gone.
4. Send the trimmed 6-item S0+S0.5 packet on #40 (draft in the Round-4 report; hashes to refresh after 1–3).

### Round 4, after the limit reset (2026-11-25)
- Step 1 DONE: b14 (`reflection/b14.log`) built the errors/reflectlite/reflectcore Links + umbrellas,
  1,648 jobs, exit 0, no `sorry` warning. `AxCheckRefl05.lean`: `errors.wp_As`, `wp_AsType`, `wp_Is`,
  `wp_initialize'`, reflectlite `wp_TypeOf`/`rtype.wp_{Elem,Kind}`/`wp_initialize'` all depend only on
  `[propext, Classical.choice, Quot.sound]` (so no hidden sorry from the `intro` bug).
- Step 2 DONE: `bin/pfull.sh … full3` at 239c3b613: 3 chunks, all exit 0 (`reflection/pfull3.log`).
- Step 3: pin bumped to 239c3b6131c84989da87ba256716bb4ada42eaa7 (lakefile.toml + manifest rev/inputRev).
  VM regen (`reflection/regen06.log`): no generated-file change (only __pycache__). Targeted build
  `reflection/eg06.log` running; then gates.
- New rule (#8 7146914944): each trusted item needs a minimal Go program + a named real program; the
  packet draft carries them (real uses: k8s apimachinery `apierrors.reasonAndCodeForError`,
  `SuggestsClientDelay` (errors.As → APIStatus); etcd rafthttp `pipelineHandler.ServeHTTP`,
  `snapshotHandler.ServeHTTP` (errors.As → writerToResponse); etcd `txn.isNil` (ValueOf.IsNil);
  k8s etcd3 `getTypeName` (TypeOf.String), `getNewItemFunc` (reflect.New)).
- etcd-grove at the new pin (0cc12bd614, pushed): fixed AsNoMatch (`ii'` → `_`), rafthttp
  snapshot/pipeline handlers (multi-line `(by …)` → `;`), ErrOk (`kindOf go.string` needs the
  Tests/ReflectTypeQuery simp set; `asTargetKind_pointer (GF := GF) (hG := hG)` — the Perennial lemma
  sits in section `wps` and auto-binds `errors.Assumptions`; kErrOk_statusError's missing `hmod`),
  ErrViews (constructor nesting for plainLeaf's `leafErrTy` triple + IsPointerError).
  Build `reflection/eg08.log`: only `k8s/etcd3/Calls.lean` fails (downstream k8s Links/MainLinked unbuilt).

**BLOCKER (Calls.clientErr_notTooLarge:169), needs a spec decision.** The WIP made `apierrors.plainLeaf`
carry `IsPointerError ii` (to discharge Perennial's `asRepr` for the interface target `APIStatus`).
A client error (`clientErr`, `clientErrTys`) may be an `rpctypes.EtcdError` or a
`context.deadlineExceededError` (structs, not pointers), and `clientErr` gives a Lean value only for
`EtcdError` (`AsTypeTyped`), so neither `IsPointerError` nor `asRepr` (`∃ W x, IntoValTyped W ii.ty ∧
ii.v = #x`) is provable for client errors. Strengthening `clientErr` is out: it is in ~30 client
proofs and in trust-boundary statements. Proposed fix (spec-only, no trusted text):
1. Perennial: `asNoMatch` needs only a TYPE representation for the no-match path (`implements`
   allocates a zero value of `ii.ty`; `ValueOf(err)` is reached only on a match): replace `errRepr`
   in `asNoMatch`/`asNoMatchLeaf` with `asTyRepr T ii := isInterface T → ∃ W _ _ (_ : IntoValTyped W ii.ty), True`
   (strictly weaker premise); adjust `errors.as_` conj 3 and `As.lean`; rebuild + full build.
2. etcd-grove: `plainLeaf` (View.lean) carries a type-level repr instead of `IsPointerError`
   (make it take `GF`, or a GF-free list predicate with a lemma to `asTyRepr`); discharge for
   `clientErrTys` case by case (EtcdError, deadlineExceededError, *errorString, grpc `*status.Error`
   all have generated `IntoValTyped`); redo ErrViews/Calls; rebuild; gates.

**Approved by coordinator-E (spec-only) and implemented:**
- Perennial `reflect-s05` 534dab4a3 (pushed): `errors.asTyRepr` (∃ W, `IntoValTyped W ii.ty`, no value),
  `asRepr_tyRepr`, `asTyRepr_pointer`, `asTyRepr_of`; `errRepr` and `asNoMatch`'s wrapper use it;
  `wp_asCheck` takes it. b16: Links 1,646 jobs ok; `#print axioms` (wp_As, wp_AsType, wp_Is,
  initialize', reflectlite TypeOf/Elem/Kind/initialize'): Lean's three. Full build `pfull4` running.
- etcd-grove: `errors.asNoMatchLeaf` (Spec/errors/AsNoMatch) and `apierrors.plainLeaf` (View, moved to
  the GF section) carry `asModelled ii.ty ∧ asTyRepr (GF := GF) …` instead of `IsPointerError`
  (also the `.plain` wrapper in `apiErrAt`); Checks/AsNoMatch/ErrViews/Calls adjusted;
  `Calls.clientErrTy_modelled` discharges the four `clientErrTys`. Pin → 534dab4a3; regen no change.
  Targeted build `reflection/eg09.log`; then gates.
- Perennial 534dab4a3 full build `pfull4`: 3 chunks exit 0.
- etcd-grove 1ab5f503ee (pushed): AsLeafTy converts its `IsPointerError` premise to `asTyRepr`;
  Calls inlines `asModelled_{etcdError,deadlineExceeded}'` (ErrOk is not imported there).
  Targeted build `reflection/eg10.log`: 13,405 jobs, exit 0.
- **Gates at 1ab5f503ee (`reflection/gates06.log`, key 44b7416aff694723, `/shared` overrides): build ok
  (28,218 jobs); tcb: trust base matches `etc/tcb-baseline.txt` (324 axioms, 0 sorries) — the
  `errors.As.wp_proof` sorry is GONE (before, at 4337c89ef1: NEW sorry, 6 collections differ);
  collections 61 match / 0 differ; axiom-tok ok; all other gates ok except `merge-status` (the VM sync
  dir is not a git repo; environmental, as before).**
- Remaining: send the 6-item packet (#40) to Upamanyu via coordinator-E; nothing merges before his OK.
  F1 for Perennial lean: `goose-localtype-varinit` a751ac526 (in the packet).

## Round 5 (2026-11-25): Upamanyu's condition — layoutModelled types opaque to reflection (#40, 7155030976)

Decision text: etcd-grove#40 comment 7155030976. Scratch: `~/.claude-D/jobs/43217da4/tmp/refl-lm/`
(bin/ has the edit scripts, `vb.sh <tag> MODS` = VM build in p-refl05 with key 2486aba726c40cb7,
`genlm.sh`, `regen-std.sh` = std-lib goose+proofgen with go1.26.11; logs `<tag>.log`).

Trusted design (Perennial reflect-s05, uncommitted until it builds):
- goose `util.Models.LayoutModelled(o)` = model type whose layout (size/align/offsets under gc, AND its
  underlying type string except for interfaces) differs from the real decl, OR a type whose decl a
  config trusts (`TrustedType`: internal/sync.Mutex (underlying bool), sync.copyChecker
  (unsafe.Pointer vs uintptr), primitive.Mutex/ProphId, proph.ProphId). `LayoutChanged` (the Sizeof
  refusal) uses the same predicate. New `goose layout-modelled` subcommand + `etc/gen-layout-modelled.sh
  [--check]` write `Perennial/Golang/Defn/LayoutModelled.lean` (`go.layoutModelledNames`,
  `go.layoutModelled : GoType → Bool`, Named n _ only); coverage check: every Code/*.toml with [model]
  or trusted must belong to a loaded package (gokv grove_ffi exempt: functions only).
  List (13): primitive.Mutex, primitive.ProphId, modeloverlay.Counter (testdata), proph.ProphId,
  internal/reflectlite.{Value,rtype}, internal/sync.Mutex, reflect.{MapIter,Method,SelectCase,Value,rtype},
  sync.copyChecker. (reflect.Type/reflectlite.Type interfaces excluded: method set unobservable.)
- Reflect.lean: `typeQuery` = none if `layoutModelled t ∧ q ≠ identByName`; arrayOf needs
  `¬ ReachesLayoutModelled t` (inductive: self/field/elem through underlying). `NotLayoutModelled t`
  class (instances for unnamed ctors). Rules: ConvertAt premises `convertExposed t/u = false`
  (t or its underlying pointer's base layoutModelled) and is no longer an instance; FieldRefAt,
  ArraySliceAt, EqNilAt, PointerOfAt_* take `[NotLayoutModelled t]`. FuncResolveAt: none (generic
  helpers run Go code at T itself).
- Overlays: isModelRType removed (reflect + reflectlite); TypeOf no longer stuck; Kind etc. stuck on rtype.
- Proof side: specs gain `[go.NotLayoutModelled T]` binders (TypeKind, TypeUnderlying, EqNilAt,
  rtype.Kind, Value.Elem, Value.IsNil, isDefined, directlyAssignable, implements, rtype.Implements,
  rtype.AssignableTo, Value.assignTo, Value.Set); ConvertAt spec gains convertExposed premises;
  directIfaceN/zeroSizeN return none at a layoutModelled type (lemmas notLayoutModelled_of_*);
  TypeOf (reflect, reflectlite) premise-free; unpackEface/ValueOf drop the rtype premise;
  errors: asModelled conj4 = `go.layoutModelled t = false`; AsDecided gains `go.layoutModelled T = false`
  (4th conjunct); asTargetKind_{pointer,interface} return it.
- Tests: harness diff/layout_test.go (MS/SM structs), Tests/ReflectTypeQuery.lean (+S, Mutex, rtype),
  Tests/ReflectLayoutModelled.lean (directIfaceN/zeroSizeN of S).

Round 5 state (continued):
- Perennial reflect-s05 f0216d09c (the change) + 1e3c8a368 (audit: MODEL marker on reflect.Type's
  tok, reason on reflectlite's), pushed. Targeted VM build b5: reflect/reflectlite/errors Links,
  umbrellas, Results, Tests.ReflectTypeQuery, Tests.ReflectLayoutModelled: 1,900 jobs, exit 0, no
  sorry. `#print axioms` (AxCheckRefl05.lean + wp_ValueOf, Value.wp_Set, rtype.wp_AssignableTo): Lean's
  three. go test ./goose/... ok; harness (gen.sh; GOWORK=off go test ./...) ok; gen-layout-modelled
  --check, gen-link --check, meta-lib --check ok.
- Perennial `review-criteria-dyntype` 36e131815 (off origin/lean): CRITERIA.md criterion 14.
- etcd-grove: pin → 1e3c8a368; VM regen (regen1): no generated change (goose refused nothing new).
- Real use (#8 rule): every etcd API message (`etcdserverpb.PutRequest`, …) holds
  `state protoimpl.MessageState`, whose `pragma.DoNotCopy` is `[0]sync.Mutex`; protobuf-go reflects on
  these structs (impl.MessageInfo: reflect.Type.Field(i)), and etcd `txn.isNil` reflects on them
  (`reflect.ValueOf(msg).IsNil()`, pointer kind: unaffected). `[0]sync.Mutex` is zero-size without a
  question about Mutex (zeroSizeN: len 0).
- Perennial full chunked build at f0216d09c..1e3c8a368 (`refl-lm/pfull1.log`): 3 chunks exit 0; the only
  `sorry` warnings are the 152 GeneratedProof ones (same count as round 4's pfull4). b6 rebuilt the
  reflection modules at 1e3c8a368: exit 0.
- etcd-grove edits for the new pin (uncommitted until built): Proof/reflect/TypeOf (no rtype premise
  passed), ValueOf spec's Elem triple pre gains `go.layoutModelled T = false` (k8s ObjSpec gains
  `objTy_notLayoutModelled`, driver: `objTyD_notLayoutModelled` by decide; processListItem passes it);
  errors.{AsNoMatch,AsLeafTy,AsLeaf} specs gain `go.layoutModelled T = false` (Perennial AsDecided);
  callers (k8s Checks `apiStatus_notLayoutModelled`, ErrOk, rafthttp writerToResponse) pass it by
  `unfold X.ty; decide`; asModelled_{etcdError,deadlineExceeded}(') conj4 by decide;
  specreq MustPanicIsNilStruct/typedNilString adjusted. Build log `refl-lm/eg1.log` (pre-edit state).

### Round 5 (layoutModelled): summary, left, draft #40 message

Done: emitter (goose layout-modelled, etc/gen-layout-modelled.sh), guards per rule (see draft below), isModelRType removed, harness + Lean tests, CRITERIA 14 (Perennial review-criteria-dyntype 36e131815) + audit (reflect.Type MODEL marker, 1e3c8a368). Built: Perennial full chunked build green; harness, etc/model-tests.sh, go test ./goose/... green; #print axioms: Lean three only.
etcd-grove at 8d45849b82 (the WIP edits above, unchanged): full VM build `refl-lm/eg2.log` (key 44b7416aff694723, incremental after eg1): 28,217 jobs, exit 0, no errors. (eg1, synced before the edits were complete, failed in AsNoMatch, reflect.{TypeOf,Type__Elem,ValueOf}, specreq MustPanicIsNilStruct/typedNilString, k8s Checks/ErrOk, rafthttp pipeline/snapshot handlers; eg2 builds all of them.)
Gates at 8d45849b82 (`refl-lm/gates07.log`, `/shared` overrides): build ok; tcb: trust base matches `etc/tcb-baseline.txt` (324 axioms, 0 sorries); axiom-tok ok (304 walked); collections 61 match / 0 differ; errorf-wrap, model-param (cache-write warnings for /shared/tmp only), goose, gen-init, kitgen, links, specreq-reflect, premisefix, k8s tests, bounds 400, mode 456, tier, import-all all ok; only `merge-status` fails (VM sync dir not a git repo). `etc/merge-status.py --selftest` run locally: synthetic ok, 228 real merges replayed, 0 with problems.
Left: send the #40 message below (HEAD_EG/EG_GATES filled in `refl-lm/msg40.md`) via coordinator-E. Nothing lands without Upamanyu.

Draft #40 message:

to: Upamanyu (via coordinator-E), etcd-grove#40 — the reflection packet's landing condition (7155030976)

**Done: a type whose layout a model changes is opaque to reflection; `isModelRType` is gone.** Nothing is landed or queued; it is all on branches for your approval.

**Heads.**
- Perennial `reflect-s05` @ `1e3c8a368` (the change is `f0216d09c`; `1e3c8a368` is the audit's one MODEL-marker fix).
- Perennial `review-criteria-dyntype` @ `36e131815` (off `lean`): CRITERIA.md criterion 14.
- etcd-grove `reflect-s05/2026-11-24` @ HEAD_EG: pins Perennial `1e3c8a368`.

**Trusted diff of this change alone** (`d9a0a99d0..1e3c8a368`, tier 0):
- `goose/util/model.go`:
  - `Models.LayoutModelled(o)` is the one list. It holds:
    - a model type whose size, alignment, field offsets or underlying type (field names, types and tags; not for interfaces) differs from the real declaration's, or that the real package does not declare;
    - a type whose declaration a config trusts (`TrustedType`).
  - `LayoutChanged`, the `unsafe.Sizeof` refusal, now uses it. Nothing in Perennial or etcd-grove is newly refused (both regenerated with no change).
- `goose/util/layoutmodelled.go`, `goose/cmd/goose/main.go`, `etc/gen-layout-modelled.sh`: `goose layout-modelled` writes the list as generated Lean.
  - It checks that every config with a `[model]` or a `trusted` entry was loaded. The exception is gokv's `grove_ffi`, which trusts only functions.
  - `--check` fails when the file is stale.
- `Perennial/Golang/Defn/LayoutModelled.lean` (generated) defines `go.layoutModelledNames` and `go.layoutModelled`. The predicate is true of `go.Named n _` for an `n` in the list. The 13 names are:
  - Models: `reflect.{rtype,Value,Method,MapIter,SelectCase}`, `internal/reflectlite.{rtype,Value}`, `modeloverlay.Counter` (testdata).
  - Trusted: `internal/sync.Mutex` (underlying `bool`; Go's is a struct), `sync.copyChecker` (`unsafe.Pointer`; Go's is `uintptr`), `primitive.{Mutex,ProphId}`, `proph.ProphId`.
- `Perennial/Golang/Defn/Reflect.lean`:
  - `typeQuery` is none on a `layoutModelled t`, for every row except `identByName`. `kind` is included.
  - `arrayOf` also needs `¬ ReachesLayoutModelled t`: no `layoutModelled` type reachable through the underlying struct fields and array elements. This is a new inductive.
  - The new class `NotLayoutModelled t` has `rfl` instances for unnamed constructors.
  - `ConvertAt` needs `convertExposed t = false` and `convertExposed u = false`. `convertExposed` holds when the type is `layoutModelled` or its underlying type is a pointer to one. The rule is no longer an instance.
  - `FieldRefAt`, `ArraySliceAt`, `EqNilAt` and all six `PointerOfAt` rules take `[NotLayoutModelled t]`.
- Overlays:
  - `isModelRType` is removed from `reflect` and `reflectlite`. `TypeOf` returns the `rtype`, and any question about it is stuck.
  - New MODEL markers say why `Type`'s `tok` method is unobservable (see the audit).
- `CRITERIA.md`: criterion 14, as you worded it.

**Per-rule guard decisions.**
- **Direct rows:** guarded, `kind` included. `TypeOf(reflect.TypeOf(0)).Kind()` is stuck.
- **`identByName`:** not guarded; it reads only the name.
- **`arrayOf`:** the whole row is guarded by reachability, `i ≤ 1` included. No model code calls it.
- **`ConvertAt`:** guarded on both sides, the pointer's base type included. The legality and result of a conversion read the underlying types. For example, `copyChecker`→`uintptr` and `*isync.Mutex`→`*B` for `type B bool` would be legal in the model but not in Go.
- **`FieldRefAt`:** guarded. The i-th field of a redefined struct is the model's.
- **`ArraySliceAt`:** guarded, for a redefined named array type.
- **`EqNilAt`, `PointerOfAt`:** guarded. Nilability is read from the underlying type: the model's `copyChecker` is a nil-able `unsafe.Pointer` where Go's `uintptr` panics.
- **`FuncResolveAt`:** no guard. It dispatches to translated generic helpers (`new(T)`, `*p`, `x.(T)`), which run ordinary Go at `T` and read no layout.

**Tests.**
- **Harness** (`diff/layout_test.go`). It has `type MS struct{ mu Mutex; n int }` with a Mutex the test declares redefined, and `SM` with the real `sync.Mutex`, whose field is the trusted `internal/sync.Mutex`.
  - These answer as in Go: `Kind`, `NumField`, `Field(i).Name/Type`, `ValueOf(s)` (with `Kind`, `Type` and `Interface`), and `FieldRefAt(&s, 1)` (`Value.Field(1)`'s primitive).
  - These are stuck: `Kind`/`NumField`/`FieldType`/`Underlying` of `Mutex`; `ValueOf(&s.mu).Elem()`; `ValueOf(Mutex{})`; `arrayOf(MS)` at lengths 1 and 2, and `arrayOf([1]MS)`; `isZeroSize` through `struct{MS; *int}` and `struct{Mutex; *int}`; `[1]Mutex`; `ConvertAt(*Mutex, *MS)`.
  - `TypeOf(TypeOf(0)).Kind()` is stuck.
  - Every earlier test is still green, including about 7,000 comparisons of reflectlite and `errors.As`. `errors.As` on `struct{ v any }` errors now matches Go where it used to be stuck.
- **Lean** (`Tests/ReflectTypeQuery.lean`, `Tests/ReflectLayoutModelled.lean`):
  - The same `S` over `internal/sync.Mutex` answers `kind`, `numField`, `fieldName` and `fieldType`.
  - Every row on Mutex except `identByName` is none, and `arrayOf S` is none.
  - `kind` of `reflect.rtype` is none.
  - `directIfaceN 2 S = some false`, without a question about Mutex.
  - `zeroSizeN n S = none`, and `directIfaceN` of a struct whose last field is a Mutex is none. `isDirectIface` and `isZeroSize` recurse only through queries on the component types.

**Witness (rule #8).**
- The minimal program is `S` above.
- **Real use.** Every etcd API message (e.g. `etcdserverpb.PutRequest`) holds `state protoimpl.MessageState`, whose `pragma.DoNotCopy` is a `[0]sync.Mutex`.
  - protobuf-go reflects on these structs field by field.
  - etcd's `txn.isNil` calls `reflect.ValueOf(msg).IsNil()` on them. That is pointer kind, which is unaffected.
  - `[0]sync.Mutex` is zero-size without a question about Mutex.

**Proofs.**
- The guards broke `errors.As`/`Is`, reflectlite and reflectcore. All are re-proved, with no `sorry` and no new axiom.
- `#print axioms` gives only `[propext, Classical.choice, Quot.sound]` for:
  - `errors.wp_As`, `wp_AsType`, `wp_Is`, `wp_initialize'`;
  - reflectlite `wp_TypeOf`, `wp_ValueOf`, `rtype.wp_{Elem,Kind,AssignableTo}`, `Value.wp_Set`, `wp_initialize'`.
- **Spec changes** (none weakens a top-level theorem):
  - `errors.AsDecided` gains `go.layoutModelled T = false`. `asModelled`'s rtype-layout conjunct becomes `go.layoutModelled t = false`.
  - Reflect `TypeOf` loses its rtype premise.
  - Kind-reading specs take `[NotLayoutModelled T]`.
  - In etcd-grove:
    - the `ValueOf` Elem triple and `errors.{AsNoMatch,AsLeafTy,AsLeaf}` take `go.layoutModelled T = false`, discharged by `decide` at `APIStatus`, `writerToResponse`, `*corruptObjectDeletedError` and the k8s `Obj`;
    - the k8s `ObjSpec` gains `objTy_notLayoutModelled`, which the driver proves.

**Builds.**
- Perennial: the full chunked build passed (3 chunks, exit 0; the only `sorry`s are the 152 GeneratedProof ones, as before). `go test ./goose/...`, the harness, and the `--check` of gen-layout-modelled, gen-link and meta-lib all pass.
- etcd-grove: EG_GATES.

**Audit (criterion 14) of the reflect/reflectlite/errors overlays.**
- **`rtype` values (Go: `*rtype`):** now `layoutModelled`, so opaque.
- **`Value`, `Method`, `MapIter`, `SelectCase`:** `layoutModelled`.
- **`reflect.Type`/`reflectlite.Type`, `tok` in place of `common`/`uncommon`:** unobservable. An interface type is never a dynamic type, only the package's own `rtype` implements it in either Go or the model, and no row reads an interface's methods.
  - `reflect`'s had no MODEL marker; one is added (`1e3c8a368`).
- **Panic values:** the same types as real (`*ValueError`, strings).
- **`errors.Is`:** returns a `bool`.
- No other `MODEL:` marker changes a dynamic type.
- **Outside the three overlays:** the trusted `internal/sync.Mutex` and `sync.copyChecker` change layouts, so they are now in the list.

— upamanyus worker (handoff pickup, reflection)
