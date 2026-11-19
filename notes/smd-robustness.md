# The structured-merge-diff driver's robustness theorem (2026-11-19)

Goal: a closed `Robustness.Robust` theorem about `examples/k8s/smd` (`Main`: nine server-side apply
and update steps through structured-merge-diff's `merge.Updater.Apply`/`Update`, each checked
against the expected object, managed fields and conflicts, with a panic on any difference), so that
"no panic" means SMD computes exactly those results. This stage: the plumbing and the statement,
building, with `Main.wp_proof` a `sorry`. SMD's translation: `notes/smd-goose.md`.

## The statement

`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/smd/TopLevelRobustness.lean` (the file to audit):

    def smd_driver_robust.spec : Prop :=
      ∀ [lctx : GoLocalContext] [sem : go.Semantics]
        [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions] (σ : state)
        (g : GlobalState) (bound : Nat),
        Robustness.Robust [] [(smdProgram, σ)] g bound

with the trivial extension (`attribute [local instance] trivialExts ...`), and the program
(`Proof/.../k8s/smd/TopLevelDefs.lean`):

    def smdProgram : Expr :=
      Seq (App (Val github_com.mit_pdos.etcd_grove.examples.k8s.smd.initialize') (Val #()))
        (App (App (Val (GoInstruction (FuncResolve github_com.mit_pdos.etcd_grove.examples.k8s.smd.Main []))) (Val #())) (Val #()))

One machine that never crashes runs the driver's initialization (SMD's five packages and the
standard library's they import) and then `Main()`, a fresh Go process (`Robust`'s premise); for any
Go semantics and package assumptions, in every execution of fewer than `bound` steps no thread is
stuck and none has an unrecovered panic.

- **The bound**: any (a parameter), as `goose/prophkv`'s: `Main.spec` takes no receipt or thread
  bound, so `goose_adequacy` runs at `N = n + 1`, `T = n + 2` for every `n`. If the proof of `Main`
  turns out to need one (a counter that must not wrap), the statement takes the bound it needs.
- **`Main.spec`** (`Spec/.../k8s/smd/Main.lean`), as prophkv's:

      abbrev Main.spec : Prop :=
        {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd }}
          (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.smd.Main)) (Val #()))
        {{ RET #(); True }}

  at `HeapGS HasLC.hasLC GF`. Returning normally is the whole guarantee: every check of the
  driver is a panic.

## The files

- Translation: project `k8s-smd` of `etc/goose.py` (`local="examples/k8s/smd"`, the driver's own
  Go module, lean roots `sigs.k8s.io/structured-merge-diff/v7=` and `github.com/mit-pdos/etcd-grove=`,
  so the driver's module imports project `smd`'s `Code.sigs_k8s_io...` modules);
  `Code/github_com/mit_pdos/etcd_grove/examples/k8s/smd.{lean,toml}`, `GeneratedProof/...`.
  `etc/goose.py --check` now also checks `GO_MOD_TAG_PINS`: the driver's `go.mod` must require
  `sigs.k8s.io/structured-merge-diff/v7` at project `smd`'s `tag` (`v7.0.0`, the tag of its `rev`
  `8d11054b`) and must not replace it (SMD is required at a tag, so `GO_MOD_PINS`' pseudo-version
  check does not apply).
- Package facts: `Proof/sigs_k8s_io/structured_merge_diff/v7/{value,schema,fieldpath,typed,merge}/
  Base.lean` and `Proof/.../k8s/smd/Base.lean`, every fact `True` (nothing reads a package variable
  yet). `etc/gen-init.py` (`SPECIAL[_SMD + ...]`, root `...examples.k8s.smd`, `PROGRAMS` entry)
  generates their `Init.lean` and the program's `PkgTable.lean`. The translated initializers are
  stepped (`errors.New` by Perennial's `wp_New_errorString`, slice literals, `[]byte` conversions,
  the walker pools' `sync.Pool` literals after `recv_eq_func_mk`, `merge`'s `var _ error =
  Conflicts{}`); the untranslatable ones are `TrustedCode` no-ops (`notes/smd-goose.md`). **No
  axiom was added for the initializers.** The program's initialization does run `reflect`'s
  existing generated `Proof/reflect/Init.lean`, whose trust-boundary axiom
  `Perennial.reflect.opaqueInitsOk` (already in the baseline, bbolt's and raft's too) is in the
  trust base.
- Link: `etc/gen-link.py --k8s-smd` from `etc/link-lean-first-k8s-smd.txt` (namespace `k8s_smd`).
- Closed theorem: `Proof/.../k8s/smd/Results.lean`, `smd_driver_safe` (the result is `#()`, no
  thread stuck, none with an unrecovered panic), from Perennial's `goose_adequacy` directly, as
  prophkv's, with the generated `wp_initialize'` at the generated table's `getIsPkgInit_wf`. (Not
  through `init_adequate`: its module, `examples/lib/etcdstart/Adequacy.lean`, imports the etcd
  server's start rights, prometheus, the WAL and bbolt invariants; the proof is the same few lines.)
- `Proof/.../k8s/smd/TopLevelRobustness.lean`: `smd_driver_robust`, by `Robust.of_single`.
- Trust base: `etc/tcb-collections/smd.txt`.

## What is trusted

`etc/tcb-report.py --collection etc/tcb-collections/smd.txt`:

- `sorry k8s_smd.Main.wp_proof`;
- the standard library as SMD calls it (names-only in Perennial), trust-boundary axioms whose spec
  files say why each is true of Go (go1.27's source quoted):
  - `reflect.DeepEqual.wp_proofNil` (`Spec/reflect/DeepEqualNil.lean`): `DeepEqual(nil, nil)` is
    `true`. `schema.StructField.Equals` compares the fields' `Default`s with it; the driver's schema
    has none. A second spec beside bbolt's `spec_pgidSet`, in a file of its own so that SMD does
    not import bbolt (gen-link's `reflect_DeepEqual+Nil`);
  - `slices.BinarySearchFunc.wp_proof`: for a `cmp` that on each element returns a pure `c e` and
    keeps a resource, with signs non-decreasing along the slice, the least index with `c ≥ 0` and
    whether `c = 0` there;
  - `slices.Insert.wp_proof`: `Insert(s, i, v...)` holds `s[:i] ++ v ++ s[i:]`, with its capacity
    (`s`'s ownership given up);
  - `sort.SliceStable.wp_proof`: with a `less` deciding a strict weak order, a sorted permutation
    (stability not stated);

  linked in the driver's `Link.lean` so that the collection lists them; their users are SMD's
  functions' proofs, not written yet;
- `Perennial.reflect.opaqueInitsOk` (above).

`etc/tcb-baseline.txt` has the four axioms and the `sorry` added by hand (its `--check --update`
needs the whole repository built; the collection's was run on the driver's roots only).

## Stage 2: a model of SMD, the specs of its API, `Main` over them (2026-11-19)

**Superseded (2026-11-19, `notes/smd-plan.md`)**: the model below transcribed SMD's algorithm and
the API specs returned "what the model computes" under a premise "the model does not panic" (an
implementation's spec, a premise no caller can check). They were replaced by abstract specs over a
new vocabulary (`Proof/sigs_k8s_io/structured_merge_diff/v7/<pkg>/Defs.lean`); `Model/`, `Own.lean`,
`OwnLaws.lean` and the driver's `Literals.lean` were deleted, the driver's proofs reset to `sorry`.
The section is kept as the record of that attempt.

`Main.wp_proof` is proved over specs of the SMD functions it calls; those specs are stated over a
pure model of SMD, and their proofs are the next stage's (`sorry`, below).

### The model (`Proof/sigs_k8s_io/structured_merge_diff/v7/Model/`, ~1500 lines)

`Value` (`UVal`: unstructured `null`/`bool`/`int64`/`string`/list/map, a map's entries sorted by
key; `UVal.equals`, `UVal.compare`, `FieldList`), `Schema` (`TypeRef`/`Atom`/`ListT`/`MapT`/
`StructField`, `Resolve`, `FindNamedType`, `FindField`, the `Equals` methods, `keysNodup`),
`Fieldpath` (`PE`, `PathElementSet` as sorted lists, `PSet`, the trie of members and children, its
`Insert`/`Union`/`Intersection`/`Difference`/`RecursiveDifference`/`EnsureNamedFieldsAreMembers`/
`Iterate`/`Equals`, `VSet`, `MF`), `Typed` (the walkers `validateW`, `toFieldSetW`, `mergeW`,
`compareW`, `removeW`, `reconcileW` and their helpers; `TV`), `Merge` (`reconcileMF`, `update`,
`prune` with the add-backs, `apply`, `updateObj`, `conflictsOf`, `conflictsEquals`). Each function
transcribes the Go function (the same loops, the same case order), so that each Go function's
proof is a refinement step. Every function is structurally recursive (fuel where Go loops over two
lists or walks a value: the wrappers give more than enough), so that the kernel runs it:
`Scenario.lean`'s facts are `decide +kernel` (no `native_decide`, no axiom). Two Lean points: a
mutual block of functions over different types compiles by well-founded recursion (irreducible;
kernel `decide` then gets stuck), so the schema's `Option ListT`/`Option MapT`/`List StructField`
are spelled `OptListT`/`OptMapT`/`Fields` inside its mutual inductive, and the functions take
their recursive calls through closures (`PSet.descend`) or folds instead of `let rec`/`where`; and
`String`-to-`GoString` coercions do not reduce in the kernel (`go!` literals only).

**Where the model is unfaithful or restricted** (each a premise of the specs or excluded by the
representation predicates): unstructured values only, no floats (`ownU`); schemas without
element-relationship overrides, unions or field defaults (`ownSchema`); an updater without
ignored fields or filter, with an identity converter (`ownUpdater`, `isIdentityConverter`), every
managed set at the request's version; Go map iteration in key order (unobservable in the walkers;
in `ConflictsFromManagers` the specs allow any order of managers); errors as a flag (which error is
not modelled); panics as `Res.panic`/`ApplyRes.panic` where Go panics (a nil `value.Value`, which
`merge` returns when its walker's output is nil), with "the model does not panic" a spec premise.
Quirks of SMD kept: list items' merge errors dropped (`nonissues/smd-merge-list-item-errors-dropped.md`),
`RemoveItems` turning an emptied map or list into `null`, `ToFieldSet` ignoring
`listItemToPathElement`'s errors, set structure (`Union` keeps empty children, `Difference` drops
them) as `Set.Equals` sees it.

**Validated against the Go run** (`Scenario.lean`): the driver's nine steps in the model, and every
check of the driver true of them, decided by the kernel: the objects, every manager's owned set,
step 3's no-op `Apply` returning a nil object (and a non-nil one with `ReturnInputOnNoop`), step
4's conflicts `[{A, .replicas}]` (managers then an empty map, model `ApplyRes.conflicts`), the
list order `[b1, a2]` after step 7.

### Representation predicates (`Own.lean`, `OwnLaws.lean`)

`ownU` (an `interface{}` of unstructured data), `ownValue` (a `*valueUnstructured`), `ownPE`,
`ownPath`, `ownSet` (the trie, slices of path elements and set nodes), `ownVSet` (a
`versionedSet` in an interface), `ownMF`, `ownTV`, `ownUpdater`, `ownConflicts`: all persistent
(`↦□`; SMD never writes a value it returned, a caller gives up its literals to read-only),
instances in `OwnLaws.lean`. `ownSchema` is exclusive: `Schema.FindNamedType` and `Map.FindField`
build lazy indexes (`sync.Once`, `atomic.Pointer`), `ownLazyIndex` either fresh (zero) or built
(`sync.isOnce` with the index persistent); the schema's immutable fields are persistent field
points-tos. Its definition is not part of the trust base (no top-level statement names it): the
next stage may refine the "built" disjunct; `newSchema`'s proof establishes the fresh one.

### The specs (`Spec/sigs_k8s_io/structured_merge_diff/v7/<pkg>/`)

`value.NewValueInterface`, `value.Equals`, `typed.AsTyped`, `typed.TypedValue.AsValue(_ptr)`,
`fieldpath.ManagedFields.Equals(_ptr)`, `fieldpath.FieldNameElement`, `fieldpath.KeyElement`,
`fieldpath.NewSet`, `fieldpath.NewVersionedSet`, `merge.UpdaterBuilder.BuildUpdater`,
`merge.Updater.Apply`, `merge.Updater.Update`, `merge.Conflicts.Equals(_ptr)` (the `_ptr` forms:
the method called through a pointer, as the driver's code does). `Apply`/`Update` return what the
model's `apply`/`updateObj` compute (`applyPost`/`updatePost` in `Own.lean`; `Update` returns its
`newObject` argument itself); `Apply`'s conflicts are `conflictsOf order` for some `order` a
permutation of the model's conflicting managers. Premises: the updater (`ownUpdater`), managers at
the request's version, a named type for the objects (the schema's indexes are owned by
`ownSchema`; an inlined type's would be owned by no one), `Schema.keysNodup` (key fields are
sorted with `sort.SliceStable`, whose trust-boundary spec does not state stability), no model panic.
Proved: `FieldNameElement`, `NewVersionedSet`, `TypedValue.AsValue`; the rest `sorry`.

### The driver (`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/smd/`)

`Defs.lean` (`ownState`), `Literals.lean` (a map or `ManagedFields` literal is an `ownUMap`/`ownMF`
of its sorted entries), the specs and proofs of every driver function (`newSchema`, the path
helpers, `applied`/`updated`, `container`, `concat`, the converter's methods, `state.typedObj`/
`apply`/`check`: no `sorry`), and `Main.wp_proof` over them and the SMD specs.

## What is left (the next stage's worklist)

The SMD functions' proofs, bottom-up (callee DAG, the call graph of notes/smd-goose.md):

1. `value`: `NewValueInterface` (allocator), `Equals` (`EqualsUsing`, `ListEquals`, the unstructured
   maps' `EqualsUsing`/`Iterate`), and `Compare` under `PathElement.Compare`.
2. `fieldpath`: `KeyElement`; `PathElement.{Compare,Equals}`, `PathElementSet.{Insert,Has,Union,
   Intersection,Difference,Equals}` (over the `slices.BinarySearchFunc`/`Insert` axioms), `Set.*`
   and `SetNodeMap.*` (refining the model's fuelled merges), `NewSet`, `ManagedFields.Equals(_ptr)`.
3. `schema`: `Resolve`/`FindNamedType`/`FindField` (the lazy indexes: `ownLazyIndex`'s fresh to
   built), the `Equals` methods (`reflect.DeepEqual(nil, nil)`).
4. `typed`: the helpers, then the walkers (`Validate` → `AsTyped`; `ToFieldSet`, `Merge`, `Compare`,
   `RemoveItems`, `ReconcileFieldSetWithSchema`; the `sync.Pool`s of walkers: their package facts
   in the `Base.lean`s, `etc/gen-init.py`'s `SPECIAL`), `TypedValue.AsValue_ptr`.
5. `merge`: `UpdaterBuilder.BuildUpdater` (`wp_auto` does not step its struct-field loads),
   `reconcileManagedFieldsWithSchemaChanges`, `update`, `prune`, `addBack*`,
   `ConflictsFromManagers`, then `Updater.Apply`/`Update`; `Conflicts.Equals(_ptr)`.

Also left: `SpecPlan/Spec/PkgInit/` for SMD and the driver (`etc/gen-specs-pkginit.py --check`, as
before this stage).

## Before stage 2: what remained


- **Specs of SMD's API** the driver calls, then `Main.wp_proof` taking them: `typed.AsTyped`,
  `value.NewValueInterface` (of `map[string]interface{}`, `[]interface{}`, `string`, `int64`),
  `merge.UpdaterBuilder.BuildUpdater`, `merge.Updater.Apply`/`Update` (the object and managed fields
  each step produces, `Conflicts` on step 4), `typed.TypedValue.AsValue`, `value.Equals`,
  `fieldpath.ManagedFields.Equals`, `fieldpath.NewSet`/`NewVersionedSet`/`MakePath`-style path
  builders, `merge.Conflicts.Equals`, and the error interface assertion `err.(merge.Conflicts)`.
  Their proofs cover the 311 SMD functions of `notes/smd-goose.md`'s table, over the four
  stdlib axioms above and Perennial's `sync.Pool`, `sync.Once`, `atomic.Pointer`, `fmt`, `errors`,
  `strings`, `sort.Strings` specs.
- **Package facts**: the proofs will need what the variables hold (`value.HeapAllocator`,
  `EmptyRange`, `fieldpath.ErrUnknownPathElementType`, `typed`'s walker pools and `ruleKeepRHS`):
  facts in the `Base.lean`s and the `finish` steps in `etc/gen-init.py`'s `SPECIAL` entries.
- `SpecPlan/Spec/PkgInit/` (`etc/gen-specs-pkginit.py --check`) does not have SMD's or the driver's
  files (SMD's were already missing before this stage; not regenerated here).
