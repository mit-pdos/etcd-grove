# structured-merge-diff: the specs for the driver's robustness theorem (stage plan, 2026-11-19)

The spec-first plan (`notes/spec-first-plan.md`) for proving `smd_driver_robust`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/smd/TopLevelRobustness.lean`, unchanged: the
driver `examples/k8s/smd`'s `Main` never panics) over specs of structured-merge-diff v7.0.0 (SMD).
The user's instruction: "write per-function specs that are enough to prove the top-level result.
First write all the specs, informally review them, then write invariants, then write proofs."

**Where it stands: Draft, repaired after review round 1** (commits on `worktree-smd-robustness`):
the scope, the abstract vocabulary (written in full, now **computable**), the specs of every SMD
function the driver calls (proofs `sorry`), the driver's own specs restated over them (proofs
`sorry`), the laws clients need (stated), the call DAG below them with an intended spec per
function, and the sanity checks, of which the driver's nine steps are now **proved by `decide`**
(`Proof/.../k8s/smd/Steps.lean`). No function proof was written. Next: review round 2 (fresh
`spec-reviewer`s on the repaired candidate), the user's decisions below, then the per-package
drafting of the DAG's specs, Test, Freeze, Prove.

**Round 1** (2026-11-19; reports `review-r1-merge.md`, `review-r1-vocab.md` in the coordinator's
scratch): one unsound statement, fixed (`Apply`'s premise admitted managed fields with a path below
a list item's key field: SMD then fails with a non-conflict error, reports a spurious conflict, or,
forced, returns duplicate keys); the vocabulary was incomplete (no lent wrapper, no set under
construction, missing laws) and not computable. What changed, finding by finding, is "Round 1's
repairs" at the end.

What it replaces: the earlier attempt (`notes/smd-robustness.md`, "Stage 2") stated the API as
"returns what a transcription of SMD's code computes", with the premise "the model does not panic":
the spec of an implementation, with a premise no caller can check (PRINCIPLES, "The spec of an API,
not of an implementation", "Every premise has a source the client sees"). Deleted:
`Proof/sigs_k8s_io/structured_merge_diff/v7/Model/{Value,Schema,Fieldpath,Typed,Merge}.lean`,
`Own.lean`, `OwnLaws.lean`, the driver's `Literals.lean`; the driver's `Scenario.lean` and
`Defs.lean` rewritten. Reused: the shape of the representation predicates (`ownU` → `isIface`,
`ownSet` → `isSet` over a canonical trie, `ownMF`, the identity converter), `UVal.compare` (the
order of a set's slices), the call graph tool (`etc/k8s-callgraph`).

## Scope

The configuration the result covers. Each restriction is a premise of a spec (checkable by the
caller on what it holds) or an exclusion of the representation predicates; **(R)** marks a scope
restriction (generality left out because it would cost much), with why.

**Values** (`isIface`, `value/Defs.lean`): SMD's unstructured values built by
`value.NewValueInterface`: `nil`, `bool`, `int64`, `string`, `[]interface{}`,
`map[string]interface{}` (`UVal`, maps canonical: sorted keys; `UVal.ofMap` sorts a literal's).
- (R) a map is a non-nil `map[string]interface{}`: Go's typed-nil map, which SMD reads as `{}`,
  is not admitted (the driver passes none); likewise a nil `ManagedFields` (`isMF`), which SMD
  treats as empty.
- (R, a margin) recursion depth: `value.Equals`, `AsTyped` and every walker recurse once per level
  of a value; Go's 1 GB stack bounds the depth (a fatal error, not a panic), GooseLang's semantics
  does not. A recursive schema admits conforming values deep enough to exhaust it, so the proved
  posts claim more than real Go gives at extreme depth (the `irr-depth.md` lesson); the driver's
  values have depth at most 3. Not a premise yet: decision D3.
- (R) No floats: SMD compares `int64` with `float64` by converting (SSA-05, kubernetes#143942:
  `Equals(MaxInt64, 2^63)` is true, equality is not transitive); with floats `value.Equals` is not
  `=`. No other integer types, no `map[interface{}]interface{}`, no reflection-backed values
  (`NewValueReflect`: names only in the translation).

**Schemas** (`Schema.WF`, `schema/Defs.lean`; decidable on a literal):
- (R) every type reference named (`TypeRef{NamedType: &n}`): no inlined atoms, no
  `ElementRelationship` override (`Resolve` then takes the schema's lock and caches: not owned);
- distinct type names, distinct field names in a map, every reference resolves, no type named
  `__untyped_deduced_` (reconciliation skips such maps);
- each atom exactly one of scalar / list / map (`isAtom`); scalars `numeric`, `string`,
  `boolean`, `untyped`;
- (R) lists **atomic**, or **associative with keys**, each key a declared scalar field of the
  element map type, keys distinct. Out: granular non-associative lists (they validate, but `Merge`
  fails on them: "invalid indexing of non-associative list"), sets (associative without keys:
  `PE.value` path elements), keys with defaults;
- maps: declared fields and an optional element type, atomic or granular (separable/unset);
- (R) no unions, no field defaults (`StructField.Equals` compares `Default` with
  `reflect.DeepEqual`, whose trust-boundary spec covers two nils only); a map type's `Unions` is the
  nil slice (an empty non-nil `Unions` is excluded, though SMD treats it alike).

**Objects**: `typed.AsTyped` without options (R: `AllowDuplicates` changes validation), so every
`TypedValue` the API takes conforms (`isTV` carries `conforms`); both objects of an `Apply`/
`Update` of one schema pointer and one type (else `Compare`/`merge` fail: the specs take one `sc`
and one `t`).

**The updater**: (R) an identity converter (`isIdentityConverter`), no `IgnoredFields` (required:
a non-nil map without an entry at the request's version makes `Apply` and `Update` panic,
`issues/smd-ignoredfields-missing-version-panic.md`), no `IgnoreFilter` (R: an empty non-nil map
behaves the same; nil kept as the simpler statement) (`Apply`/`Update` take
`isUpdater u cv nil nil rion`). `ReturnInputOnNoop` either way. One API version for `Apply`, every
manager's entry at the request's version: **required**, not a saving (round 1, finding 2). With
managers at several versions SMD prunes per version (`addBackOwnedItems`, one pass per version in
Go's map order, each from the previous pass's output) and removes a field owned at the applier's
own version (`issues/smd-apply-multiversion-prunes-owned.md`, Go-reproduced); with three or more
versions the result depends on the map's order. `Update` needs none (with an identity converter
every version compares alike: Go-checked, `TestUpdateVersions` below; 26 000 updates with mixed
versions in round 1).

**Managed fields**: any `ManagedFields` whose sets are canonical tries (every set SMD builds is;
`isSet`), reconciled with the schema by the specs themselves (`reconcile`, the identity on sets
written at this schema), and, for `Apply`, **`keysWithItems`** on every set: (1) a set with an
item's key field has the item, (2) a set with a granular item has its key fields, and (3) **no
path of the set extends a key field's path** (round 1). Every set SMD computes has it (`fieldSet`
and `compare` never produce a path below a scalar, `afterUpdate` only removes paths; Go: 10 000
random sequences, about 60 000 steps); `Apply` and `Update` keep it (`applyResult_premise`,
`updateResult_premise`). Without (1) or (3) the pruning can strip a key field off an item it keeps
(`ensureNamed` makes the key field a member when a path below it is), and `Apply` fails with an
error that is not a conflict, or leaves two items with one key and reports a spurious conflict, or,
forced, returns that non-conforming object with no error
(`nonissues/smd-apply-keyless-item-compare-error.md`, Go-reproduced). Round 0's form had only (1)
and (2) and admitted those inputs, so its "no other outcome" was false. The reviewer's alternative,
"(1) for paths at or below a key field" (`keysWithItems S t (ensureNamed S t s)`), also removed
every failure but is not kept by `Update` (an update removing item `k` takes `c[k]` and `c[k].name`
from another manager but leaves its `c[k].name.x`), so the chaining laws would be false with it.
Decided on a literal by `keysWithItemsB` (`keysWithItemsB_iff`).

**Known SMD defects, stated faithfully, not repaired**:
- an emptied container becomes `null`; `RemoveItems` turns every empty list or map it visits into
  `null` (SSA-01/02: kubernetes#143853, #104694) — `removeAt`;
- a list item goes as a whole when its path is pruned, even if another manager owns a field in it
  (SSA-03, kubernetes#134902) — `prune`, `removeL`;
- list items' merge errors are dropped (`nonissues/smd-merge-list-item-errors-dropped.md`) —
  unreachable in scope (conforming values, lists atomic or keyed);
- re-applying a struct deletes it when its remaining content is an unowned field and an empty list
  (`issues/smd-apply-deletes-own-struct.md`, round 1's G3) — `prune`'s third pass;
- with managers at several versions a field owned at the applier's version is pruned
  (`issues/smd-apply-multiversion-prunes-owned.md`, G2) — excluded by the one-version premise;
- a non-nil `IgnoredFields` without an entry at the version panics
  (`issues/smd-ignoredfields-missing-version-panic.md`, G4) — excluded by `IgnoredFields` nil;
- managed fields splitting an item from its key field, or below a key field (G1,
  `nonissues/smd-apply-keyless-item-compare-error.md`) — excluded by `keysWithItems`;
- SSA-04 (CRD status strategy) is the API server's; SSA-06 (FieldsV1 decoding rounds integer keys)
  is serialization, names only in the translation, out of scope.

**Outcomes**: in the scope `Apply` returns the merged object and managers, or (not forced) a
`Conflicts` error; `Update` never fails; `AsTyped` accepts exactly the conforming values. No other
error outcome is stated, and none exists in scope (Go: every `Apply` error of the random sequences
was a `Conflicts`).

## The vocabulary (written in full: `Proof/sigs_k8s_io/structured_merge_diff/v7/<pkg>/Defs.lean`)

Pure (no Iris), **computable** (round 1, P1): every definition branches on decidable conditions
only and recurses structurally (no well-founded recursion), so `decide` (the kernel's) evaluates it
on literals; the driver's nine steps are proved that way (`Steps.lean`, below).

| Name | Module | Meaning |
|---|---|---|
| `UVal` | value | an unstructured value, hand-written `DecidableEq` (`UVal.decEq`: the deriving handler fails on the nested `List (GoString × UVal)`); `UVal.ofMap` (a map literal, sorted), `kvsOf`/`insertKV`, `UVal.compare` (`value.Compare`, the order of sets' slices only) |
| `PE`, `Path`, `FieldList` | fieldpath | path elements (field, key, value, index) and paths (`DecidableEq` derived) |
| `FSet α` | fieldpath | a finite set: lists up to having the same members (a quotient); `mem`, `any`, `all`, `isEmpty`, `filter`, `bind`, `map`, `union`, `inter`, `diff`; equality decidable (both inclusions) and extensional |
| `PathSet` | fieldpath | `FSet Path`; `ofList` (non-empty paths), `single`, `under`, `IsEmpty` |
| `VSet`, `MF` | fieldpath | a versioned set (set, version, applied; `DecidableEq` by hand: the derived one transports along a set equality, stuck for the kernel); managed fields, an association list **sorted by manager** (`MF.get`, `MF.set`, `MF.ofList` for a literal, `MF.none`) so that equal managed fields are equal lists |
| `Trie`, `Trie.paths`, `Trie.Canonical` | fieldpath | the representation's trie (sorted, no empty child); clients never see it |
| `Scalar`, `ElemRel`, `TypeRef`, `Atom`, `Schema` | schema | a flat named-type schema; `Schema.find`, `fieldType`, `Schema.WF` (the scope, a `Bool` computation: `decide` proves it of a literal) |
| `conforms S t x` | typed | `x` validates against `t` (`TypedValue.Validate`): `conformsB … = true` |
| `keyOf ks x` | typed | an associative list item's key (its key fields, sorted by name) |
| `fieldSet S t x` | typed | `ToFieldSet`: scalars, atomic values, list items, map entries that are `null`/`{}`/undeclared |
| `removeItems S t x R` | typed | `RemoveItems`: `x` without `R`, emptied containers `null` |
| `merge S t l r`, `mergeKeys` | typed | `Merge` (`r` wins at leaves; per key; list items in `mergeKeys` order) |
| `compare S t l r : Cmp` | typed | `Compare`: removed, modified, added paths |
| `ensureNamed S t s` | typed | `EnsureNamedFieldsAreMembers`: `s` plus declared fields with paths below (computed by `namedAlong`; declaratively `ensureNamed_mem`) |
| `atomicNodes`, `reconcile S t s`, `schemaConsistent` | typed | `ReconcileFieldSetWithSchema`: subtrees under atomic nodes collapsed (`atomicNodes_mem`, `reconcile_mem`) |
| `reconcileMF`, `prune`, `afterUpdate`, `conflictsOf` | merge | the steps of SSA, over the typed operations; conflicts are a set of (manager, path) pairs |
| `applyResult … : ApplyOutcome` | merge | `ok obj mf'` or `conflicts cs` (`DecidableEq` by hand) |
| `updateResult … : MF` | merge | the managers after `Update` |
| `keysWithItems S t s`, `keysWithItemsB` | merge | `Apply`'s premise on each managed set (three clauses), and its decision procedure |

Representation predicates (all **persistent** but `freshSchema`, `freshAtom`, `ownSet` and
`isValF` below the discarded fraction; SMD never writes what it was given or returned). All are
**sealed** (`@[no_expose]`, round 1, P3): a client uses the laws; the package's own proofs
`import all` the `Defs` they unfold (`FieldNameElement`'s does). The importable modules are
`etc/api/smd.txt`; their interfaces `interface/{Spec,Proof}/sigs_k8s_io/`.

| Predicate | Meaning |
|---|---|
| `isIface i x` | an `interface{}` holding `x` (read-only slices and maps, discarded fractions) |
| `isValF v dq x` | a `value.Value` (`*valueUnstructured`), its wrapper at fraction `dq`, over an interface holding `x`: what SMD's recursion lends (`EqualsUsing` rewrites one wrapper per entry, `reuse`; the freelist allocator frees and reuses them) |
| `isVal v x` | `isValF v DFrac.discard x` (an abbreviation): what the API takes and hands out |
| `isFieldList s fl`, `isPE e pe`, `isPath s p`, `isPaths` | the `fieldpath` path types |
| `isSet p S` | a `*fieldpath.Set` whose trie is canonical with paths `S` (persistent) |
| `ownSet p S` | the same, **owned**: a set under construction (`NewSet`'s, the walkers' `Comparison` and field sets), which `Set.Insert` updates; `ownSet_persist` hands it out as `isSet` |
| `isVSet i e` | a `VersionedSet` (`versionedSet`) holding `e` |
| `isMF m mf` | a non-nil `ManagedFields` map holding `mf` (sorted) |
| `isTypeRef tr t` | a named `schema.TypeRef` |
| `isSchema sc S` | a `*schema.Schema` holding `S`, its lazy indexes (`FindNamedType`'s, each `FindField`'s: `sync.Once` + `atomic.Pointer`) under `sync.isOnce`: **persistent**, so concurrent readers are covered (the API server shares schemas); `freshSchema sc S` is a literal with zero indexes (built from `freshAtom`s by `freshSchema_intro`), made an `isSchema` by a ghost update (`isSchema_intro`) |
| `isTV p sc S t x` | a `*typed.TypedValue` of schema `sc`, type `t`, value `x`; **carries** `isSchema sc S`, `S.WF` and `conforms S t x` (round 1, P2: every typed operation drops those two premises) |
| `isUpdater u cv igf igfl rion` | a `*merge.Updater` (read-only), from `BuildUpdater` or a literal (`isUpdater_intro`: Kubernetes builds one directly) |
| `isIdentityConverter cv` | a `Converter` whose methods are the identity / `false` (Hoare triples on its dynamic type) |
| `isConflicts s cs` | a `merge.Conflicts` slice holding `(manager, path)` pairs |

The old `ownSchema` was exclusive (threaded through every call); `isSchema` is persistent. The old
sets were the trie itself (`PSet`, structure-equal); `PathSet` is the set, the trie canonical in the
representation, so `Set.Equals` is `=`.

**Laws** (`Proof/sigs_k8s_io/structured_merge_diff/v7/Laws.lean`, stated as `def <name>.law : Prop`,
proved after the freeze; all are the next phase's invariant work, none is proved yet):
- persistence of every persistent predicate (`isIface`, `isVal`, `isFieldList`, `isPE`, `isPath`,
  `isPaths`, `isSet`, `isVSet`, `isMF`, `isSchema`, `isTypeRef`, `isTV`, `isConflicts`,
  `isIdentityConverter`, `isUpdater`);
- fractions and ownership: `isValF_split` (fractional), `isValF_persist`, `ownSet_persist`,
  `ownSet_empty` (`&Set{}`);
- agreement: `isIface_agree`, `isValF_agree`, `isSet_agree`, `isMF_agree`, `isSchema_agree`;
- introduction (a client's literals): `isIface_scalar`, `isIface_list`, `isIface_ofMap` (a map
  literal's entries in any order, no sortedness premise), `isFieldList_intro`, `isPath_intro`,
  `isPaths_nil`/`_cons`/`_app`/`_length`, `isMF_intro` (over `MF.ofList`), `isConflicts_intro`,
  `isUpdater_intro`, `isTypeRef_intro`, `freshAtom_scalar`/`_list`/`_map`, `freshSchema_intro`,
  `isSchema_intro` (fresh → shared, a fancy update);
- elimination: `isTV_conforms`, `isTV_schema`;
- pure: `PathSet_ext`, `MF_ext` (sorted), `ensureNamed_mem`, `atomicNodes_mem`, `reconcile_mem`
  (the computable definitions' declarative readings), `reconcile_id`, `keysWithItemsB_iff`,
  `applyResult_premise`/`updateResult_premise` (the results keep `Apply`'s three-clause premise, are
  sorted and schema-consistent: chaining), `mergeF_none`.

## The API specs (`Spec/sigs_k8s_io/structured_merge_diff/v7/<pkg>/<F>.lean`)

Every function the driver calls (`examples/k8s/smd/smd.go`; the translated driver's calls). Each
takes `isPkgInit` of its package.

| Function | Pre | Post |
|---|---|---|
| `value.NewValueInterface(i)` | `isIface i x` | `isValF v (DFrac.own 1) x` (the fresh wrapper, whole) |
| `value.Equals(a, b)` | `isValF a dq1 x ∗ isValF b dq2 y` | both back, `r = true ↔ x = y` |
| `fieldpath.FieldNameElement(n)` | — | `isPE e (.field n)` (proof kept) |
| `fieldpath.KeyElement(fields...)` | `isFieldList s fl` | `isPE e (.key fl)` |
| `fieldpath.NewSet(paths...)` | `s ↦*{dq} ss ∗ isPaths ss ps` | `isSet p (PathSet.ofList ps)` |
| `fieldpath.NewVersionedSet(set, v, b)` | `isSet p S` | `isVSet i ⟨S, v, b⟩` |
| `ManagedFields.Equals` (and `_ptr`) | `isMF m1 a ∗ isMF m2 b` | `r = true ↔ a = b` |
| `typed.AsTyped(v, sc, tr)` | `isVal v x ∗ isSchema sc S ∗ isTypeRef tr t ∗ ⌜S.WF⌝` | `conforms S t x ∧ err = nil ∗ isTV p sc S t x` (which carries the schema), or `¬ conforms S t x ∧ p = nil ∧ err ≠ nil` |
| `TypedValue.AsValue` (value receiver) | — | its `value` field (proof kept) |
| `TypedValue.AsValue` (`_ptr`) | `isTV p sc S t x` | `isVal v x` |
| `UpdaterBuilder.BuildUpdater` | `b ↦{dq} ub` | `isUpdater u ub.Converter ub.IgnoredFields ub.IgnoreFilter ub.ReturnInputOnNoop` |
| `Updater.Apply` | below | below |
| `Updater.Update` | below | below |
| `Conflicts.Equals` (and `_ptr`) | `isConflicts s1 a ∗ isConflicts s2 b` | `r = true ↔ a = b` |

`Updater.Apply(lp, cp, ver, mfm, mgr, force)`:

    {{ isPkgInit merge ∗ isUpdater u cv nil nil rion ∗ isIdentityConverter cv ∗
       isTV lp sc S t live ∗ isTV cp sc S t config ∗ isMF mfm mf ∗
       ⌜∀ m e, mf.get m = some e → e.version = ver ∧ keysWithItems S t e.set⌝ }}
      u.Apply(lp, cp, ver, mfm, mgr, force)
    {{ (op, mfm', err).
       match applyResult S t rion live config ver mf mgr force with
       | ok obj mf' => err = nil ∗ isMF mfm' mf' ∗ (obj = none → op = nil) ∗ (obj = some x → isTV op sc S t x)
       | conflicts cs => op = nil ∗ isMF mfm' MF.none ∗ ∃ s l, err = Conflicts(s) ∧ l.Nodup ∧
                         FSet.ofList l = cs ∗ isConflicts s l }}

    applyResult S t rion live config ver mf mgr force :=
      mf0    := reconcileMF S t mf
      merged := merge S t live config
      mf1    := mf0.set mgr ⟨fieldSet S t config, ver, applied⟩
      new    := prune S t merged mf1 (mf0.get mgr)
      c      := compare S t live new
      confl  := conflictsOf mf1 mgr c          -- {(m, p) | m ≠ mgr, p ∈ mf1 m ∩ (c.modified ∪ c.added)}
      if ¬force ∧ confl ≠ ∅ then conflicts confl
      else ok (if ¬rion ∧ new = live then none else some new) (afterUpdate mf1 mgr confl c.removed)

    prune S t merged mf last :=                 -- none or empty last: merged
      p0 := removeItems merged (ens last)                              -- what mgr applied last time
      p1 := removeItems merged (ens(fs merged) \ (ens(fs p0) ∪ ens(∪ mf)))   -- add back owned
      removeItems merged ((ens(fs merged) \ ens(fs p1)) ∩ ens last)  -- add back dangling
    (ens = ensureNamed S t, fs = fieldSet S t)

`Updater.Update(lp, np, ver, mfm, mgr)`:

    {{ isPkgInit merge ∗ isUpdater u cv nil nil rion ∗ isIdentityConverter cv ∗
       isTV lp sc S t live ∗ isTV np sc S t new ∗ isMF mfm mf }}
      u.Update(lp, np, ver, mfm, mgr)
    {{ (op, mfm', err). op = np ∧ err = nil ∗ isMF mfm' (updateResult S t live new ver mf mgr) }}

    updateResult S t live new ver mf mgr :=
      mf0 := reconcileMF S t mf;  c := compare S t live new
      mf2 := afterUpdate mf0 mgr (conflictsOf mf0 mgr c) c.removed   -- others lose changed+removed
      s   := ((mf2 mgr).set \ c.removed) ∪ c.modified ∪ c.added
      mf2 with mgr ↦ (if s = ∅ then none else ⟨s, ver, not applied⟩)

**Why `Apply`'s post is a composition of the typed operations, not a declarative "what SSA
means".** There is no simpler faithful statement: the documented reading ("a field is removed iff
the manager applied it last time, did not apply it now, and no other applier claims it") is false of
SMD in places the driver does not reach but a client can, even on managed fields SMD computed
itself (round 1, finding 3): SSA-03 (an item is removed even though another manager owns a field
inside it); G3 (A applied `{spec: {}}` and owns `.spec`; the live `spec` also holds an unowned
`a` and an empty list `l: []`; A applies `{spec: {}}` again and SMD returns the object **without**
`spec`: the second pass drops `a`, the third sees no field path left under `spec` and removes it
as dangling, `issues/smd-apply-deletes-own-struct.md`). The reviewer tried the natural declarative
candidate (`removeItems merged ((ens L ∩ ens(fieldSet merged)) \ ens(mfUnion mf))`): it differs
from `prune` in 243 of 20 000 crafted cases, so D1 stands. `prune`'s header no longer gives a
"read as a whole" description; it lists these exceptions. The operations
composed are SMD's public `typed` and `fieldpath` API (`Merge`, `ToFieldSet`, `RemoveItems`,
`Compare`, `EnsureNamedFieldsAreMembers`, `ReconcileFieldSetWithSchema`, `Set` algebra), each
defined over values and paths, not over SMD's walkers; another implementation of the same API
(same `typed` operations) meets the spec. Decision D1 below.

**Margins** (what the code guarantees beyond the post): the conflicts' order (managers in Go's map
order, each manager's paths in the trie's preorder: stated only as "each pair once"); the error
messages; that the returned object is fresh (not the live one). Where the post claims **more**
than real Go (round 1, P8): recursion depth (Go's stack, above); and `AsTyped`'s error branch
formats values (`errorf("...%#v")`, `%T`, `PathElement.String`), so its proof will rest on `fmt`'s
trust-boundary axioms for arbitrary interface values (to check with `etc/tcb-report.py --roots`
when proved).

## The driver's specs, restated (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/smd/`)

Over the scenario (`Proof/.../k8s/smd/Scenario.lean`: `sc0`, `rootRef`, `version`, the path
builders `field`/`mapKey`/`item`/`itemField`/`containerPaths`, `applied`/`updated` as `VSet`s, `St`)
and `Defs.lean` (`isUMap m kvs := isIface (map m) (.map kvs)`; `ownState s sc st`: the state
struct, `isSchema sc sc0`, an updater without `ReturnInputOnNoop` with an identity converter,
`isTV lv sc sc0 rootRef st.live`, `isMF mfm st.mf`):

- `newSchema` → `isSchema sc sc0` (its proof does `isSchema_intro` at the end);
- `field`/`mapKey`/`item`/`itemField` → `isPath s (…)`; `containerPaths` → `isPaths`;
  `applied`/`updated` (`isPaths ss ps`) → `isVSet v (applied ps)`/`(updated ps)`;
  `container` → `isUMap m (containerKVs n i)`; `concat`, the converter's methods: unchanged;
- `state.typedObj(m)`: `isUMap m kvs ∗ ⌜conforms sc0 rootRef (.map kvs)⌝` → `isTV p sc sc0 rootRef (.map kvs)`;
- `state.apply(m, mgr)`: `ownState s sc st ∗ isUMap m kvs ∗ ⌜conforms …⌝ ∗ ⌜st.mf`'s sets at
  `version`, `keysWithItems` (three clauses)⌝ `∗ ⌜applyResult sc0 rootRef false st.live (.map kvs)
  version st.mf mgr false = ok obj mf'⌝` → `RET obj.isSome; ownState s sc ⟨obj.getD st.live, mf'⟩`;
- `state.check(m, mfm)`: `ownState s sc st ∗ isUMap m kvs ∗ isMF mfm mf ∗ ⌜st.live = .map kvs ∧
  st.mf = mf⌝` → `ownState s sc st`.

Their proofs (all proved before, over the old vocabulary, but `concat` and the converter's) are
`sorry` until the freeze: `newSchema`, `field`, `mapKey`, `item`, `itemField`, `containerPaths`,
`applied`, `updated`, `container`, `state.typedObj`, `state.apply`, `state.check`, `Main`.

## The call DAG (for parallel drafting)

From `etc/k8s-callgraph` (VTA over RTA, root the driver's `Main`), the SMD functions reachable
without passing through the reflection implementation (`*Reflect*`) or package initializers,
closures folded into their enclosing function. The 311 of `notes/smd-goose.md` counted closures
and the `typed.TypedValue` methods the driver does not reach. Each function's intended spec is in
the abstract vocabulary; "internal" marks a spec that may mirror its code (PRINCIPLES "Scope": used
only inside its package). Out-of-scope rows (reached by the over-approximating call graph, never in
the scope: `mapUnstructuredInterface`, ignored-field filters, `CopyInto`, unions, sets,
`ExtractItems`) get no spec, or a `False`-free trivial one.

The DAG by package: **`value` 71, `fieldpath` 61, `schema` 13, `typed` 92, `merge` 12** (249).
Drafting order: `value` and `schema` (leaves, over the stdlib axioms and `sync.Once`), then
`fieldpath` (the trie lemmas: canonicity kept by each operation), then `typed` (the walkers: each
walker's invariant is "its output is the abstract function on the subtree"), then `merge`.
Unclear abstract specs: none at the level of the table; the hard ones are the walker invariants
(`mergingWalker.visitListItems` ↔ `mergeKeys`, checked against Go on 20000 random cases;
`reconcileWithSchemaWalker` ↔ `atomicWithChildren`) and `Set.Iterate`'s order (stated as "each
path once").

249 functions (closures folded into their enclosing function); by package: `fieldpath` 61, `merge` 12, `schema` 13, `typed` 92, `value` 71.

#### `fieldpath` (61)

| function | where | intended spec (abstract vocabulary) | callees |
|---|---|---|---|
| `FieldNameElement` | fieldpath/element.go:52 | API (proved). → `isPE e (.field n)` | 0 |
| `KeyElement` | fieldpath/element.go:57 | API. `isFieldList s fl` → `isPE e (.key fl)` | 0 |
| `MakePath` | fieldpath/path.go:82 | `isPE`s → `isPath s p` (no error for PathElements) | 0 |
| `MakePathElementMap` | fieldpath/pathelementmap.go:76 | empty `PathElementMap` (`isPEMap m ∅`) | 0 |
| `MakePathElementSet` | fieldpath/element.go:232 | empty `PathElementSet` (sorted list `[]`) | 0 |
| `MakePathElementValueMap` | fieldpath/pathelementmap.go:34 | empty `PathElementValueMap` | 1 |
| `NewExcludeSetFilter` | fieldpath/set.go:771 | out of scope (ignored fields nil): only reached under `IgnoredFields != nil` | 0 |
| `NewSet` | fieldpath/set.go:44 | API. `isPaths ss ps` → `isSet p (ofList ps)` (internally `ownSet` from `&Set{}`, then `ownSet_persist`) | 1 |
| `NewVersionedSet` | fieldpath/managers.go:37 | API. `isSet p S` → `isVSet i ⟨S, ver, b⟩` | 0 |
| `ManagedFields.Equals` | fieldpath/managers.go:63 | API. `isMF`s → `r ↔ a = b` | 4 |
| `Path.Copy` | fieldpath/path.go:75 | `isPath s p` → `isPath s' p` (fresh) | 0 |
| `Path.Equals` | fieldpath/path.go:39 | `r ↔ p = p'` | 1 |
| `Path.String` | fieldpath/path.go:30 | error strings only: some string | 1 |
| `PathElement.Compare` | fieldpath/element.go:87 | `PE.compare` | 2 |
| `PathElement.Equals` | fieldpath/element.go:133 | `r ↔ pe = pe'` | 2 |
| `PathElement.Less` | fieldpath/element.go:82 | `PE.compare a b < 0` | 1 |
| `PathElement.String` | fieldpath/element.go:170 | some string | 1 |
| `PathElementMap.Get` | fieldpath/pathelementmap.go:97 | lookup by `PE` (binary search: `slices.BinarySearchFunc` axiom) | 1 |
| `PathElementMap.Insert` | fieldpath/pathelementmap.go:84 | insert/overwrite, sorted (`slices.Insert` axiom) | 1 |
| `PathElementSet.Difference` | fieldpath/element.go:315 | sorted lists: `xs \ ys` | 1 |
| `PathElementSet.Equals` | fieldpath/element.go:348 | `r ↔ xs = ys` (sorted, so as sets) | 1 |
| `PathElementSet.Has` | fieldpath/element.go:340 | `pe ∈ xs` | 1 |
| `PathElementSet.Insert` | fieldpath/element.go:257 | sorted insert (no duplicate) | 1 |
| `PathElementSet.Intersection` | fieldpath/element.go:295 | sorted `xs ∩ ys` | 1 |
| `PathElementSet.Iterate` | fieldpath/element.go:361 | calls `f` on each, in order | 3 |
| `PathElementSet.Size` | fieldpath/element.go:337 | `xs.length` | 0 |
| `PathElementSet.Union` | fieldpath/element.go:268 | sorted `xs ∪ ys` | 1 |
| `PathElementValueMap.Get` | fieldpath/pathelementmap.go:58 | as `PathElementMap.Get` | 1 |
| `PathElementValueMap.Insert` | fieldpath/pathelementmap.go:52 | as `PathElementMap.Insert` | 1 |
| `Set.All` | fieldpath/set.go:401 | iterator over the paths (preorder); only through `Iterate` in scope | 0 |
| `Set.Difference` | fieldpath/set.go:106 | `isSet a A ∗ isSet b B` → `isSet r (A.diff B)` (canonical kept) | 2 |
| `Set.Empty` | fieldpath/set.go:353 | `r ↔ S.IsEmpty` | 2 |
| `Set.EnsureNamedFieldsAreMembers` | fieldpath/set.go:133 | `isSet p S ∗ isSchema` → `isSet r (ensureNamed S t s)` | 5 |
| `Set.Equals` | fieldpath/set.go:380 | `r ↔ A = B` (canonical tries) | 2 |
| `Set.Has` | fieldpath/set.go:361 | `r ↔ S p` | 2 |
| `Set.Insert` | fieldpath/set.go:63 | `ownSet p S` → `ownSet p (S ∪ {p})` (only on sets under construction: `NewSet`, walkers' sets) | 2 |
| `Set.Intersection` | fieldpath/set.go:90 | `isSet r (A.inter B)` | 2 |
| `Set.Iterate` | fieldpath/set.go:396 | calls `f` once per path of `S` (preorder; the order is the trie's, stated as "each path once") | 1 |
| `Set.RecursiveDifference` | fieldpath/set.go:122 | `isSet r {q ∈ A | no prefix of q (incl. q) in B}` | 2 |
| `Set.Size` | fieldpath/set.go:346 | the number of paths | 2 |
| `Set.String` | fieldpath/set.go:385 | some string | 2 |
| `Set.Union` | fieldpath/set.go:80 | `isSet r (A.union B)` | 2 |
| `Set.WithPrefix` | fieldpath/set.go:416 | `isSet r (S.under pe)` | 2 |
| `Set.iteratePrefix` | fieldpath/set.go:409 | internal: `Iterate` with a prefix | 6 |
| `SetNodeMap.All` | fieldpath/set.go:730 | internal | 0 |
| `SetNodeMap.Descend` | fieldpath/set.go:489 | internal (exclusive): the child set, created empty if absent | 1 |
| `SetNodeMap.Difference` | fieldpath/set.go:599 | internal: children part of `Set.Difference` | 3 |
| `SetNodeMap.Empty` | fieldpath/set.go:510 | internal: no path below | 1 |
| `SetNodeMap.EnsureNamedFieldsAreMembers` | fieldpath/set.go:671 | internal: children part | 4 |
| `SetNodeMap.Equals` | fieldpath/set.go:532 | internal: structural (= set equality on canonical) | 2 |
| `SetNodeMap.Get` | fieldpath/set.go:520 | internal: the child set if any | 1 |
| `SetNodeMap.Intersection` | fieldpath/set.go:577 | internal: children part | 3 |
| `SetNodeMap.Iterate` | fieldpath/set.go:723 | internal | 3 |
| `SetNodeMap.RecursiveDifference` | fieldpath/set.go:635 | internal: children part | 4 |
| `SetNodeMap.Size` | fieldpath/set.go:501 | internal | 1 |
| `SetNodeMap.Union` | fieldpath/set.go:548 | internal: children part | 2 |
| `SetNodeMap.iteratePrefix` | fieldpath/set.go:738 | internal | 1 |
| `excludeFilter.Filter` | fieldpath/set.go:788 | out of scope (ignored fields) | 1 |
| `versionedSet.APIVersion` | fieldpath/managers.go:49 | `e.version` | 0 |
| `versionedSet.Applied` | fieldpath/managers.go:53 | `e.applied` | 0 |
| `versionedSet.Set` | fieldpath/managers.go:45 | `isSet p e.set` | 0 |

#### `merge` (12)

| function | where | intended spec (abstract vocabulary) | callees |
|---|---|---|---|
| `ConflictsFromManagers` | merge/conflict.go:108 | `isMF`-like map of conflict sets → a list `l`, `Nodup`, `(m,p) ∈ l ↔ cs m p`, `isConflicts` | 3 |
| `Conflict.Equals` | merge/conflict.go:44 | `r ↔ c = c'` | 1 |
| `Conflicts.Equals` | merge/conflict.go:86 | API. `r ↔ a = b` | 1 |
| `Updater.Apply` | merge/update.go:209 | API. outcome `applyResult` (see the spec) | 11 |
| `Updater.Update` | merge/update.go:167 | API. managers `updateResult`, object `newObject` | 10 |
| `Updater.addBackDanglingItems` | merge/update.go:345 | internal: `removeItems S t merged ((ens(fs merged) \ ens(fs pruned)) ∩ ens L)` | 9 |
| `Updater.addBackOwnedItems` | merge/update.go:284 | internal: `addBackOwnedItemsForVersion` at the one version (all managers at `ver`) | 5 |
| `Updater.addBackOwnedItemsForVersion` | merge/update.go:313 | internal: `(merged, removeItems S t merged (ens(fs merged) \ (ens(fs pruned) ∪ ens M)))` | 7 |
| `Updater.prune` | merge/update.go:256 | internal: `prune S t merged mf1 last` | 9 |
| `Updater.reconcileManagedFieldsWithSchemaChanges` | merge/update.go:374 | internal: a fresh map of `reconcileMF S t mf` | 5 |
| `Updater.update` | merge/update.go:73 | internal: `.conflicts (conflictsOf ..)` if not forced and any; else `afterUpdate mf mgr confl c.removed` and `c = compare S t old new` | 12 |
| `UpdaterBuilder.BuildUpdater` | merge/update.go:49 | API. → `isUpdater u cv igf igfl rion` (the builder's fields) | 0 |

#### `schema` (13)

| function | where | intended spec (abstract vocabulary) | callees |
|---|---|---|---|
| `Atom.Equals` | schema/equals.go:76 | structural equality of atoms (`reflect.DeepEqual(nil,nil)` axiom via StructField) | 2 |
| `List.Equals` | schema/equals.go:186 | structural | 1 |
| `Map.CopyInto` | schema/elements.go:174 | unreachable in scope (only `Resolve` with an override) | 0 |
| `Map.Equals` | schema/equals.go:101 | structural (no unions: `Union.Equals` on empty slices) | 3 |
| `Map.FindField` | schema/elements.go:157 | `isSchema`-owned map type → `lookupKV n fs` (the once builds the index) | 0 |
| `Schema.CopyInto` | schema/elements.go:369 | unreachable in scope (override path) | 0 |
| `Schema.FindNamedType` | schema/elements.go:283 | `isSchema sc S` → `S.find n` (once-built index) | 0 |
| `Schema.Resolve` | schema/elements.go:317 | `isSchema sc S ∗ isTypeRef tr t` → the atom of `S.find t.name` (no override: lock untouched); the empty TypeRef → the zero atom | 2 |
| `Schema.resolveNoOverrides` | schema/elements.go:295 | internal: as `Resolve` for a named ref | 1 |
| `StructField.Equals` | schema/equals.go:172 | `r = true` on two in-scope fields with equal name/type (defaults nil: `DeepEqual(nil,nil)`) | 1 |
| `TypeRef.Equals` | schema/equals.go:42 | `r ↔ t = t'` (named, no override) | 1 |
| `Union.Equals` | schema/equals.go:131 | unreachable (no unions) | 1 |
| `UnionField.Equals` | schema/equals.go:158 | unreachable (no unions) | 0 |

#### `typed` (92)

| function | where | intended spec (abstract vocabulary) | callees |
|---|---|---|---|
| `AsTyped` | typed/typed.go:53 | API. `conforms` → `isTV`, else error | 1 |
| `ReconcileFieldSetWithSchema` | typed/reconcile_schema.go:119 | `isSet p s ∗ isTV` → `nil` if `schemaConsistent`, else `isSet r (reconcile S t s)` (either way `reconcile`) | 5 |
| `deduceAtom` | typed/helpers.go:123 | single-kind atoms: the atom itself | 6 |
| `errorf` | typed/helpers.go:93 | a non-nil error | 0 |
| `getAssociativeKeyDefault` | typed/helpers.go:187 | `(nil, nil)` (no defaults in scope) | 2 |
| `handleAtom` | typed/helpers.go:142 | dispatch to the walker's `doMap`/`doScalar`/`doList` (a spec per walker: `atomHandler` bundle) | 19 |
| `isUntypedDeducedMap` | typed/reconcile_schema.go:280 | `false` in scope (`Schema.WF`) | 1 |
| `isUntypedDeducedRef` | typed/reconcile_schema.go:284 | `false` in scope | 0 |
| `keyedAssociativeListItemToPathElement` | typed/helpers.go:200 | `keyOf ks x` (`none` ↦ error) | 9 |
| `listItemToPathElement` | typed/helpers.go:255 | `keyOf` for associative-with-keys; error for non-associative (unreached in scope) | 2 |
| `listValue` | typed/helpers.go:161 | `.null` ↦ nil list; `.list vs` ↦ list view; else error | 3 |
| `mapValue` | typed/helpers.go:173 | nil ↦ error; `.null` ↦ nil; `.map` ↦ view; else error | 3 |
| `merge` | typed/typed.go:249 | internal: `merge S t l r` (both `isTV` of one schema and type) | 5 |
| `removeItemsWithSchema` | typed/remove.go:36 | `isVal (removeAt S t R x)` | 3 |
| `resolveSchema` | typed/helpers.go:105 | resolve then `handleAtom` | 4 |
| `setItemToPathElement` | typed/helpers.go:235 | unreached in scope (no sets) | 3 |
| `typeRefAtPath` | typed/reconcile_schema.go:267 | `reconChild` | 1 |
| `validateScalar` | typed/validate.go:88 | no error ↔ `scalarOk s x` (or nil value) | 7 |
| `Comparison.ExcludeFields` | typed/compare.go:65 | out of scope (ignored fields nil: returns `c`) | 2 |
| `Comparison.FilterFields` | typed/compare.go:75 | nil filter: returns `c` unchanged | 0 |
| `TypedValue.AsValue` | typed/typed.go:95 | API (proved): its `value` field | 0 |
| `TypedValue.Compare` | typed/typed.go:157 | `isTV`s of one schema/type → `Comparison` holding `compare S t l r` (`isSet`s) | 5 |
| `TypedValue.ExtractItems` | typed/typed.go:205 | not on the scope's path (VTA over-approximation); spec omitted | 2 |
| `TypedValue.Merge` | typed/typed.go:143 | `isTV`s → `isTV r sc S t (merge S t l r)` (conforms) | 1 |
| `TypedValue.RemoveItems` | typed/typed.go:199 | `isTV p` ∗ `isSet R` → `isTV r (removeItems S t x R)` (conforms) | 1 |
| `TypedValue.Schema` | typed/typed.go:100 | its schema pointer | 0 |
| `TypedValue.ToFieldSet` | typed/typed.go:122 | `isTV` → `isSet r (fieldSet S t x)` | 3 |
| `TypedValue.TypeRef` | typed/typed.go:90 | its TypeRef (`isTypeRef`) | 0 |
| `TypedValue.Validate` | typed/typed.go:105 | nil ↔ `conforms S t x` | 3 |
| `TypedValue.toFieldSetWalker` | typed/tofieldset.go:31 | a walker from the pool, initialised | 1 |
| `TypedValue.walker` | typed/validate.go:31 | a validating walker from the pool | 1 |
| `ValidationError.Error` | typed/helpers.go:36 | some string | 0 |
| `ValidationErrors.Error` | typed/helpers.go:48 | some string | 1 |
| `ValidationErrors.WithLazyPrefix` | typed/helpers.go:79 | same length/nil-ness | 2 |
| `ValidationErrors.WithPrefix` | typed/helpers.go:69 | same length | 0 |
| `compareWalker.compare` | typed/compare.go:107 | internal, mirrors code: adds `cmpF n S t p l r` to `w.comparison`'s three sets; errors none on conforming inputs | 7 |
| `compareWalker.compareListItem` | typed/compare.go:370 | internal, mirrors code: adds `cmpF n S t p l r` to `w.comparison`'s three sets; errors none on conforming inputs | 3 |
| `compareWalker.derefList` | typed/compare.go:379 | as `listValue`/`mapValue`, nil for a nil side | 2 |
| `compareWalker.derefMap` | typed/compare.go:205 | as `listValue`/`mapValue`, nil for a nil side | 2 |
| `compareWalker.doLeaf` | typed/compare.go:144 | internal, mirrors code: adds `cmpF n S t p l r` to `w.comparison`'s three sets; errors none on conforming inputs | 2 |
| `compareWalker.doList` | typed/compare.go:390 | internal, mirrors code: adds `cmpF n S t p l r` to `w.comparison`'s three sets; errors none on conforming inputs | 5 |
| `compareWalker.doMap` | typed/compare.go:444 | internal, mirrors code: adds `cmpF n S t p l r` to `w.comparison`'s three sets; errors none on conforming inputs | 6 |
| `compareWalker.doScalar` | typed/compare.go:164 | internal, mirrors code: adds `cmpF n S t p l r` to `w.comparison`'s three sets; errors none on conforming inputs | 2 |
| `compareWalker.finishDescent` | typed/compare.go:198 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `compareWalker.prepareDescent` | typed/compare.go:178 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `compareWalker.visitListItems` | typed/compare.go:216 | internal, mirrors code: adds `cmpF n S t p l r` to `w.comparison`'s three sets; errors none on conforming inputs | 10 |
| `compareWalker.visitMapItem` | typed/compare.go:419 | internal, mirrors code: adds `cmpF n S t p l r` to `w.comparison`'s three sets; errors none on conforming inputs | 4 |
| `compareWalker.visitMapItems` | typed/compare.go:433 | internal, mirrors code: adds `cmpF n S t p l r` to `w.comparison`'s three sets; errors none on conforming inputs | 2 |
| `mergingWalker.derefList` | typed/merge.go:329 | as `listValue`/`mapValue`, nil for a nil side | 2 |
| `mergingWalker.derefMap` | typed/merge.go:157 | as `listValue`/`mapValue`, nil for a nil side | 2 |
| `mergingWalker.doLeaf` | typed/merge.go:104 | internal, mirrors code: sets `w.out` to `mergeF n S t l r` (none ↦ nil); errors none on conforming inputs | 0 |
| `mergingWalker.doList` | typed/merge.go:340 | internal, mirrors code: sets `w.out` to `mergeF n S t l r` (none ↦ nil); errors none on conforming inputs | 5 |
| `mergingWalker.doMap` | typed/merge.go:401 | internal, mirrors code: sets `w.out` to `mergeF n S t l r` (none ↦ nil); errors none on conforming inputs | 6 |
| `mergingWalker.doScalar` | typed/merge.go:116 | internal, mirrors code: sets `w.out` to `mergeF n S t l r` (none ↦ nil); errors none on conforming inputs | 2 |
| `mergingWalker.finishDescent` | typed/merge.go:150 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `mergingWalker.indexListPathElements` | typed/merge.go:285 | internal, mirrors code: sets `w.out` to `mergeF n S t l r` (none ↦ nil); errors none on conforming inputs | 9 |
| `mergingWalker.merge` | typed/merge.go:71 | internal, mirrors code: sets `w.out` to `mergeF n S t l r` (none ↦ nil); errors none on conforming inputs | 6 |
| `mergingWalker.mergeListItem` | typed/merge.go:317 | internal, mirrors code: sets `w.out` to `mergeF n S t l r` (none ↦ nil); errors none on conforming inputs | 3 |
| `mergingWalker.prepareDescent` | typed/merge.go:130 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `mergingWalker.visitListItems` | typed/merge.go:168 | internal, mirrors code: sets `w.out` to `mergeF n S t l r` (none ↦ nil); errors none on conforming inputs | 9 |
| `mergingWalker.visitMapItem` | typed/merge.go:369 | internal, mirrors code: sets `w.out` to `mergeF n S t l r` (none ↦ nil); errors none on conforming inputs | 4 |
| `mergingWalker.visitMapItems` | typed/merge.go:386 | internal, mirrors code: sets `w.out` to `mergeF n S t l r` (none ↦ nil); errors none on conforming inputs | 2 |
| `reconcileWithSchemaWalker.doList` | typed/reconcile_schema.go:182 | internal, mirrors code: accumulates `toRemove`/`toAdd`: the `atomicWithChildren` nodes below `path` | 2 |
| `reconcileWithSchemaWalker.doMap` | typed/reconcile_schema.go:224 | internal, mirrors code: accumulates `toRemove`/`toAdd`: the `atomicWithChildren` nodes below `path` | 4 |
| `reconcileWithSchemaWalker.doScalar` | typed/reconcile_schema.go:157 | internal, mirrors code: accumulates `toRemove`/`toAdd`: the `atomicWithChildren` nodes below `path` | 0 |
| `reconcileWithSchemaWalker.finishDescent` | typed/reconcile_schema.go:78 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 1 |
| `reconcileWithSchemaWalker.finished` | typed/reconcile_schema.go:31 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `reconcileWithSchemaWalker.prepareDescent` | typed/reconcile_schema.go:60 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `reconcileWithSchemaWalker.reconcile` | typed/reconcile_schema.go:148 | internal, mirrors code: accumulates `toRemove`/`toAdd`: the `atomicWithChildren` nodes below `path` | 3 |
| `reconcileWithSchemaWalker.visitListItems` | typed/reconcile_schema.go:161 | internal, mirrors code: accumulates `toRemove`/`toAdd`: the `atomicWithChildren` nodes below `path` | 7 |
| `reconcileWithSchemaWalker.visitMapItems` | typed/reconcile_schema.go:200 | internal, mirrors code: accumulates `toRemove`/`toAdd`: the `atomicWithChildren` nodes below `path` | 8 |
| `removingWalker.doList` | typed/remove.go:53 | internal, mirrors code: sets `w.out` to `removeAt S t R x` | 16 |
| `removingWalker.doMap` | typed/remove.go:112 | internal, mirrors code: sets `w.out` to `removeAt S t R x` | 13 |
| `removingWalker.doScalar` | typed/remove.go:48 | internal, mirrors code: sets `w.out` to `removeAt S t R x` | 1 |
| `toFieldSetWalker.doList` | typed/tofieldset.go:132 | internal, mirrors code: adds `fieldsAt S t path x` to `w.set` | 4 |
| `toFieldSetWalker.doMap` | typed/tofieldset.go:173 | internal, mirrors code: adds `fieldsAt S t path x` to `w.set` | 4 |
| `toFieldSetWalker.doScalar` | typed/tofieldset.go:90 | internal, mirrors code: adds `fieldsAt S t path x` to `w.set` | 1 |
| `toFieldSetWalker.finishDescent` | typed/tofieldset.go:79 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `toFieldSetWalker.finished` | typed/tofieldset.go:41 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `toFieldSetWalker.prepareDescent` | typed/tofieldset.go:62 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `toFieldSetWalker.toFieldSet` | typed/tofieldset.go:86 | internal, mirrors code: adds `fieldsAt S t path x` to `w.set` | 1 |
| `toFieldSetWalker.visitListItems` | typed/tofieldset.go:96 | internal, mirrors code: adds `fieldsAt S t path x` to `w.set` | 10 |
| `toFieldSetWalker.visitMapItems` | typed/tofieldset.go:151 | internal, mirrors code: adds `fieldsAt S t path x` to `w.set` | 12 |
| `validatingObjectWalker.doList` | typed/validate.go:157 | internal, mirrors code: no error ↔ `conforms S t x` | 4 |
| `validatingObjectWalker.doMap` | typed/validate.go:193 | internal, mirrors code: no error ↔ `conforms S t x` | 4 |
| `validatingObjectWalker.doScalar` | typed/validate.go:119 | internal, mirrors code: no error ↔ `conforms S t x` | 1 |
| `validatingObjectWalker.finishDescent` | typed/validate.go:78 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `validatingObjectWalker.finished` | typed/validate.go:43 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `validatingObjectWalker.prepareDescent` | typed/validate.go:62 | internal: walker pool / spare-walker bookkeeping (exclusive walker resources) | 0 |
| `validatingObjectWalker.validate` | typed/validate.go:84 | internal, mirrors code: no error ↔ `conforms S t x` | 2 |
| `validatingObjectWalker.visitListItems` | typed/validate.go:126 | internal, mirrors code: no error ↔ `conforms S t x` | 12 |
| `validatingObjectWalker.visitMapItems` | typed/validate.go:173 | internal, mirrors code: no error ↔ `conforms S t x` | 9 |

#### `value` (71)

| function | where | intended spec (abstract vocabulary) | callees |
|---|---|---|---|
| `BoolCompare` | value/scalar.go:43 | `boolCompare` | 0 |
| `Compare` | value/value.go:232 | `isVal`s → `UVal.compare x y` (the order of `PE.compare`) | 1 |
| `CompareUsing` | value/value.go:240 | as `Compare`, any allocator | 19 |
| `Equals` | value/value.go:105 | API. `isVal a x ∗ isVal b y` → `r ↔ x = y` | 1 |
| `EqualsUsing` | value/value.go:110 | `isValF a dq1 x ∗ isValF b dq2 y` (any allocator), both back → `r ↔ x = y` (no floats: the float branch is dead) | 18 |
| `FloatCompare` | value/scalar.go:21 | unreachable in scope (no floats); trivial spec (pure Go float compare) | 0 |
| `IntCompare` | value/scalar.go:32 | `intCompare` | 0 |
| `ListCompareUsing` | value/list.go:111 | lexicographic `UVal.compareF` on items | 7 |
| `ListEqualsUsing` | value/list.go:78 | two lists of `isVal`-items → `r ↔ xs = ys` | 9 |
| `MapCompareUsing` | value/map.go:210 | `UVal.compareF` map case | 4 |
| `MapEqualsUsing` | value/map.go:254 | two `isIface` maps → `r ↔ kvs = kvs'` (canonical) | 1 |
| `MapZipUsing` | value/map.go:88 | calls `fn(k, l?, r?)` over the union of keys (order per `MapTraverseOrder`); internal: a fold over `zipLexical` / any order | 6 |
| `NewFreelistAllocator` | value/allocator.go:92 | a fresh allocator predicate (`isAllocator a`) | 0 |
| `NewValueInterface` | value/valueunstructured.go:27 | API. `isIface i x` → `isVal v x` | 2 |
| `ToString` | value/value.go:191 | error strings only: returns some string (no content claim) | 17 |
| `defaultMapZip` | value/map.go:102 | internal: as `MapZipUsing` (any key order) | 2 |
| `lexicalKeyOrderedMapZip` | value/map.go:144 | internal: `zipLexical` | 15 |
| `unorderedMapZip` | value/map.go:113 | internal: as `MapZipUsing`, unordered | 15 |
| `FieldList.Compare` | value/fields.go:177 | `flCompare` | 1 |
| `FieldList.Equals` | value/fields.go:204 | `r ↔ fl = fl'` | 1 |
| `FieldList.Sort` | value/fields.go:155 | `flSort` (distinct names; over `sort.SliceStable`'s axiom) | 0 |
| `emptyRange.Item` | value/list.go:66 | unreachable (Next is false) | 0 |
| `emptyRange.Next` | value/list.go:62 | returns false | 0 |
| `freelistAllocator.Free` | value/allocator.go:154 | gives back an allocated wrapper (resource bookkeeping) | 0 |
| `freelistAllocator.allocListUnstructuredRange` | value/allocator.go:195 | a fresh range object | 0 |
| `freelistAllocator.allocValueUnstructured` | value/allocator.go:191 | a fresh `*valueUnstructured` | 0 |
| `heapAllocator.Free` | value/allocator.go:79 | no-op | 0 |
| `heapAllocator.allocListUnstructuredRange` | value/allocator.go:55 | a fresh range | 0 |
| `heapAllocator.allocValueUnstructured` | value/allocator.go:51 | a fresh `*valueUnstructured` | 0 |
| `listUnstructured.At` | value/listunstructured.go:25 | `isIface` list → item i as `isVal` | 1 |
| `listUnstructured.AtUsing` | value/listunstructured.go:29 | as `At` | 2 |
| `listUnstructured.EqualsUsing` | value/listunstructured.go:37 | as `ListEqualsUsing` | 1 |
| `listUnstructured.Length` | value/listunstructured.go:21 | `vs.length` | 0 |
| `listUnstructured.RangeUsing` | value/listunstructured.go:45 | a range over the items | 2 |
| `listUnstructuredRange.Item` | value/listunstructured.go:66 | current (index, item) | 1 |
| `listUnstructuredRange.Next` | value/listunstructured.go:61 | advances; false at the end | 0 |
| `mapUnstructuredInterface.Empty` | value/mapunstructured.go:72 | unreachable in scope (`map[interface{}]interface{}` excluded by `isIface`); spec `False` pre or omitted | 0 |
| `mapUnstructuredInterface.EqualsUsing` | value/mapunstructured.go:80 | unreachable in scope (`map[interface{}]interface{}` excluded by `isIface`); spec `False` pre or omitted | 10 |
| `mapUnstructuredInterface.Get` | value/mapunstructured.go:25 | unreachable in scope (`map[interface{}]interface{}` excluded by `isIface`); spec `False` pre or omitted | 1 |
| `mapUnstructuredInterface.GetUsing` | value/mapunstructured.go:29 | unreachable in scope (`map[interface{}]interface{}` excluded by `isIface`); spec `False` pre or omitted | 3 |
| `mapUnstructuredInterface.Has` | value/mapunstructured.go:37 | unreachable in scope (`map[interface{}]interface{}` excluded by `isIface`); spec `False` pre or omitted | 0 |
| `mapUnstructuredInterface.Iterate` | value/mapunstructured.go:46 | unreachable in scope (`map[interface{}]interface{}` excluded by `isIface`); spec `False` pre or omitted | 1 |
| `mapUnstructuredInterface.IterateUsing` | value/mapunstructured.go:50 | unreachable in scope (`map[interface{}]interface{}` excluded by `isIface`); spec `False` pre or omitted | 13 |
| `mapUnstructuredInterface.Length` | value/mapunstructured.go:68 | unreachable in scope (`map[interface{}]interface{}` excluded by `isIface`); spec `False` pre or omitted | 0 |
| `mapUnstructuredInterface.ZipUsing` | value/mapunstructured.go:104 | unreachable in scope (`map[interface{}]interface{}` excluded by `isIface`); spec `False` pre or omitted | 1 |
| `mapUnstructuredString.Empty` | value/mapunstructured.go:188 | `kvs = []` | 0 |
| `mapUnstructuredString.EqualsUsing` | value/mapunstructured.go:160 | `r ↔ kvs = kvs'` | 10 |
| `mapUnstructuredString.Get` | value/mapunstructured.go:114 | `lookupKV k kvs` as `isVal` | 1 |
| `mapUnstructuredString.GetUsing` | value/mapunstructured.go:117 | as `Get` | 3 |
| `mapUnstructuredString.Has` | value/mapunstructured.go:125 | `(lookupKV k kvs).isSome` | 0 |
| `mapUnstructuredString.Iterate` | value/mapunstructured.go:134 | calls `fn` on each entry (any order) until false | 1 |
| `mapUnstructuredString.IterateUsing` | value/mapunstructured.go:138 | as `Iterate` | 13 |
| `mapUnstructuredString.Length` | value/mapunstructured.go:152 | `kvs.length` | 0 |
| `mapUnstructuredString.ZipUsing` | value/mapunstructured.go:184 | as `MapZipUsing` | 1 |
| `valueUnstructured.AsBool` | value/valueunstructured.go:168 | the bool of a `.boo` value | 0 |
| `valueUnstructured.AsFloat` | value/valueunstructured.go:95 | unreachable in scope (no floats) | 0 |
| `valueUnstructured.AsInt` | value/valueunstructured.go:127 | the int of a `.int` value | 0 |
| `valueUnstructured.AsList` | value/valueunstructured.go:76 | a `listUnstructured` view of a `.list` (`isList l vs`) | 1 |
| `valueUnstructured.AsListUsing` | value/valueunstructured.go:80 | as `AsList` | 0 |
| `valueUnstructured.AsMap` | value/valueunstructured.go:51 | a `mapUnstructuredString` view of a `.map` (`isMapV m kvs`) | 1 |
| `valueUnstructured.AsMapUsing` | value/valueunstructured.go:55 | as `AsMap` | 0 |
| `valueUnstructured.AsString` | value/valueunstructured.go:156 | the string of a `.str` value | 0 |
| `valueUnstructured.IsBool` | value/valueunstructured.go:160 | `r ↔ x is a bool` (`isIface`; Float: always false in scope) | 0 |
| `valueUnstructured.IsFloat` | value/valueunstructured.go:84 | `r ↔ x is a float` (`isIface`; Float: always false in scope) | 0 |
| `valueUnstructured.IsInt` | value/valueunstructured.go:102 | `r ↔ x is a int` (`isIface`; Float: always false in scope) | 0 |
| `valueUnstructured.IsList` | value/valueunstructured.go:68 | `r ↔ x is a list` (`isIface`; Float: always false in scope) | 0 |
| `valueUnstructured.IsMap` | value/valueunstructured.go:41 | `r ↔ x is a map` (`isIface`; Float: always false in scope) | 0 |
| `valueUnstructured.IsNull` | value/valueunstructured.go:172 | `r ↔ x is a null` (`isIface`; Float: always false in scope) | 0 |
| `valueUnstructured.IsString` | value/valueunstructured.go:148 | `r ↔ x is a string` (`isIface`; Float: always false in scope) | 0 |
| `valueUnstructured.Unstructured` | value/valueunstructured.go:176 | its interface (`isIface i x`) | 0 |
| `valueUnstructured.reuse` | value/valueunstructured.go:36 | `isValF v (DFrac.own 1) _` → `isValF v (DFrac.own 1) x` (sets the wrapped interface) | 0 |


## Sanity checks

### The driver's nine steps, proved by `decide` (round 1)

`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/smd/Steps.lean` states each step's outcome on
the driver's literals and proves it by `decide +kernel` (no `native_decide`; axioms `propext`,
`Quot.sound`, `Classical.choice` from the decidable-equality instances' proofs): `step1` …
`step9` (`step7a`, `step7b`: ten calls, nine checks plus the conflict check of step 4) give
`applyResult … = .ok (some obj_i) mf_i` (step 3: `.ok none mf3`; step 4: `.conflicts {(A,
[replicas])}`) and `updateResult … = mf8`; and the specs' premises at each step: `sc0_wf`,
`conforms_all` (every object the driver types), `kwi_all` (every managed set before an `Apply`,
by `keysWithItemsB`). The whole file checks in about 6 s (`lake env lean`, 3 s of it loading the
imports); the reviewer's Go transcription of the definitions (`driver_test.go`) gives the same
results as Go. The derivation by hand below is kept as the explanation.

### The driver's nine steps from the specs (informal derivation)

Paths: `n i r` the root's `name image replicas`, `c` containers, `c[k]` the item named `k`,
`c[k].f` its field, `L.k` a label, `s` the selector. `S_A1 = {n,i,r,L.app,s,c[a1],c[a1].name,
c[a1].image}`. Every literal conforms to `rootRef` (strings, `int64`, items with a `name`); every
managed set is schema-consistent (nothing below the atomic `s`), so `reconcileMF` is the identity
(`reconcile_id`), and keeps items with their names (`keysWithItems`).

1. **A applies cfg1** on `{}`: `merge {} cfg1 = cfg1` (each key one side; `mergeKeys [] [a1] =
   [a1]`); `fieldSet cfg1 = S_A1` (labels' keys are undeclared: entries; `s` atomic: one path);
   no last set: `new = cfg1`; `compare` adds everything, no other manager: `ok (some cfg1) {A ↦
   applied S_A1}` = the check. ✓
2. **B applies {labels:{team:t}}**: `merge` adds `team`; `fieldSet = {L.team}` (labels is a
   declared non-empty field: no entry path); B had no entry: no pruning; `compare`: added
   `{L.team}`; `S_A1 ∩ {L.team} = ∅`: `ok`, A unchanged, B `{L.team}`. ✓
3. **B applies {image:img1, labels:{team:t}}**: merged = live; last `{L.team}`, `ens = {L, L.team}`;
   pass 1 drops `labels`, pass 2 adds back everything (owned: `L` via `ens`, `L.app` by A, `L.team`
   by B), pass 3 removes nothing: `new = live`; `compare` empty; not `rion` and `new = live`:
   `ok none {A ↦ S_A1, B ↦ {i, L.team}}`; `apply` returns `false`. ✓
4. **B applies replicas 2, not forced**: pruning keeps everything (B's `i`, `L.team` still applied);
   `compare`: modified `{r}`; `conflictsOf`: A `S_A1 ∩ {r} = {r}`, others empty: `conflicts`; the
   post's list `l` is `Nodup` with `(m,p) ∈ l ↔ m = A ∧ p = [r]`, so `l = [(A, field replicas)]`;
   `err.(merge.Conflicts)` succeeds, `Conflicts.Equals` gives `true`; the state is unchanged. ✓
5. **The same, forced**: `ok (some live[r:=2])`, A `S_A1 \ {r}`, B `{i, r, L.team}`. ✓
6. **A applies {name, containers [a1 x], selector}**: merged = live; last `S_A5`, `ens` adds `L`,
   `c`; pass 1 leaves `{replicas: 2}`; pass 2's removal set is `Fm \ (Fp0 ∪ ens M) = {L.app}` (B owns
   `i`, `r`, `L.team`; A's new set `n`, `s`, the item); pass 3 removes `{L.app}`; `new` = live with
   `labels {team}`; `compare`: removed `{L.app}`; B keeps its set; A `{n, s, c[a1]…}`. ✓
7. **B applies containers [b1 y]**: `mergeKeys [a1] [b1] = [a1, b1]`; pruning of B's last
   (`i, r, L.team`) adds all back; added `c[b1]…`, no conflict; B `+ containerPaths b1`. ✓
   **A applies containers [a2 z]**: `mergeKeys [a1, b1] [a2] = [a1, b1, a2]` (`a1`, `b1` not in the
   configuration stay where they are); pass 1 drops `name`, `selector`, `containers`; pass 2's
   removal set is `{c[a1], c[a1].name, c[a1].image}` (no one else owns them); pass 3 the same:
   `containers [b1 y, a2 z]` — the driver's order ✓; `compare`: removed `a1`'s, added `a2`'s; B
   keeps `b1`'s; A `{n, s, c[a2]…}`. ✓
8. **C updates** replicas 3 and `labels.env`: `compare`: modified `{r}`, added `{L.env}`; B loses
   `r` (`conflictsOf`, forced); C had nothing: `s = {r, L.env}`, not applied; `Update` returns
   `newObject` itself. ✓
9. **A applies selector {k: v2}** (atomic): `merge`: the selector replaced whole; `mergeKeys [b1,
   a2] [a2] = [b1, a2]` (shared `a2` matched in order); pruning adds all back (A's new set equals
   its last; C's set counts as owned too); `compare`: modified `{s}` (atomic: one path); no other
   manager owns `s`: `ok`, managers unchanged. ✓

`state.check`'s `value.Equals` and `ManagedFields.Equals` posts are `↔ =`, so each check reduces
to an equality of `UVal`s (canonical maps) and of `MF`s (`funext`, set extensionality on
`PathSet.ofList`).

### Against Go (throwaway tests outside the repository)

`smd_check_test.go` (a scratch module against v7.0.0 with the driver's schema; recorded in the
candidate file), all passing:
- `TestMergeOrder`: SMD's `Merge` order of keyed list items equals the Go transcription of
  `mergeKeys`/`mergeOrderF` on 20000 random pairs of key lists over six keys;
- `TestKeylessItemError`: the `keysWithItems` counterexample errors (not a conflict); either half
  alone does not;
- `TestRandomSequences`: 3000 random sequences of 8 applies (forced or not) and updates by three
  managers on random objects: every `Apply` error is a `Conflicts`, `Update` never fails, every
  result validates, every managed set has `keysWithItems`;
- `TestRemoveItemsEmptied` (an emptied granular map becomes `null`, its key kept; a removed root
  becomes `null`; an empty root `{}` becomes `null`), `TestCompareNode` (a granular map added is
  itself in `added`), `TestUpdateVersions` (versions do not change `Update`'s sets),
  `TestAsTypedRejects` (duplicates, undeclared fields, `null` items, keyless items, wrong scalar
  kinds, non-scalar keys rejected; `null` fields and `null` key values accepted).

Round 1's reviewers checked the definitions against Go through a hand transcription
(`review-go/lean_test.go`, `diff_test.go`): on SMD-computed managed fields (10 000 random 6-step
sequences, about 60 000 steps) and on crafted sets meeting the three-clause premise (10 000), the
object (list order, `null` versus absent), `nil` on a no-op, the managed fields and the conflict
sets matched exactly; 50 000 random updates matched `updateResult`. Now that the definitions are
computable, the Test step can evaluate them in Lean directly (`decide`, or `#eval`).

## Decisions for the user

Each in plain terms first (PRINCIPLES, "Explain a finding in plain terms before asking for a
decision").

- **D1. How `Apply`'s result is described.** SMD decides what to delete from an object by running
  three passes over it (delete what the manager applied last time, put back what any manager owns,
  put back what the manager never applied). The spec says exactly that, in terms of SMD's public
  operations on values and field sets, rather than a one-line rule such as "a field goes when its
  last applier drops it and nobody else owns it", because that rule is false of SMD: SSA-03, and the
  case found in round 1 where re-applying `spec: {}` deletes `spec` (G3). Cost: the statement is
  longer and a client reasons about it by computing (which `decide` now does on literals).
  Alternative: the one-line rule as the spec, which would be unsound. Recommended: keep.
- **D2. What `Apply` requires of the managed fields it is given** (a premise on a spec with a
  client, the driver; changed in round 1). Old: an item's key field never without the item, and a
  granular item never without its key fields. New, added: **no field path goes below a list item's
  key field** (`containers[name=a].name.x`). Why: with such a path SMD's pruning strips the key off
  an item it keeps; then `Apply` returns an error that is not a conflict, or a conflict that is not
  real, or, forced, an object with two items under one key and no error. Every set SMD itself
  computes meets the new premise, and `Apply`/`Update` preserve it, so a caller that only feeds back
  SMD's outputs (the driver, the API server for its own writes) discharges it by a law; a set a
  client wrote by hand (Kubernetes accepts client-written `managedFields`) may not, and SMD offers no
  check. Alternatives: (a) the reviewer's weaker form ("an item keeps its key field also when only a
  path below the key field is there"): also excludes every failure found, but `Update` does not
  preserve it, so chaining breaks; (b) no premise, and an error outcome in the spec (Kubernetes
  handles every error `Apply` returns): the abstract functions would then have to model SMD's
  invalid keys and duplicate items, and the forced case returns a non-conforming object, so `isTV`
  could not be the post. Recommended: the new premise (the third clause).
- **D3. The scope restrictions marked (R)**, in particular what keeps Kubernetes' own caller
  (`apimachinery/.../managedfields/internal/structuredmerge.go`) outside the specs. The reviewer
  found it fails six premises; what widening each would cost:
  1. *Its converter is not the identity* (it round-trips through the API's conversion even at one
     version). Cost: small for a converter that returns a typed value with the same value, schema
     and type (a generalized `isIdentityConverter`); a real conversion between versions is a
     different spec (values change), large.
  2. *It sets `IgnoreFilter`* (reset fields of status subresources). Cost: moderate: the applier's
     new set and `Update`'s set become `filter(set)`, with `Filter` an abstract function on sets;
     an empty or missing entry is already the same as nil.
  3. *Managers at several API versions* are normal in stored managed fields. Cost: large, and the
     premise is required by SMD's behavior, not by convenience (G2): the spec would need a
     per-version `prune` with Go's map order as nondeterminism, or the issue fixed upstream.
  4. *It types objects with `AllowDuplicates`*. Cost: moderate: a second conformance (`conforms`
     without the no-duplicate-keys check) and a variant of `isTV`; `merge`/`compare` on lists with
     duplicate keys follow SMD's handling of duplicates, to be specified.
  5. *Its values are reflection-backed* (`FromStructured`) or unstructured with `float64`. Cost:
     large: the reflection value implementation is a second representation of every value
     operation (about 60 more functions), and floats break `value.Equals = =` (SSA-05).
  6. *Its schemas* use inlined types, element-relationship overrides, sets (`listType=set`), key
     defaults and `__untyped_deduced_`. Cost: large: a non-flat `Schema` (atoms inside atoms),
     `Resolve`'s lock and cache owned, `PE.value` paths, defaults in `keyOf`.
  Plus, not a premise yet: recursion depth (a value deeper than Go's stack allows makes Go fail
  where the proved post says it returns); adding a depth premise costs every caller a depth fact.
  Recommended: keep the scope for the driver now; the cheapest steps toward Kubernetes are (1) and
  (4).
- **D4. `isSchema` persistent** (sync.Once-guarded lazy indexes) instead of the old exclusive
  `ownSchema`: concurrent readers covered; costs the `isSchema_intro` ghost update once per schema
  literal. `BuildUpdater` gives a persistent `isUpdater` (the updater's deprecated public fields can
  no longer be written by a client after it); a literal `Updater` gets one by `isUpdater_intro`.
- **D5. Proofs reset**: the driver's helper proofs (proved over the old vocabulary, `newSchema` 280
  lines) and the partial `Main` are `sorry`; of SMD's, `FieldNameElement` and the value-receiver
  `AsValue` keep their proofs; `NewVersionedSet` (proved before) now has an abstract post
  (`isVSet`), its proof `sorry`.
- **D6. Sets and managed fields as computable data** (round 1, P1). A set of paths is now a finite
  set (a list, order and repetitions forgotten), so two sets with the same paths are equal and a
  machine can check it; managed fields are a list sorted by manager name. This is what lets the
  driver's nine expected results be checked by evaluation instead of by hand. Cost: `MF`'s "equal
  as lists" means "equal" only for sorted lists, which every value the specs produce and `isMF`
  admits is (`MF_ext`); the specs read `mf.get m` instead of `mf m`. Alternative: keep sets as
  predicates (`Path → Prop`), and prove each driver step by rewriting by hand (the plan's former
  "costliest part"). Recommended: keep.
- **D7. A typed value carries its schema** (round 1, P2): `isTV` now includes `isSchema sc S` and
  `S.WF`, so `Apply`/`Update` (and the ~90 typed specs to come) lose two premises each. Cost: none
  found; `isTV_schema` gives the schema back to a caller that needs it.
- **D8. Stronger value specs** (round 1, F1): `NewValueInterface` returns the whole fresh wrapper
  (`isValF v (DFrac.own 1) x`, persisted by `isValF_persist`) and `value.Equals` takes any shares
  of its two wrappers and gives them back; both old specs are instances. Cost: a client holding the
  result of `NewValueInterface` persists it once (one law) before passing it on.
- **No new axiom.** The trust base gains no `sorry` in round 1 (the same 27, listed in
  `etc/tcb-collections/smd.txt` and `etc/tcb-baseline.txt`; `--check --update` needs the whole
  repository built). `Steps.lean` and the definitions use no `sorry`; the laws are statements
  (`def … .law : Prop`). The stdlib axioms SMD's proofs will use are the existing four
  (`reflect.DeepEqual(nil, nil)`, `slices.BinarySearchFunc`, `slices.Insert`, `sort.SliceStable`),
  plus `fmt`'s for `AsTyped`'s error branch (P8).

## Round 1's repairs (2026-11-19)

| Finding | What changed |
|---|---|
| merge F1 (unsound: `keysWithItems`) | third clause (no path below a key field); `applyResult_premise`/`updateResult_premise` over it; `state.apply`'s premise; `keysWithItemsB` + `keysWithItemsB_iff`; the nonissue corrected and widened (G1) |
| merge F2 (one version "very likely the same") | justification: required (G2, `issues/smd-apply-multiversion-prunes-owned.md`) |
| merge F3 (`prune` prose) | header rewritten with the G3 counterexample (`issues/smd-apply-deletes-own-struct.md`) |
| merge F4 (laws) | `isUpdater_persistent`, `isUpdater_intro`, chaining laws restated |
| merge F5 (`isUpdater … nil nil`) | `IgnoredFields` nil documented as required (G4, `issues/smd-ignoredfields-missing-version-panic.md`); `IgnoreFilter` kept nil (an empty map is the same; the simpler statement), said so |
| merge F6 / D3 | the six costs above |
| vocab F1 (lent wrappers) | `isValF v dq x`, `isVal` its instance; `isValF_split`/`_persist`/`_agree`; `value.Equals` over fractions; `NewValueInterface` gives the whole wrapper |
| vocab F2 (sets under construction) | `ownSet`, `ownSet_persist`, `ownSet_empty` |
| vocab F3 (missing laws) | persistence of `isFieldList`, `isPaths`, `isUpdater`; intro laws for `isFieldList`, `isPath`, `isPaths` (nil, cons, append, length), the schema literal (`isTypeRef_intro`, `freshAtom_*`, `freshSchema_intro`), `isUpdater_intro`, `isIface_ofMap`, `isMF_intro` over `MF.ofList` |
| vocab P1 (not computable) | `UVal.decEq`; `FSet`/`PathSet`; sorted `MF`; `conformsB`, `Schema.WF`, `keysWithItemsB`, `atomicNodes`, computed `ensureNamed`/`reconcile`; no classical branching, no well-founded recursion; hand-written `DecidableEq` for `VSet`, `Cmp`, `ApplyOutcome`; the nine steps by `decide` (`Steps.lean`) |
| vocab P2 | `isTV` carries `isSchema`, `S.WF`; `isTV_schema` |
| vocab P3 | every representation predicate and internal sealed (`@[no_expose]`); `etc/api/smd.txt` (no `root`: the specs' names `smd.<pkg>.<F>` do not follow the path; checked by hand that each spec/proof file exposes only its spec/proof); `interface/` generated |
| vocab P4 | `UVal.ofMap`, `kvsOf`, `MF.ofList` exported (the driver's `mkKVs`/`mkMF`/`insertKV` removed); `UVal.Canonical` dropped |
| vocab P5 | agreement laws stated |
| vocab P6 | `[merge.Assumptions]` did not enter the statements (`#check`), but each spec and proof file of `value`/`fieldpath`/`typed` now imports its own package's `Base` and declares its own `Assumptions` (a later proof of `value.Equals` would otherwise have carried `merge`'s) |
| vocab P7/P8 | nil maps and nil `ManagedFields`, nil `Unions` marked (R); recursion depth and `AsTyped`'s `fmt` reliance recorded as margins |

## Glue

None proved in this step. After the freeze, the glue (callers that only pass state between
callees): `state.apply`, `state.check`, `state.typedObj`, `applied`, `updated`, `field`, `mapKey`,
`item`, `itemField`, `containerPaths`, `Main` (whose steps' facts about `applyResult`/
`updateResult` on the scenario's values are now proved by `decide`: `Steps.lean`).

## Decisions taken (2026-11-19, the coordinator, by the user's delegation)

The user (2026-11-19): "I don't care about intermediate iris specs, I just want the robustness test
proved. Try to make decisions about internal proof details yourself instead of posing them to me."
So the decisions above, and the freeze, are the coordinator's; the target is `smd_driver_robust`
proved (`Main.wp_proof` and every SMD proof it links), with the trust base unchanged but for the four
standard-library axioms already listed.

- D1 accepted: `prune` stays SMD's three passes.
- D2 accepted: the three-clause `keysWithItems` premise (the driver meets it; proved by `decide`).
- D3: no widening. The scope is what `smd_driver_robust` needs; Kubernetes' `structuredmerge.go`
  stays out of scope (one version, identity converter, no ignore filter, no floats or reflection
  values, `Schema.WF`).
- D4, D6, D7, D8 accepted as drafted.
- D5 accepted: the driver's proofs are redone over the new vocabulary in Prove.
- Freeze: the coordinator tags `smd-stage1-frozen` once the internal drafts and review round 2's
  first-tier findings are repaired; proofs start after the tag. Later spec changes found by proofs
  are made by the coordinator without asking, recorded here.
