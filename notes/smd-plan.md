# structured-merge-diff: the specs for the driver's robustness theorem (stage plan, 2026-11-19)

The spec-first plan (`notes/spec-first-plan.md`) for proving `smd_driver_robust`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/smd/TopLevelRobustness.lean`, unchanged: the
driver `examples/k8s/smd`'s `Main` never panics) over specs of structured-merge-diff v7.0.0 (SMD).
The user's instruction: "write per-function specs that are enough to prove the top-level result.
First write all the specs, informally review them, then write invariants, then write proofs."

**Where it stands: Draft, first step** (commit on `worktree-smd-robustness`): the scope, the abstract
vocabulary (written in full), the specs of every SMD function the driver calls (proofs `sorry`), the
driver's own specs restated over them (proofs `sorry`), the laws clients need (stated), the call
DAG below them with an intended spec per function, and the sanity checks. No proof was written; no
glue is listed for this step. Next: Review (fresh `spec-reviewer` rounds on this plan and the
candidate), then the per-package drafting of the DAG's specs, Test, Freeze, Prove.

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
`map[string]interface{}` (`UVal`, maps canonical: sorted keys).
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
  `reflect.DeepEqual`, whose trust-boundary spec covers two nils only).

**Objects**: `typed.AsTyped` without options (R: `AllowDuplicates` changes validation), so every
`TypedValue` the API takes conforms (`isTV` carries `conforms`); both objects of an `Apply`/
`Update` of one schema pointer and one type (else `Compare`/`merge` fail: the specs take one `sc`
and one `t`).

**The updater**: (R) an identity converter (`isIdentityConverter`), no `IgnoredFields`, no
`IgnoreFilter` (`Apply`/`Update` take `isUpdater u cv nil nil rion`). `ReturnInputOnNoop` either
way. One API version: (R) for `Apply`, every manager's entry at the request's version (with others
`addBackOwnedItems` adds back per version in map order; very likely the same result, unproved);
`Update` needs none (with an identity converter every version compares alike: Go-checked,
`TestUpdateVersions` below).

**Managed fields**: any `ManagedFields` whose sets are canonical tries (every set SMD builds is;
`isSet`), reconciled with the schema by the specs themselves (`reconcile`, the identity on sets
written at this schema), and, for `Apply`, **`keysWithItems`** on every set: a set with an item's
key field has the item, and a set with a granular item has its key fields. Every set SMD computes
has it (Go: 3000 random apply/update sequences); without it, `Apply` can fail with an error that is
not a conflict (`nonissues/smd-apply-keyless-item-compare-error.md`, Go-reproduced): the one
non-conflict error the scope would otherwise contain.

**Known SMD defects, stated faithfully, not repaired**:
- an emptied container becomes `null`; `RemoveItems` turns every empty list or map it visits into
  `null` (SSA-01/02: kubernetes#143853, #104694) — `removeAt`;
- a list item goes as a whole when its path is pruned, even if another manager owns a field in it
  (SSA-03, kubernetes#134902) — `prune`, `removeL`;
- list items' merge errors are dropped (`nonissues/smd-merge-list-item-errors-dropped.md`) —
  unreachable in scope (conforming values, lists atomic or keyed);
- SSA-04 (CRD status strategy) is the API server's; SSA-06 (FieldsV1 decoding rounds integer keys)
  is serialization, names only in the translation, out of scope.

**Outcomes**: in the scope `Apply` returns the merged object and managers, or (not forced) a
`Conflicts` error; `Update` never fails; `AsTyped` accepts exactly the conforming values. No other
error outcome is stated, and none exists in scope (Go: every `Apply` error of the random sequences
was a `Conflicts`).

## The vocabulary (written in full: `Proof/sigs_k8s_io/structured_merge_diff/v7/<pkg>/Defs.lean`)

Pure (no Iris):

| Name | Module | Meaning |
|---|---|---|
| `UVal` | value | an unstructured value; `UVal.Canonical` (maps sorted), `UVal.compare` (`value.Compare`, the order of sets' slices only) |
| `PE`, `Path`, `FieldList` | fieldpath | path elements (field, key, value, index) and paths |
| `PathSet` | fieldpath | a set of paths, `Path → Prop`; `union`/`inter`/`diff`/`IsEmpty`/`under`/`ofList`/`single` |
| `VSet`, `MF` | fieldpath | a versioned set (set, version, applied); managed fields `GoString → Option VSet` |
| `Trie`, `Trie.paths`, `Trie.Canonical` | fieldpath | the representation's trie (sorted, no empty child); clients never see it |
| `Scalar`, `ElemRel`, `TypeRef`, `Atom`, `Schema` | schema | a flat named-type schema; `Schema.find`, `fieldType`, `Schema.WF` (the scope) |
| `conforms S t x` | typed | `x` validates against `t` (`TypedValue.Validate`) |
| `keyOf ks x` | typed | an associative list item's key (its key fields, sorted by name) |
| `fieldSet S t x` | typed | `ToFieldSet`: scalars, atomic values, list items, map entries that are `null`/`{}`/undeclared |
| `removeItems S t x R` | typed | `RemoveItems`: `x` without `R`, emptied containers `null` |
| `merge S t l r`, `mergeKeys` | typed | `Merge` (`r` wins at leaves; per key; list items in `mergeKeys` order) |
| `compare S t l r : Cmp` | typed | `Compare`: removed, modified, added paths |
| `ensureNamed S t s` | typed | `EnsureNamedFieldsAreMembers`: `s` plus declared fields with paths below |
| `reconcile S t s`, `schemaConsistent` | typed | `ReconcileFieldSetWithSchema`: subtrees under atomic nodes collapsed |
| `reconcileMF`, `prune`, `afterUpdate`, `conflictsOf` | merge | the steps of SSA, over the typed operations |
| `applyResult … : ApplyOutcome` | merge | `ok obj mf'` or `conflicts cs` |
| `updateResult … : MF` | merge | the managers after `Update` |
| `keysWithItems S t s` | merge | `Apply`'s premise on each managed set |

Representation predicates (all **persistent** but `freshSchema`; SMD never writes what it was given
or returned):

| Predicate | Meaning |
|---|---|
| `isIface i x` | an `interface{}` holding `x` (read-only slices and maps, discarded fractions) |
| `isVal v x` | a `value.Value` (`*valueUnstructured`) over an interface holding `x` |
| `isFieldList s fl`, `isPE e pe`, `isPath s p`, `isPaths` | the `fieldpath` path types |
| `isSet p S` | a `*fieldpath.Set` whose trie is canonical with paths `S` |
| `isVSet i e` | a `VersionedSet` (`versionedSet`) holding `e` |
| `isMF m mf` | a non-nil `ManagedFields` map holding `mf` |
| `isTypeRef tr t` | a named `schema.TypeRef` |
| `isSchema sc S` | a `*schema.Schema` holding `S`, its lazy indexes (`FindNamedType`'s, each `FindField`'s: `sync.Once` + `atomic.Pointer`) under `sync.isOnce`: **persistent**, so concurrent readers are covered (the API server shares schemas); `freshSchema sc S` is a literal with zero indexes, made an `isSchema` by a ghost update (`isSchema_intro`) |
| `isTV p sc S t x` | a `*typed.TypedValue` of schema `sc`, type `t`, value `x`, and `conforms S t x` |
| `isUpdater u cv igf igfl rion` | a `*merge.Updater` (read-only) |
| `isIdentityConverter cv` | a `Converter` whose methods are the identity / `false` (Hoare triples on its dynamic type) |
| `isConflicts s cs` | a `merge.Conflicts` slice holding `(manager, path)` pairs |

The old `ownSchema` was exclusive (threaded through every call); `isSchema` is persistent. The old
sets were the trie itself (`PSet`, structure-equal); `PathSet` is the set, the trie canonical in the
representation, so `Set.Equals` is `=`.

**Laws** (`Proof/sigs_k8s_io/structured_merge_diff/v7/Laws.lean`, stated as `def <name>.law : Prop`,
proved after the freeze): persistence of every predicate; `isSchema_intro` (fresh → shared, a
fancy update); literal introduction for `isIface` (scalars, lists, maps), `isMF`, `isConflicts`;
`isTV_conforms`; `reconcile_id` (consistent sets are their own reconciliation);
`applyResult_premise`/`updateResult_premise` (the results keep `Apply`'s premise and are
schema-consistent: chaining); `mergeF_none` (merging nothing is the identity).

## The API specs (`Spec/sigs_k8s_io/structured_merge_diff/v7/<pkg>/<F>.lean`)

Every function the driver calls (`examples/k8s/smd/smd.go`; the translated driver's calls). Each
takes `isPkgInit` of its package.

| Function | Pre | Post |
|---|---|---|
| `value.NewValueInterface(i)` | `isIface i x` | `isVal v x` |
| `value.Equals(a, b)` | `isVal a x ∗ isVal b y` | `r = true ↔ x = y` |
| `fieldpath.FieldNameElement(n)` | — | `isPE e (.field n)` (proof kept) |
| `fieldpath.KeyElement(fields...)` | `isFieldList s fl` | `isPE e (.key fl)` |
| `fieldpath.NewSet(paths...)` | `s ↦*{dq} ss ∗ isPaths ss ps` | `isSet p (PathSet.ofList ps)` |
| `fieldpath.NewVersionedSet(set, v, b)` | `isSet p S` | `isVSet i ⟨S, v, b⟩` |
| `ManagedFields.Equals` (and `_ptr`) | `isMF m1 a ∗ isMF m2 b` | `r = true ↔ a = b` |
| `typed.AsTyped(v, sc, tr)` | `isVal v x ∗ isSchema sc S ∗ isTypeRef tr t ∗ ⌜S.WF⌝` | `conforms S t x ∧ err = nil ∗ isTV p sc S t x`, or `¬ conforms S t x ∧ p = nil ∧ err ≠ nil` |
| `TypedValue.AsValue` (value receiver) | — | its `value` field (proof kept) |
| `TypedValue.AsValue` (`_ptr`) | `isTV p sc S t x` | `isVal v x` |
| `UpdaterBuilder.BuildUpdater` | `b ↦{dq} ub` | `isUpdater u ub.Converter ub.IgnoredFields ub.IgnoreFilter ub.ReturnInputOnNoop` |
| `Updater.Apply` | below | below |
| `Updater.Update` | below | below |
| `Conflicts.Equals` (and `_ptr`) | `isConflicts s1 a ∗ isConflicts s2 b` | `r = true ↔ a = b` |

`Updater.Apply(lp, cp, ver, mfm, mgr, force)`:

    {{ isPkgInit merge ∗ isUpdater u cv nil nil rion ∗ isIdentityConverter cv ∗
       isSchema sc S ∗ isTV lp sc S t live ∗ isTV cp sc S t config ∗ isMF mfm mf ∗
       ⌜S.WF⌝ ∗ ⌜∀ m e, mf m = some e → e.version = ver ∧ keysWithItems S t e.set⌝ }}
      u.Apply(lp, cp, ver, mfm, mgr, force)
    {{ (op, mfm', err).
       match applyResult S t rion live config ver mf mgr force with
       | ok obj mf' => err = nil ∗ isMF mfm' mf' ∗ (obj = none → op = nil) ∗ (obj = some x → isTV op sc S t x)
       | conflicts cs => op = nil ∗ isMF mfm' (no managers) ∗ ∃ s l, err = Conflicts(s) ∧ l.Nodup ∧
                         (∀ m p, (m, p) ∈ l ↔ cs m p) ∗ isConflicts s l }}

    applyResult S t rion live config ver mf mgr force :=
      mf0    := reconcileMF S t mf
      merged := merge S t live config
      mf1    := mf0 with mgr ↦ ⟨fieldSet S t config, ver, applied⟩
      new    := prune S t merged mf1 (mf0 mgr)
      c      := compare S t live new
      confl  := conflictsOf mf1 mgr c          -- m ≠ mgr: mf1 m ∩ (c.modified ∪ c.added)
      if ¬force ∧ some confl m ≠ ∅ then conflicts confl
      else ok (if ¬rion ∧ new = live then none else some new) (afterUpdate mf1 mgr confl c.removed)

    prune S t merged mf last :=                 -- none or empty last: merged
      p0 := removeItems merged (ens last)                              -- what mgr applied last time
      p1 := removeItems merged (ens(fs merged) \ (ens(fs p0) ∪ ens(∪ mf)))   -- add back owned
      removeItems merged ((ens(fs merged) \ ens(fs p1)) ∩ ens last)  -- add back dangling
    (ens = ensureNamed S t, fs = fieldSet S t)

`Updater.Update(lp, np, ver, mfm, mgr)`:

    {{ isPkgInit merge ∗ isUpdater u cv nil nil rion ∗ isIdentityConverter cv ∗
       isSchema sc S ∗ isTV lp sc S t live ∗ isTV np sc S t new ∗ isMF mfm mf ∗ ⌜S.WF⌝ }}
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
SMD in places the driver does not reach but a client can (SSA-03: an item is removed even though
another manager owns a field inside it; `ensureNamed` makes a struct field with children a member,
so the first pass removes whole fields and the second adds back what is owned). The operations
composed are SMD's public `typed` and `fieldpath` API (`Merge`, `ToFieldSet`, `RemoveItems`,
`Compare`, `EnsureNamedFieldsAreMembers`, `ReconcileFieldSetWithSchema`, `Set` algebra), each
defined over values and paths, not over SMD's walkers; another implementation of the same API
(same `typed` operations) meets the spec. Decision D1 below.

**Margins** (what the code guarantees beyond the post): the conflicts' order (managers in Go's map
order, each manager's paths in the trie's preorder: stated only as "each pair once"); the error
messages; that the returned object is fresh (not the live one).

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
  `version`, `keysWithItems`⌝ `∗ ⌜applyResult sc0 rootRef false st.live (.map kvs) version st.mf mgr
  false = ok obj mf'⌝` → `RET obj.isSome; ownState s sc ⟨obj.getD st.live, mf'⟩`;
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
| `NewSet` | fieldpath/set.go:44 | API. `isPaths ss ps` → `isSet p (ofList ps)` | 1 |
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
| `Set.Insert` | fieldpath/set.go:63 | exclusive trie: `S ↦ S ∪ {p}` (only on sets under construction: `NewSet`, walkers' sets) | 2 |
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
| `EqualsUsing` | value/value.go:110 | `isVal`s (any allocator) → `r ↔ x = y` (no floats: the float branch is dead) | 18 |
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
| `valueUnstructured.reuse` | value/valueunstructured.go:36 | sets the wrapped interface | 0 |


## Sanity checks

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

Not yet checked against Go: `merge`, `compare`, `fieldSet`, `removeItems`, `ensureNamed`,
`reconcile` as functions on random inputs (the Test step: evaluating them needs computable
versions; `PathSet` is a `Prop` set).

## Decisions for the user

- **D1. `Apply`'s post as SSA's composition of the typed operations** (above), rather than a
  declarative characterization (cleaner to read, but a theorem about SMD that is false in corners:
  SSA-03). Each operation is defined declaratively over values; the list-merge order alone follows
  SMD's loop (`mergeOrderF`), there being no simpler description.
- **D2. The new premise `keysWithItems` on `Apply`'s managed fields** (a spec with a client: the
  driver; checkable, decidable on a literal; every SMD-computed set has it; without it `Apply` has a
  non-conflict error outcome, Go-reproduced). Alternative: no premise, and an `error` outcome
  defined by when `compare` meets a keyless item (the abstract functions would then have to model
  SMD's invalid path elements).
- **D3. The scope restrictions marked (R)** above, in particular one API version for `Apply`, an
  identity converter, no ignored fields, no floats, no sets, named types only.
- **D4. `isSchema` persistent** (sync.Once-guarded lazy indexes) instead of the old exclusive
  `ownSchema`: concurrent readers covered; costs the `isSchema_intro` ghost update once per schema
  literal. `BuildUpdater` gives a persistent `isUpdater` (the updater's deprecated public fields can
  no longer be written by a client after it).
- **D5. Proofs reset**: the driver's helper proofs (proved over the old vocabulary, `newSchema` 280
  lines) and the partial `Main` are `sorry`; of SMD's, `FieldNameElement` and the value-receiver
  `AsValue` keep their proofs; `NewVersionedSet` (proved before) now has an abstract post
  (`isVSet`), its proof `sorry`.
- **No new axiom.** The trust base gains only `sorry`s (27, listed in
  `etc/tcb-collections/smd.txt` and `etc/tcb-baseline.txt`, by hand: `--check --update` needs the
  whole repository built). The stdlib axioms SMD's proofs will use are the existing four
  (`reflect.DeepEqual(nil, nil)`, `slices.BinarySearchFunc`, `slices.Insert`, `sort.SliceStable`).

## Glue

None proved in this step. After the freeze, the glue (callers that only pass state between
callees): `state.apply`, `state.check`, `state.typedObj`, `applied`, `updated`, `field`, `mapKey`,
`item`, `itemField`, `containerPaths`, `Main` (whose steps need the derivation above as Lean
lemmas about `applyResult`/`updateResult` on the scenario's values: the costliest part of the
driver's proof).
