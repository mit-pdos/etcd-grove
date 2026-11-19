# Translating structured-merge-diff with Goose (2026-11-19)

Goal: the Goose translation of Kubernetes' structured-merge-diff (SMD, server-side apply's merge
library), with bodies for everything `merge.Updater.Apply`/`Update` and the `typed.TypedValue`
API reach, for a robustness theorem (`Robustness.Robust`: no panic, no stuck thread) about a Go
driver whose `Main` runs an apply/update scenario and panics on a violated check
(`examples/k8s/smd/`, written separately). No specs or proofs here. Perennial and the pinned
translator are unchanged.

## Setup

- Project `smd` of `etc/goose.py`: upstream `kubernetes-sigs/structured-merge-diff` at tag
  v7.0.0, commit `8d11054be605e4018886201fb2bce0651c053592` (module
  `sigs.k8s.io/structured-merge-diff/v7`; `examples/k8s/etcd3/go.mod` requires v7.0.0). No fork,
  no patch: the configuration alone cuts what does not translate.
- Packages `value`, `schema`, `fieldpath`, `typed`, `merge`; `-lean-root
  sigs.k8s.io/structured-merge-diff/v7=` (modules `Code.sigs_k8s_io.structured_merge_diff.v7.*`,
  `GeneratedProof.…`); owns `sigs_k8s_io/structured_merge_diff`; counted module
  `sigs.k8s.io/structured-merge-diff/v7`. Configuration:
  `Code/sigs_k8s_io/structured_merge_diff/v7/{value,schema,fieldpath,typed,merge}.toml`.
- The standard library is Perennial's: `fmt`, `errors`, `strings`, `sort`, `slices`, `iter`,
  `math`, `reflect`, `sync`, `sync/atomic`. `encoding/json/v2`, `encoding/json/jsontext`,
  `go.yaml.in/yaml/v2` and the module's `internal/json` are not imported (the declarations that use
  them are names only), so no new standard-library or third-party translation was needed.
- One module per package (no chunks): `Code/…/value.lean` 0.5 MB, `fieldpath` 0.5 MB, `typed`
  0.9 MB, `merge` 0.25 MB, `schema` 0.14 MB; `GeneratedProof` 0.3 MB in all.

## What has bodies

The call graph was computed with `golang.org/x/tools` (CHA, then VTA over the CHA-reachable
functions), roots `(*merge.Updater).Apply`, `Update`, `typed.AsTyped`, `AsTypedUnvalidated` and
every `TypedValue` method, with the reflection implementation (`*Reflect*`, `NewValueReflect`) and
`typed.ParseableType` cut. It reaches 311 SMD functions (closures included); **every one of them
is translated with its body**. The coordinator's Go coverage run of the driver
(`examples/k8s/smd`) agrees: everything it executed is in this table (`typed/reconcile_schema.go`,
`validate.go`, `compare.go`, `merge/conflict.go`, `value/map.go`, `list.go`, `fields.go`,
`fieldpath/pathelementmap.go`, `path.go`, `schema/equals.go`, the allocators' unstructured
cases); what it executed outside SMD's bodies is `reflect.DeepEqual`, the `sync.Pool`s and the
package initializers, below.

| Package | Reached, with bodies |
|---|---|
| `merge` | `Updater.Apply`, `Update`, `update`, `prune`, `addBackOwnedItems`, `addBackOwnedItemsForVersion`, `addBackDanglingItems`, `reconcileManagedFieldsWithSchemaChanges`, `ConflictsFromManagers` (and the rest of the package: `Conflict(s).Error/Equals/ToSet`, `UpdaterBuilder.BuildUpdater`) |
| `typed` | `AsTyped`, `AsTypedUnvalidated`, `TypedValue.{TypeRef,AsValue,Schema,Validate,ToFieldSet,Merge,Compare,RemoveItems,ExtractItems,Empty}`, `merge`, the walkers (`validatingObjectWalker`, `toFieldSetWalker`, `mergingWalker`, `compareWalker`, `removingWalker`, `reconcileWithSchemaWalker`: all methods), `ReconcileFieldSetWithSchema`, `Comparison.{ExcludeFields,FilterFields}`, `ValidationError(s)`, the helpers (`resolveSchema`, `deduceAtom`, `handleAtom`, `listValue`, `mapValue`, `keyedAssociativeListItemToPathElement`, `setItemToPathElement`, `listItemToPathElement`, `getAssociativeKeyDefault`, `typeRefAtPath`, `isUntypedDeduced*`, `validateScalar`, `errorf`); the `sync.Pool`s of walkers |
| `fieldpath` | `PathElement.{Less,Compare,Equals,String,Copy}`, `PathElementSet.*`, `Path.*`, `MakePath`, `PathElementMap`, `PathElementValueMap` (`pathelementmap.go`), `Set.*` (but `Leaves`), `SetNodeMap.*`, `NewExcludeSetFilter`, `NewIncludeMatcherFilter`, matchers, `SetFromValue`/`objectWalker`, `ManagedFields`, `VersionedSet` |
| `schema` | `Schema.{FindNamedType,Resolve,resolveNoOverrides,CopyInto}`, `Map.{FindField,CopyInto}`, every `Equals` |
| `value` | `NewValueInterface`, `valueUnstructured.*`, `mapUnstructuredString.*`, `mapUnstructuredInterface.*`, `listUnstructured.*`, `listUnstructuredRange.*`, `EmptyRange`, `Equals(Using)`, `Compare(Using)`, `Less`, `ToString`, `ListEquals/Compare(Using)`, `MapZip(Using)`, `defaultMapZip`, `unorderedMapZip`, `lexicalKeyOrderedMapZip`, `MapEquals/Compare/Less(Using)`, `FieldList.{Sort,Less,Compare,Equals,Copy}`, `FloatCompare`, `IntCompare`, `BoolCompare`, `HeapAllocator`, `NewFreelistAllocator`, `freelist[T].{allocate,free}`, both allocators' methods (the `alloc*Reflect` ones and `freelistAllocator.Free`'s reflection cases included: they only allocate and clear structs) |

## What is names only, and why

| Declarations | Why | Reached from the bodies? |
|---|---|---|
| `value`'s reflection implementation: the functions and methods of `valuereflect.go`, `structreflect.go`, `mapreflect.go`, `listreflect.go`, `reflectcache.go`, `jsontagutil.go` (their **types are translated**: the allocators allocate and clear them) (their package variables: trusted initializers, below) | Go reflection (`reflect.Value` is opaque in Perennial) | Only through `NewValueReflect`, which only `typed.ParseableType.FromStructured` (names only) calls; the `Value`/`Map`/`List` interface calls of the bodies dispatch to the reflection methods only on a value built by it. A driver that builds its values with `NewValueInterface` (or `ParseableType.FromUnstructured`) never reaches them. |
| `value.FromJSON`, `FromJSONFast`, `ToJSON`, `ToYAML`, `ValueMarshalJSONTo`, `FieldList.MarshalJSONTo`/`UnmarshalJSONFrom`, the `var _ json.MarshalerTo = …` assertions | `encoding/json/v2`, `go.yaml.in/yaml/v2`, `internal/json`: not translated | No. |
| `fieldpath`'s FieldsV1 serialization: `Set.ToJSON`, `ToJSONStream`, `FromJSON`, `SerializePathElement`, `DeserializePathElement`, `pathElementSerializer` (type axiomatized), `fastMarshalValue` (axiomatized), `setContentsV1` (axiomatized), `writePathKey`, `readIterV1`, `writeEmptyObject` (the variables `allowInvalidUTF8`, `allowDuplicates`, `pool`: trusted initializers, below) | `encoding/json/v2` | No: `merge` and `typed` keep managed fields as `fieldpath.Set`s; FieldsV1 bytes are the API server's business. |
| `fieldpath.Set.Leaves` | a labelled `continue outer` (G1 below) | No (only `SetNodeMap.Leaves`, bodied, calls it; nothing reached calls either). |
| `typed`: `create`, `createOrDie`, `NewParser`, `ParseableType.FromYAML`, `ParseableType.FromStructured` | YAML (`go.yaml.in/yaml/v2`), reflection | No. `Parser.Type`, `TypeNames`, `ParseableType.IsValid`, `FromUnstructured` have bodies. |

## Trusted: the package initializers that do not translate

Every program that imports `typed` runs `value`'s, `fieldpath`'s and `typed`'s package
initializers, so the opaque initializers of the names-only variables would be trust-boundary
axioms of any whole-program theorem (`etc/gen-init.py`'s `opaqueInitsOk`). They are `trusted`
instead, each with a no-op model and a docstring saying why it is faithful
(`TrustedCode/sigs_k8s_io/structured_merge_diff/v7/{value,fieldpath,typed}.lean`, with the empty
`ManualProof/…` modules the generated proofs import), the precedent being protobuf's
`protoreflect` type descriptors:

| Variables | Go initializer | Why a no-op is faithful |
|---|---|---|
| `value`: `nilType`, `isZeroerType`, `marshalerType`, `unmarshalerType`, `unstructuredConverterType`, `unstructuredConverterWithErrorType` | `reflect.TypeOf`/`TypeFor`: a static type descriptor | cannot panic, no visible effect; only the names-only reflection code reads them |
| `value.defaultReflectCache` | `newReflectCache()`: allocates a cache, stores an empty map in its `atomic.Value` | cannot panic; only the names-only reflection cache reads it |
| `fieldpath`: `allowInvalidUTF8`, `allowDuplicates`, `pool` | `jsontext` option constants; a `sync.Pool` literal | cannot panic; only the names-only serialization reads them |
| `value._`, `fieldpath._` | `var _ json.MarshalerTo = (*FieldList)(nil)` etc. | a discarded conversion to an interface |
| `typed`: `ssParser`, `DeducedParseableType` | `createOrDie(…)`: `yaml.Unmarshal` of a constant schema document, panicking on a parse error | the two documents are constants that parse (every importer of `typed` runs them before `main`); the stored value is unobservable: `ssParser`'s only reader is `NewParser` (names only), `DeducedParseableType` has no reader in the translated packages or the driver. **A translated reader of `DeducedParseableType` would load a zero `ParseableType`**: it would need a model that builds the deduced schema. |

`schema.SchemaSchemaYAML` (a string constant) and every other package variable (`HeapAllocator`,
`EmptyRange`, the walker pools `cmpwPool`, `mwPool`, `tPool`, `vPool`, `fmPool`,
`ruleKeepRHS`, `AssociativeListCandidateFieldNames`, `ErrUnknownPathElementType`, the
`pe*SepBytes`, `nullBytes`/`trueBytes`/`falseBytes`) are translated with their initializers.

## Standard-library functions the bodies call

Perennial's translation, names only unless said: what a proof will need specs (or Perennial
bodies) for. From the call graph (VTA, as above):

- `fmt.Sprintf`, `fmt.Errorf` (trusted models in Perennial), `errors.New`, `strings.Join`,
  `strings.Compare` (trusted), `sort.Strings` (bodied over `slices.Sort`).
- `slices.BinarySearchFunc`, `slices.Insert` (and `slices.Reverse`, `rotateLeft/Right`,
  `overlaps` under it): **names only** in Perennial (`slices.toml` translates the sorts only); every
  `PathElementSet.Insert/Has`, `PathElementMap`, `PathElementValueMap`, `SetNodeMap.Descend/Get`
  calls them. The main proof obligation outside SMD.
- `sort.SliceStable` (reflection-based swapper; names only): `value.FieldList.Sort`, which the
  key-field path elements of associative lists use.
- `reflect.DeepEqual` (names only in Perennial: reflection): `schema.StructField.Equals` compares
  `Default` (an `interface{}`) with it, reached on every merge/compare through `TypeRef.Equals` →
  `Atom.Equals` → `Map.Equals` (`typed/merge.go:88`, `compare.go:124`). Goose's `trusted` does not
  apply to methods, so `StructField.Equals` keeps its body and the call stays a call of Perennial's
  names-only `reflect.DeepEqual`: the proof needs a trust-boundary spec of `DeepEqual`, as
  `Spec/reflect/DeepEqual.lean` already has for bbolt's `pidSet` maps (an axiom,
  `Proof/reflect/DeepEqual.lean`); the driver's schemas have no defaults, so the case needed is two
  nil interfaces (Go: `DeepEqual(nil, nil)` is `x == nil || y == nil` → `x == y`, `true`;
  `reflect/deepequal.go`), and, for a schema with defaults, two scalar defaults.
- `sync.Once.Do` (bodied), `sync/atomic.Pointer[T].Load/Store` (trusted models): `schema`'s lazy
  field/type indexes (`Map.FindField`, `Schema.FindNamedType`).
- `sync.Pool.Get/Put`: `typed`'s walker pools (`cmpwPool`, `mwPool`, `tPool`, `vPool`, `fmPool`) on
  every `Compare`/`Merge`/`ToFieldSet`/`Validate`/`ReconcileFieldSetWithSchema`. **Supported by
  Perennial**: trusted models over the Go model pool `goose/model/pool` (`Perennial/TrustedCode/
  sync.lean`) with proved specs (`Perennial/Spec/sync/Pool__Get.lean`, `Proof/sync/Pool__Put.lean`;
  `Get` returns a value previously `Put` or `New()`'s). The pools' initializers (struct literals
  with a `New` closure) are translated. `sync.Mutex` (trusted).
- `math.IsInf`, `math.IsNaN` are only in `ValueMarshalJSONTo` (names only). Float comparisons and
  `float64(int64)` conversions are in `value.EqualsUsing`/`CompareUsing`/`FloatCompare`: a driver
  without float values never reaches them.

## Gaps

**G1. Labelled statements** (`[unsupported]: statement *ast.LabeledStmt`), `fieldpath/set.go:432`
in `Set.Leaves` (`outer: for … { for … { … continue outer } }`). Not on the Apply/Update path;
names only. `notes/perennial-changes.md`, "Goose: labelled `break`/`continue`".

Nothing else failed: the reflection and JSON code translated too (its bodies are cut for being
untranslatable in meaning, not by the translator).

## Not done here (done since, 2026-11-19: `notes/smd-robustness.md`)

- `etc/gen-init.py`: `smd`'s packages have no `Proof/**/Init.lean` yet; no initializer of theirs is
  opaque now (above), so none needs an `opaqueInitsOk` axiom. (Done: generated, fact `True`, no
  axiom.)
- `GO_MOD_PINS`: SMD is required at its tag (no `replace`), so there is no pseudo-version for
  `etc/goose.py` to check; the driver's `go.mod` must require `sigs.k8s.io/structured-merge-diff/v7
  v7.0.0` to be the translated code. (Done: `GO_MOD_TAG_PINS`, project `smd`'s `tag`.)
