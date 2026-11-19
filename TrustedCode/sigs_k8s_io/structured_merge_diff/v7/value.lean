/-
Trusted code for structured-merge-diff's `sigs.k8s.io/structured-merge-diff/v7/value` (v7.0.0,
`8d11054b`), in namespace `sigs_k8s_io.structured_merge_diff.v7.value` like the generated package
(`Code/sigs_k8s_io/structured_merge_diff/v7/value.toml`; notes/smd-goose.md).
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace sigs_k8s_io.structured_merge_diff.v7.value
section code
variable [GooseExts] [GoGlobalContext]

/-! ### The reflection implementation's package variables

```go
var nilType = reflect.TypeOf(&struct{}{})                                     // valuereflect.go
var isZeroerType = reflect.TypeOf((*isZeroer)(nil)).Elem()                    // jsontagutil.go
var marshalerType = reflect.TypeFor[json.Marshaler]()                         // reflectcache.go
var unmarshalerType = reflect.TypeFor[json.Unmarshaler]()
var unstructuredConverterType = reflect.TypeFor[UnstructuredConverter]()
var unstructuredConverterWithErrorType = reflect.TypeFor[UnstructuredConverterWithError]()
var defaultReflectCache = newReflectCache()
```

Each model does nothing, and the variable keeps its zero value. The first six are runtime type
descriptors (`reflect.Type`), which the semantics cannot represent (`reflect` is names only in
Perennial); Go computes each from a static descriptor (`TypeOf` of a non-nil pointer or of a nil
interface pointer, `Elem` of a pointer type, `TypeFor` of an interface type), which cannot panic
and has no other effect the program can see. `newReflectCache` (`reflectcache.go`) allocates a
`typeReflectCache` and stores an empty `reflectCacheMap` (`make`) into its `atomic.Value`: no panic
(the first `Store` of a non-nil value), and its only effect is the allocation. The only readers
of all seven are the reflection implementation's functions (`valuereflect.go`, `structreflect.go`,
`mapreflect.go`, `listreflect.go`, `reflectcache.go`, `jsontagutil.go`), which are names only: no
translated code loads them, so their values are unobservable to the translated program. A
translation of a reader would need a model that stores the value. -/

/-- `nilType = reflect.TypeOf(&struct{}{})`: does nothing. -/
def nilType.init : val :=
  λ: <>, #()

/-- `isZeroerType = reflect.TypeOf((*isZeroer)(nil)).Elem()`: does nothing. -/
def isZeroerType.init : val :=
  λ: <>, #()

/-- `marshalerType = reflect.TypeFor[json.Marshaler]()`: does nothing. -/
def marshalerType.init : val :=
  λ: <>, #()

/-- `unmarshalerType = reflect.TypeFor[json.Unmarshaler]()`: does nothing. -/
def unmarshalerType.init : val :=
  λ: <>, #()

/-- `unstructuredConverterType = reflect.TypeFor[UnstructuredConverter]()`: does nothing. -/
def unstructuredConverterType.init : val :=
  λ: <>, #()

/-- `unstructuredConverterWithErrorType = reflect.TypeFor[UnstructuredConverterWithError]()`:
does nothing. -/
def unstructuredConverterWithErrorType.init : val :=
  λ: <>, #()

/-- `defaultReflectCache = newReflectCache()`: does nothing (see above: an allocation only the
names-only reflection cache reads). -/
def defaultReflectCache.init : val :=
  λ: <>, #()

/-- The interface assertions of `fields.go`,

```go
var _ json.MarshalerTo = (*FieldList)(nil)
var _ json.UnmarshalerFrom = (*FieldList)(nil)
```

(goose names every blank variable `_`, and both run this model): a compile-time check; at run
time the conversion of a nil pointer to an interface, discarded, which cannot panic and has no
effect. Does nothing. -/
def «_».init : val :=
  λ: <>, #()

end code
end sigs_k8s_io.structured_merge_diff.v7.value

end Perennial
