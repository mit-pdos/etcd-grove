/-
Trusted code for structured-merge-diff's `sigs.k8s.io/structured-merge-diff/v7/fieldpath`
(v7.0.0, `8d11054b`), in namespace `sigs_k8s_io.structured_merge_diff.v7.fieldpath` like the
generated package (`Code/sigs_k8s_io/structured_merge_diff/v7/fieldpath.toml`;
notes/smd-goose.md).
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace sigs_k8s_io.structured_merge_diff.v7.fieldpath
section code
variable [GooseExts] [GoGlobalContext]

/-! ### The FieldsV1 serialization's package variables

```go
var allowInvalidUTF8 = jsontext.AllowInvalidUTF8(true)    // serialize-pe.go
var allowDuplicates = jsontext.AllowDuplicateNames(true)
var pool = sync.Pool{New: func() any { … }}              // serialize.go
var _ json.MarshalerTo = fastMarshalValue{}               // serialize-pe.go
var _ json.MarshalerTo = (*setContentsV1)(nil)            // serialize.go
var _ json.UnmarshalerFrom = (*setContentsV1)(nil)
```

Each model does nothing, and the variable keeps its zero value. `AllowInvalidUTF8` and
`AllowDuplicateNames` (`encoding/json/jsontext`, not translated) return a constant option value
(a flag set; they cannot panic and allocate nothing visible); `pool`'s initializer is a struct
literal whose `New` is a function literal (no call, no panic); the blank variables are
compile-time interface checks, at run time the conversion of a value to an interface, discarded.
The only readers of the three named variables are the JSON serialization's functions
(`serialize.go`, `serialize-pe.go`: `Set.ToJSON`, `FromJSON`, `SerializePathElement`, ...), which
are names only: no translated code loads them. A translation of a reader would need a model that
stores the value. -/

/-- `allowInvalidUTF8 = jsontext.AllowInvalidUTF8(true)`: does nothing. -/
def allowInvalidUTF8.init : val :=
  λ: <>, #()

/-- `allowDuplicates = jsontext.AllowDuplicateNames(true)`: does nothing. -/
def allowDuplicates.init : val :=
  λ: <>, #()

/-- `pool = sync.Pool{New: …}` (the serializer's buffer pool): does nothing. -/
def pool.init : val :=
  λ: <>, #()

/-- The three blank interface assertions (goose names every blank variable `_`, and all three
run this model): does nothing. -/
def «_».init : val :=
  λ: <>, #()

end code
end sigs_k8s_io.structured_merge_diff.v7.fieldpath

end Perennial
