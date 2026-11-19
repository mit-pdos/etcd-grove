/-
Trusted code for structured-merge-diff's `sigs.k8s.io/structured-merge-diff/v7/typed` (v7.0.0,
`8d11054b`), in namespace `sigs_k8s_io.structured_merge_diff.v7.typed` like the generated package
(`Code/sigs_k8s_io/structured_merge_diff/v7/typed.toml`; notes/smd-goose.md).
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace sigs_k8s_io.structured_merge_diff.v7.typed
section code
variable [GooseExts] [GoGlobalContext]

/-! ### The parser's package variables (`parser.go`)

```go
var ssParser = createOrDie(YAMLObject(schema.SchemaSchemaYAML))

var DeducedParseableType ParseableType = createOrDie(YAMLObject(`types:
- name: __untyped_atomic_
  …
- name: __untyped_deduced_
  …
`)).Type("__untyped_deduced_")
```

Each model does nothing, and the variable keeps its zero value. Go's initializers parse a
constant YAML document with `go.yaml.in/yaml/v2` (`yaml.Unmarshal` into a `schema.Schema`,
through reflection; not translated) and panic if it fails to parse (`createOrDie`). Both
documents are constants of the pinned source and parse: every program that imports `typed` runs
both initializers before `main` (any Kubernetes API server, SMD's own tests, the driver
`examples/k8s/smd`), so on the pinned `go.yaml.in/yaml/v2` (v2.4.2, SMD's `go.mod`) they do not
panic. Their effect is to allocate the parsed schema and store the parser (resp. the
`ParseableType`) into the variable.

That stored value is what this model leaves out, and it is unobservable to the translated
program: `ssParser`'s only reader is `NewParser` (names only), and `DeducedParseableType` has no
reader in SMD's translated packages (`value`, `schema`, `fieldpath`, `typed`, `merge`; its users
are SMD's test fixtures and Kubernetes' API server for objects without a schema) nor in the
driver. A translated reader of `DeducedParseableType` would load a zero `ParseableType` (a nil
`Schema`) where Go has the deduced schema: such a reader needs this model replaced by one that
builds the two `TypeDef`s first. -/

/-- `ssParser = createOrDie(YAMLObject(schema.SchemaSchemaYAML))`: does nothing. -/
def ssParser.init : val :=
  λ: <>, #()

/-- `DeducedParseableType = createOrDie(…).Type("__untyped_deduced_")`: does nothing (no
translated reader; see above). -/
def DeducedParseableType.init : val :=
  λ: <>, #()

end code
end sigs_k8s_io.structured_merge_diff.v7.typed

end Perennial
