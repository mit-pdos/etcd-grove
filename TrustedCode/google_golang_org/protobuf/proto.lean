/-
Trusted code for protobuf-go's `google.golang.org/protobuf/proto` (v1.36.12), in namespace
`google_golang_org.protobuf.proto` like the generated package
(`Code/google_golang_org/protobuf/proto.toml`).

`proto` is translated names-only (its functions are the trust-boundary specs of
`Spec/google_golang_org/protobuf/proto/`), so no translated code reads the variables below, and a
translated reader could not load one: nothing gives a points-to for it (the package's `isPkgInit`
is `True`). Each model does nothing, and the variable is not allocated (2026-10-20; until then
each was an axiom of the translation, and the trust-boundary axioms `proto.opaqueInitsOk` and
`proto.initFuncsOk` said they return). Each Go initializer returns without panicking and has no
effect a translated function can observe, so the no-op loses nothing a proof could use. The other
rung, translating them, would need protobuf's `internal/errors` (`errors.New`, `errors.Error`)
and `protowire` translated, for variables whose only readers are untranslated.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace google_golang_org.protobuf.proto
section code
variable [GooseExts] [GoGlobalContext]

/-- `wireTypes` (`encode_gen.go`), the wire type of each field kind, read by the encoder:

```go
var wireTypes = map[protoreflect.Kind]protowire.Type{
	protoreflect.BoolKind:     protowire.VarintType,
	...
}
```

A map literal of constants: it allocates the map, and cannot panic. The model does nothing. -/
def wireTypes.init : val :=
  λ: <>, #()

/-- `errUnknown = errors.New("BUG: internal error (unknown)")` (`decode.go`; `errors` is
protobuf's `internal/errors`): allocates the error, and cannot panic. The model does nothing. -/
def errUnknown.init : val :=
  λ: <>, #()

/-- `errDecode = errors.New("cannot parse invalid wire-format data")` (`decode.go`): allocates the
error, and cannot panic. The model does nothing. -/
def errDecode.init : val :=
  λ: <>, #()

/-- `errRecursionDepth = errors.New("exceeded maximum recursion depth")` (`decode.go`): allocates
the error, and cannot panic. The model does nothing. -/
def errRecursionDepth.init : val :=
  λ: <>, #()

/-- `proto`'s `init` function (`proto.go`):

```go
var Error error

func init() {
	Error = errors.Error
}
```

It stores protobuf's `internal/errors.Error` (a sentinel error value) into `Error`, the value
`errors.Is` compares a protobuf error against; it cannot panic. The model does nothing: no
translated code reads `Error` (the trust-boundary specs of `proto`'s functions do not mention it),
and `Error` is not allocated (names-only, so no `GlobalAlloc` of it is translated). -/
def init.«0».impl : val :=
  λ: <>, #()

end code
end google_golang_org.protobuf.proto

end Perennial
