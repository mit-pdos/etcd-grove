/-
Trusted code for protobuf-go's `google.golang.org/protobuf/reflect/protoreflect` (v1.36.12), in
namespace `google_golang_org.protobuf.reflect.protoreflect` like the generated package
(`Code/google_golang_org/protobuf/reflect/protoreflect.toml`).
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace google_golang_org.protobuf.reflect.protoreflect
section code
variable [FfiSyntax] [GoGlobalContext]

/-! ### The type descriptors (`value_unsafe.go`)

```go
var (
	nilType     = typeOf(nil)
	boolType    = typeOf(*new(bool))
	...
	enumType    = typeOf(*new(EnumNumber))
)

// typeOf returns a pointer to the Go type information.
func typeOf(t any) unsafe.Pointer {
	return (*ifaceHeader)(unsafe.Pointer(&t)).Type
}
```

Each model does nothing, and the variable is not allocated (2026-10-20; until then each `X.init`
was an axiom of the translation, which the trust-boundary axiom `protoreflect.opaqueInitsOk` said
returns). Each value is the runtime type descriptor of a type, read out of an interface's memory
through `unsafe`, which the semantics cannot represent: irreducible, as Perennial's
`errors.errorType`. Go's initializer reads a static descriptor and allocates nothing the program
can see, so it cannot panic and has no other effect. Its readers (`Value`'s methods, `ValueOf*`)
are not translated (`protoreflect` is names-only), and a translated reader could not load the
variable: nothing gives a points-to for it (the package's `isPkgInit` is `True`). -/

/-- `nilType = typeOf(nil)`: does nothing. -/
def nilType.init : val :=
  λ: <>, #()

/-- `boolType = typeOf(*new(bool))`: does nothing. -/
def boolType.init : val :=
  λ: <>, #()

/-- `int32Type = typeOf(*new(int32))`: does nothing. -/
def int32Type.init : val :=
  λ: <>, #()

/-- `int64Type = typeOf(*new(int64))`: does nothing. -/
def int64Type.init : val :=
  λ: <>, #()

/-- `uint32Type = typeOf(*new(uint32))`: does nothing. -/
def uint32Type.init : val :=
  λ: <>, #()

/-- `uint64Type = typeOf(*new(uint64))`: does nothing. -/
def uint64Type.init : val :=
  λ: <>, #()

/-- `float32Type = typeOf(*new(float32))`: does nothing. -/
def float32Type.init : val :=
  λ: <>, #()

/-- `float64Type = typeOf(*new(float64))`: does nothing. -/
def float64Type.init : val :=
  λ: <>, #()

/-- `stringType = typeOf(*new(string))`: does nothing. -/
def stringType.init : val :=
  λ: <>, #()

/-- `bytesType = typeOf(*new([]byte))`: does nothing. -/
def bytesType.init : val :=
  λ: <>, #()

/-- `enumType = typeOf(*new(EnumNumber))`: does nothing. -/
def enumType.init : val :=
  λ: <>, #()

end code
end google_golang_org.protobuf.reflect.protoreflect

end Perennial
