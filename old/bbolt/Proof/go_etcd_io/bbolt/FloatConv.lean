/-
Conversions between integers and `float64`, which Perennial's `Float64Semantics` does not
model (the float operations themselves are `FloatOps`, uninterpreted): `node.splitTwo`
(`float64(pageSize)` of a `uintptr`, `int(...)` of the product) and `node.rebalance`
(`float64(pageSize)` of an `int`).

`FloatConvSemantics` gives the conversions as uninterpreted functions on the 64 bits (an
integer's bits in, a `float64`'s bits out, and back) with their step facts, as instances the
way `Perennial/Golang/Defn/Predeclared.lean`'s `Float64Semantics` does. Go's float-to-integer
conversion of a value out of range (or NaN) is implementation-defined, not a panic: the
conversion is total. Proofs take the class as an instance hypothesis; it is to move into
Perennial (with the next batch of its changes).
-/
module

public import Perennial.Golang.Defn.Predeclared

@[expose] public section

namespace Perennial
namespace go

section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

/-- Integer/`float64` conversions: the functions, uninterpreted, and their step facts. -/
class FloatConvSemantics [GoSemanticsFunctions] where
  /-- `float64(x)` of an unsigned 64-bit integer (`uint64`, `uint`, `uintptr`). -/
  float64OfUint64 : w64 → w64
  /-- `float64(x)` of a signed 64-bit integer (`int64`, `int`). -/
  float64OfInt64 : w64 → w64
  /-- `int64(f)`/`int(f)`: total (Go: implementation-defined out of range). -/
  float64ToInt64 : w64 → w64
  /-- `uint64(f)`/`uint(f)`/`uintptr(f)`: total. -/
  float64ToUint64 : w64 → w64
  convert_uintptr_to_float64 (v : w64) :
    ⟦Convert go.uintptr go.float64, #v⟧ ⤳[under] #(float64OfUint64 v)
  convert_uint64_to_float64 (v : w64) :
    ⟦Convert go.uint64 go.float64, #v⟧ ⤳[under] #(float64OfUint64 v)
  convert_uint_to_float64 (v : w64) :
    ⟦Convert go.uint go.float64, #v⟧ ⤳[under] #(float64OfUint64 v)
  convert_int_to_float64 (v : w64) :
    ⟦Convert go.int go.float64, #v⟧ ⤳[under] #(float64OfInt64 v)
  convert_int64_to_float64 (v : w64) :
    ⟦Convert go.int64 go.float64, #v⟧ ⤳[under] #(float64OfInt64 v)
  convert_float64_to_int (v : w64) :
    ⟦Convert go.float64 go.int, #v⟧ ⤳[under] #(float64ToInt64 v)
  convert_float64_to_int64 (v : w64) :
    ⟦Convert go.float64 go.int64, #v⟧ ⤳[under] #(float64ToInt64 v)
  convert_float64_to_uintptr (v : w64) :
    ⟦Convert go.float64 go.uintptr, #v⟧ ⤳[under] #(float64ToUint64 v)
  convert_float64_to_uint64 (v : w64) :
    ⟦Convert go.float64 go.uint64, #v⟧ ⤳[under] #(float64ToUint64 v)
  convert_float64_to_uint (v : w64) :
    ⟦Convert go.float64 go.uint, #v⟧ ⤳[under] #(float64ToUint64 v)

attribute [instance] FloatConvSemantics.convert_uintptr_to_float64
  FloatConvSemantics.convert_uint64_to_float64 FloatConvSemantics.convert_uint_to_float64
  FloatConvSemantics.convert_int_to_float64 FloatConvSemantics.convert_int64_to_float64
  FloatConvSemantics.convert_float64_to_int FloatConvSemantics.convert_float64_to_int64
  FloatConvSemantics.convert_float64_to_uintptr FloatConvSemantics.convert_float64_to_uint64
  FloatConvSemantics.convert_float64_to_uint
export FloatConvSemantics (float64OfUint64 float64OfInt64 float64ToInt64 float64ToUint64
  convert_uintptr_to_float64 convert_uint64_to_float64 convert_uint_to_float64
  convert_int_to_float64 convert_int64_to_float64 convert_float64_to_int convert_float64_to_int64
  convert_float64_to_uintptr convert_float64_to_uint64 convert_float64_to_uint)

end defs
end go
end Perennial
