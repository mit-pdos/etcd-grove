/-
Lean-first (no Rocq counterpart).

# linkv: the instance's vocabulary for `lintest` (2026-10-19)

What the `lintest` driver's specs (`Proof/.../examples/lintest/Defs.lean`: `genSpec`,
`applySpec`) are instantiated with for `examples/linkv`:

- `boxIn x`: the Go input `x : Input` as the driver passes it, `any(x)`;
- `genKeys`, `genVals`: the keys and values `Gen` picks from (its local slices);
- `GenInput x`: `x` is an input `Gen` may return: its key one of `genKeys` and, for a put, its
  value one of `genVals`;
- `linkvInOk i`: the driver's `inOk`: `i` is a boxed `Input` that `Gen` may return. `Gen`
  returns only such inputs (`Gen.spec`); `Apply` may assume one (its `input.(Input)` cannot
  panic, and the key is one of three short, non-empty strings).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkv

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The input `x`, boxed (`any(x)`). -/
abbrev boxIn (x : Input) : GoInterface := interface.mkOk Input.ty #x

/-- The keys `Gen` picks from. -/
abbrev genKeys : List GoString := [go!"k0", go!"k1", go!"k2"]

/-- The values `Gen` picks from. -/
abbrev genVals : List GoString := [go!"a", go!"b", go!"c", go!"d"]

/-- An input `Gen` may return. -/
def GenInput (x : Input) : Prop := x.Key' ∈ genKeys ∧ (x.Put' = true → x.Val' ∈ genVals)

/-- The driver's `inOk` (see the file header). -/
abbrev linkvInOk (i : GoInterface) : IProp GF := iprop(⌜∃ x : Input, i = boxIn x ∧ GenInput x⌝)

end defs

end linkv
end EtcdGrove
end Perennial
