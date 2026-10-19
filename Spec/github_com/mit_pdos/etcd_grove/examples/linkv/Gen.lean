/- Lean-first (no Rocq counterpart).

`Gen(id)` (linkv.go): the input generator `lintest.Run` is given, the function value `Gen`, meets
`genSpec` (`Proof/.../lintest/Defs.lean`) with `linkvInOk`: for any client id, it returns a boxed
`Input` with a key of `genKeys` and, for a put, a value of `genVals` (`GenInput`), whatever
`primitive.RandomUint64` returns. It needs no `isPkgInit`: it reads no package variable.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- See the file header. -/
abbrev Gen.spec : Prop :=
  ⊢ lintest.genSpec (GF := GF)
      (functions github_com.mit_pdos.etcd_grove.examples.linkv.Gen []) linkvInOk

end spec

end linkv
end EtcdGrove
end Perennial
