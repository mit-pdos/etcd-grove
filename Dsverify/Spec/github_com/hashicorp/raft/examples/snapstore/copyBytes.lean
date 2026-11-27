/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/inproc/copyBytes.lean (241f27e),
into snapstore (the `Reader` moved there: examples/snapstore/reader.go).
-/
/-
`snapstore.copyBytes`'s spec.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.snapstore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

/-- `copyBytes(b)`: a fresh copy of the bytes of `b`. -/
abbrev github_com.hashicorp.raft.examples.snapstore.copyBytes.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗
        b ↦*{dq} bs }}
      (App (Val (@! copyBytes)) (Val #b))
    {{ (c : GoSlice), RET #c; b ↦*{dq} bs ∗ c ↦* bs }}

end spec

end Perennial
