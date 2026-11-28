/-
`rpctransport.copyBytes`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Wire

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-- `copyBytes(b)`: a fresh copy of the bytes of `b`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        b ↦*{dq} bs }}
      (App (Val (@! copyBytes)) (Val #b))
    {{ (c : GoSlice), RET #c; b ↦*{dq} bs ∗ c ↦* bs }}

end spec

end Perennial
