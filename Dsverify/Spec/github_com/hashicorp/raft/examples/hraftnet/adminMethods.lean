/-
`hraftnet.adminMethods`'s spec (the hraft kit's orchestrator, notes/dsv-hraft.md, S5g).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.OrchDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]
variable [π : NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet

/-- `adminMethods()`: a new slice of the admin's methods. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.adminMethods.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! adminMethods)) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ L, sl ↦* L ∗ ⌜L = adminMeths⌝ }}

end spec

end Perennial
