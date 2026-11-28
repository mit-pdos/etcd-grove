/-
`hraftnet.configure`'s spec (the hraft kit's configuration protocol, notes/dsv-hraft.md, S5g).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ConfDefs

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
variable [π : NetProtoGS]

open github_com.hashicorp.raft.examples.hraftnet

/-- `configure(n0)`: the drawn size `n0` (`chosen γc n`) sent to every server machine's configuration
address, each until it acknowledges it. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.configure.spec : Prop :=
  ∀ (γc : GName) (n : Nat), N0Ok n →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ∗
        confProtos (G := hG.goose_globalGS) γc ∗ chosen γc n }}
      (App (Val (@! configure)) (Val #(W64 (n : Int))))
    {{ RET #(); True }}

end spec

end Perennial
