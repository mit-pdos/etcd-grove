/-
`hraftnet.chooseOps`'s spec (the hraft kit's orchestrator, notes/dsv-hraft.md, S5g).
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

/-- `chooseOps()`: 1 to `MaxOps` (`2 ^ 20`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.chooseOps.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet }}
    (App (Val (@! chooseOps)) (Val #()))
  {{ (r : w64), RET #r; ⌜1 ≤ uint.Z r ∧ uint.Z r ≤ 2 ^ 20⌝ }}

end spec

end Perennial
