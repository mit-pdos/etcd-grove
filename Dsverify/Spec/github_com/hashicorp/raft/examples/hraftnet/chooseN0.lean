/-
`hraftnet.chooseN0`'s spec (the hraft kit's orchestrator, notes/dsv-hraft.md, S5g).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ConfDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet

/-- `chooseN0()`: 3 or 5 (`3 + 2*rnd(2)`), with the two receipts of its arithmetic's steps (the
orchestrator's draw spends them on the drawn protocol's bounds, `gprot.alloc_init`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.chooseN0.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet }}
    (App (Val (@! chooseN0)) (Val #()))
  {{ (r : w64), RET #r; ∃ n : Nat, ⌜r = W64 (n : Int) ∧ N0Ok n⌝ ∗ ⧗ 2 }}

end spec

end Perennial
