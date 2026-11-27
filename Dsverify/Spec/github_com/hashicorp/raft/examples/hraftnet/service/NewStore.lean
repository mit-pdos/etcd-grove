/-
`service.NewStore`'s spec (the hraft kit's state machine, notes/dsv-hraft.md, S5).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.FsmDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

/-- `NewStore()`: an empty register, the store of server `i` in the FSMs' context `fc`, with its
FSM goroutine's state at `0`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.NewStore.spec : Prop :=
  ∀ (γ : GNames) (fc : FCtx GF) (i : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗ frInv γ fc ∗ linStep γ fc ∗ durBound γ i }}
    (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.service.NewStore)) (Val #()))
  {{ (s : Loc), RET #s; ∃ alb : GName, isStore γ fc alb i s ∗ fsmOwn alb 0 }}

end spec

end Perennial
