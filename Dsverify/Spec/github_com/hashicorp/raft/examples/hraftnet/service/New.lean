/-
`service.New`'s spec (the hraft kit's API service, notes/dsv-hraft.md, S5).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.ApiDefs

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

/-- `New(r, fsm, enqueue, wait)`: server `i`'s API over its raft `r`, whose responses are the
store's (`rc.respP = respP γ fc alb`), and its store `fsm`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.New.spec : Prop :=
  ∀ (r fsm : Loc) (enq wt : time.Duration) (γ : GNames) (rc : RCtx GF) (i : SID) (fc : FCtx GF)
    (alb : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗
      isRaft r γ rc i ∗ ⌜rc.respP = respP γ fc alb⌝ ∗ isStore γ fc alb i fsm }}
    (App (App (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.service.New))
      (Val #r)) (Val #fsm)) (Val #enq)) (Val #wt))
  {{ (a : Loc), RET #a; isAPI a γ rc i fc alb }}

end spec

end Perennial
