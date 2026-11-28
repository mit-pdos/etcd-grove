/-
`service.API.Apply`'s spec (the hraft kit's API service, notes/dsv-hraft.md, S5).
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

/-- `a.Apply(args, reply)`: submits the command `d` with its token and waits for the outcome;
`reply` says it (`applyOut`); returns nil. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.API.Apply.spec : Prop :=
  ∀ (a args reply : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (fc : FCtx GF) (alb : GName)
    (sl : GoSlice) (d : List w8) (n : Nat) (rep0 : ApplyReply),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗
      isAPI a γ rc i fc alb ∗ args ↦□ ApplyArgs.mk sl ∗ sl ↦*□ d ∗ opTok γ d n ∗ reply ↦ rep0 }}
    (App (App (Val (a @!! go.GoType.PointerType API.ty @!! go!"Apply")) (Val #args)) (Val #reply))
  {{ RET #interface.nil; ∃ rep : ApplyReply, reply ↦ rep ∗ applyOut γ fc d n rep }}

end spec

end Perennial
