/-
`service.API.Status`'s spec (the hraft kit's API service, notes/dsv-hraft.md, S5).
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

/-- `a.Status(args, reply)`: what this server knows of the cluster (`State`, `LeaderWithID` on a
goroutine of its own, `GetConfiguration`'s servers and voters); the reply carries no facts. Runs on a
goroutine with no thread token (net/rpc's method goroutine): the forked goroutine has one. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.API.Status.spec : Prop :=
  ∀ (a args reply : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (fc : FCtx GF) (alb : GName)
    (rep0 : StatusReply),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗ isAPI a γ rc i fc alb ∗ reply ↦ rep0 }}
    (App (App (Val (a @!! go.GoType.PointerType API.ty @!! go!"Status")) (Val #args)) (Val #reply))
  {{ RET #interface.nil; ∃ rep : StatusReply, reply ↦ rep }}

end spec

end Perennial
