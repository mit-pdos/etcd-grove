/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__runCandidate.lean (241f27e).
-/
/-
`raft.(*Raft).runCandidate`'s spec (main goroutine; internal to MAIN-C). Entered with the state
`Candidate`; returns as follower (newer term), as leader (`becomeLeader` before
`setState(Leader)`), or still candidate (election timeout).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.main.MainCLemmas
public import Dsverify.Proof.github_com.hashicorp.raft.iface.Net

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*Raft).runCandidate()`. -/
abbrev github_com.hashicorp.raft.Raft.runCandidate.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
      mainOwnAt r γ rc i s stCandidate ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"runCandidate")) (Val #()))
  {{ RET #(); mainOwn r γ rc i ∗ rtok tid }}

end spec

end Perennial
