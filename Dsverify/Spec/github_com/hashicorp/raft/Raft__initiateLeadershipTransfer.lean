/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__initiateLeadershipTransfer.lean (241f27e).
-/
/-
`raft.(*Raft).initiateLeadershipTransfer`'s spec (stage 2; API-internal: `LeadershipTransfer` and
`LeadershipTransferToServer` call it).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.FutBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

/-- `(*Raft).initiateLeadershipTransfer(id, address)` (API-internal): no target (`nil`, `nil`) or a
voter `j` as both (read-only); returns a future whose `Error()` may be called once (any answer). -/
abbrev github_com.hashicorp.raft.Raft.initiateLeadershipTransfer.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (idp ap : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     (⌜idp = null ∧ ap = null⌝ ∨
      ∃ j : SID, idp ↦□ (j : ServerID) ∗ ap ↦□ (j : ServerAddress) ∗ isSrv γ j) }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"initiateLeadershipTransfer"))
      (Val #idp)) (Val #ap))
  {{ (fi : GoInterface), RET #fi; futWait fi (fun _ => iprop(True)) }}

end spec

end Perennial
