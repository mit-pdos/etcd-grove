/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__preElectSelf.lean (241f27e).
-/
/-
`raft.(*Raft).preElectSelf`'s spec (main goroutine; internal to MAIN-C). Asks every other voter
for a pre-vote of term `s.term + 1` (no protocol effect) and returns the pre-vote channel.
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

/-- `(*Raft).preElectSelf()`. -/
abbrev github_com.hashicorp.raft.Raft.preElectSelf.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
      mainOwnAt r γ rc i s st ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"preElectSelf")) (Val #()))
  {{ (ch : Loc), RET #ch; ∃ γc : ChanNames,
      mainOwnAt r γ rc i s st ∗ isChanBag (V := Loc) γc ch (pvP γ (s.term + 1)) ∗ rtok tid }}

end spec

end Perennial
