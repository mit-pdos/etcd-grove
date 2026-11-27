/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__persistVote.lean (241f27e).
-/
/-
`raft.(*Raft).persistVote`'s spec (raft-internal interface, notes/raft-iface.md). Writes the vote to the stable store (whose writes never fail).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

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

/-- `(*Raft).persistVote`: Writes the vote to the stable store (whose writes never fail). -/
abbrev github_com.hashicorp.raft.Raft.persistVote.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (sst : StableAbs) (t : w64) (cs : GoSlice)
    (cb : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ rc.ownS sst ∗ cs ↦*□ cb }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"persistVote")) (Val #t)) (Val #cs))
  {{ RET #interface.nil; rc.ownS (StableAbs.mk (sst.ints.insert (go!"LastVoteTerm" : List w8) t)
      (sst.bytes.insert (go!"LastVoteCand" : List w8) cb)) }}

end spec

end Perennial
