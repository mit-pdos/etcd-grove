/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setLatestConfiguration.lean (241f27e).
-/
/-
`raft.(*Raft).setLatestConfiguration`'s spec (API-internal; called by `NewRaft` and, stage 3, by `installSnapshot`).
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

/-- `(*Raft).setLatestConfiguration(c, ci)`: stores `c` as the latest configuration and a pointer to a
copy of it in the `latestConfiguration` cell (D33: an `atomic.Pointer[Configuration]`). Two modes (`b`):
the caller owns the cell (`NewRaft`: it gets the cell back pointing to the copy, whose servers it owns),
or (stage 3, `installSnapshot`, review T1-6) the cell is `isRaft`'s invariant cell (`raftConf`,
`latestCfgCell`) and `c` has no servers or is a valid configuration (stage 4, `srvsOk`; stage 3: a
bootstrap configuration): the copy goes into the invariant. (Stage 4: the main goroutine calls it in
the second mode whenever its latest configuration changes.) -/
abbrev github_com.hashicorp.raft.Raft.setLatestConfiguration.spec : Prop :=
  ∀ (b : Bool) (r : Loc) (γ : GNames) (c0 l : Configuration) (i0 li : w64) (c : Configuration)
    (ci : w64) (ss : List Server) (dq : DFrac) (p0 : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     r.[Raft, go!"configurations"] ↦ configurations.mk c0 i0 l li ∗
     c.Servers' ↦*{dq} ss ∗
     (if b then sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"])
        (DFrac.own 1) p0
      else ⌜ss = [] ∨ srvsOk γ ss⌝ ∗ inv latestCfgN (latestCfgCell r γ)) }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setLatestConfiguration")) (Val #c)) (Val #ci))
  {{ RET #(); r.[Raft, go!"configurations"] ↦ configurations.mk c0 i0 c ci ∗ c.Servers' ↦*{dq} ss ∗
      (if b then ∃ (p : Loc) (c' : Configuration),
        sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p ∗
        p ↦□ c' ∗ c'.Servers' ↦* ss else True) }}

end spec

end Perennial
