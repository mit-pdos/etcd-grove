/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__getLatestConfiguration.lean (241f27e).
-/
/-
`raft.(*Raft).getLatestConfiguration`'s spec (API-internal; stage 3, D33: the cell is an
`atomic.Pointer[Configuration]`).
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

/-- `(*Raft).getLatestConfiguration()`: any goroutine; a copy of the latest configuration, with no
servers or a valid one (`cfgOpt`; stage 4; stage 3: a bootstrap configuration: `raftConf`'s cell always
points to one after `NewRaft`). -/
abbrev github_com.hashicorp.raft.Raft.getLatestConfiguration.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getLatestConfiguration")) (Val #()))
  {{ (c : Configuration), RET #c; cfgOpt γ c }}

end spec

end Perennial
