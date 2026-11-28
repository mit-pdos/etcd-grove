/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__run.lean (241f27e).
-/
/-
`raft.(*Raft).run`'s spec (raft-internal interface, notes/raft-iface.md). The main goroutine (started by `NewRaft` through `goFunc`). It never returns (`shutdownCh` is never closed).
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

/-- `(*Raft).run`: The main goroutine (started by `NewRaft` through `goFunc`). It never returns (`shutdownCh` is never closed). -/
abbrev github_com.hashicorp.raft.Raft.run.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ mainOwn r γ rc i ∗ leaderStateAny r rc ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"run")) (Val #()))
  {{ RET #(); False }}

end spec

end Perennial
