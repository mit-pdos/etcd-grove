/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__runSnapshots.lean (241f27e).
-/
/-
`raft.(*Raft).runSnapshots`'s spec (raft-internal interface). The snapshot goroutine (started by `NewRaft` through `goFunc`). Stage 3: it snapshots (`takeSnapshot`) when `shouldSnapshot` says so and on user requests. It never returns.
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

/-- `(*Raft).runSnapshots`: the snapshot goroutine (started by `NewRaft` through `goFunc`): on its
timer, when `shouldSnapshot` says so, and on each user request (`userSnapshotCh`, answered with
`takeSnapshot`'s error), takes a snapshot (`takeSnapshot`). It never returns (`shutdownCh` is never
closed). -/
abbrev github_com.hashicorp.raft.Raft.runSnapshots.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"runSnapshots")) (Val #()))
  {{ RET #(); False }}

end spec

end Perennial
