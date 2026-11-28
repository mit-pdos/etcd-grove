/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__Snapshot.lean (241f27e).
-/
/-
`raft.(*Raft).Snapshot`'s spec (stage 3, API: a user snapshot).
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

/-- `r.Snapshot()` (stage 3, the adversary's user snapshot): sends a user snapshot request to the
snapshot goroutine (`userSnapshotCh`, `userSnapP`) and returns its future, whose `Error()` the caller
may call once (any answer: `futWait`). -/
abbrev github_com.hashicorp.raft.Raft.Snapshot.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"Snapshot")) (Val #()))
  {{ (fi : GoInterface), RET #fi; futWait fi (fun _ => iprop(True)) }}

end spec

end Perennial
