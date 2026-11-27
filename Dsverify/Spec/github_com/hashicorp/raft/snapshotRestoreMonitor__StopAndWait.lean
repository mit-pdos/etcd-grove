/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/snapshotRestoreMonitor__StopAndWait.lean (241f27e).
-/
/-
``(*snapshotRestoreMonitor).StopAndWait()``'s spec (stage 3, raft-internal, snap: package-internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.SnapDefs

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

/-- `(*snapshotRestoreMonitor).StopAndWait()`: stops the monitor goroutine (once) and waits for it. -/
abbrev github_com.hashicorp.raft.snapshotRestoreMonitor.StopAndWait.spec : Prop :=
  ∀ (m : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ monitorOwn m }}
    (App (Val (m @!! go.GoType.PointerType snapshotRestoreMonitor.ty @!! go!"StopAndWait")) (Val #()))
  {{ RET #(); True }}

end spec

end Perennial
