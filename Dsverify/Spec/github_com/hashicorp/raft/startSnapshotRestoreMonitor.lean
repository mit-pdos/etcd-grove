/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/startSnapshotRestoreMonitor.lean (241f27e).
-/
/-
``startSnapshotRestoreMonitor(cr, size, networkTransfer)``'s spec (stage 3, raft-internal, snap: package-internal).
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

/-- `startSnapshotRestoreMonitor(cr, size, networkTransfer)`: starts the monitor goroutine (which only waits for its stop: `runOnce` reports nothing) and returns the monitor. -/
abbrev github_com.hashicorp.raft.startSnapshotRestoreMonitor.spec : Prop :=
  ∀ (cr : GoInterface) (size : w64) (nt : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
    (App (App (App (Val (@! github_com.hashicorp.raft.startSnapshotRestoreMonitor)) (Val #cr))
      (Val #size)) (Val #nt))
  {{ (m : Loc), RET #m; monitorOwn m }}

end spec

end Perennial
