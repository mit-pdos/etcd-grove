/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/snapshotRestoreMonitor__run.lean (241f27e).
-/
/-
``getSnapshotVersion(v)``'s spec (stage 3, raft-internal, snap: package-internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.SnapDefs
public import Perennial.Proof.context.Base

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

/-- `(*snapshotRestoreMonitor).run(ctx)`: the monitor goroutine: until `ctx` is done, `runOnce` on
each tick; then closes `doneCh` (the closer's right, `.Pending`). -/
abbrev github_com.hashicorp.raft.snapshotRestoreMonitor.run.spec : Prop :=
  ∀ (m : Loc) (ctx : GoInterfaceOk) (desc : context.ContextDesc (IProp GF)) (dch : Loc) (γd : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     m.[snapshotRestoreMonitor, go!"doneCh"] ↦□ dch ∗ ownBroadcastChan dch γd iprop(True) .Pending ∗
     context.isContext ctx desc }}
    (App (Val (m @!! go.GoType.PointerType snapshotRestoreMonitor.ty @!! go!"run"))
      (Val #(interface.ok ctx)))
  {{ RET #(); True }}

end spec

end Perennial
