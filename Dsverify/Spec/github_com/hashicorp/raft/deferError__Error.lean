/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/deferError__Error.lean (241f27e).
-/
/-
`raft.(*deferError).Error`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*logFuture` (promoted; also hr3's `f.Error()` on the `ApplyFuture`): waits for the answer, once.
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

/-- `(*deferError).Error`: Called through `*logFuture` (promoted; also hr3's `f.Error()` on the
`ApplyFuture`), and (stage 2) through `*verifyFuture` and `*leadershipTransferFuture` (hr3's
`waitFuture` on `VerifyLeader`'s and `LeadershipTransfer`'s futures), (stage 3) through
`*userSnapshotFuture` (hr3's `waitFuture` on `Snapshot`'s future), (stage 4) through
`*configurationChangeFuture` (promoted through its `logFuture`; hr3's `waitFuture` on the configuration
changes' futures), and on any `*deferError` (raft's
own futures: the install's restore future, `takeSnapshot`'s snapshot and configurations requests,
whose `ShutdownCh` is the never-closed `shutdownCh`, `deferWait`): waits for the answer, once. -/
abbrev github_com.hashicorp.raft.deferError.Error.spec : Prop :=
  (∀ (f : Loc) (Q : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ deferWait (f.[logFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType logFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }}) ∧
  (∀ (f : Loc) (Q : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ deferWait (f.[verifyFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType verifyFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }}) ∧
  (∀ (f : Loc) (Q : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     deferWait (f.[leadershipTransferFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType leadershipTransferFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }}) ∧
  (∀ (f : Loc) (Q : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     deferWait (f.[userSnapshotFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType userSnapshotFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }}) ∧
  (∀ (f : Loc) (Q : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     deferWait ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType configurationChangeFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }}) ∧
  (∀ (d : Loc) (Q : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ deferWait d Q }}
    (App (Val (d @!! go.GoType.PointerType deferError.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }})

end spec

end Perennial
