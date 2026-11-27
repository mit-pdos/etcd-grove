/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/countingReadCloser__Close.lean (241f27e).
-/
/-
``getSnapshotVersion(v)``'s spec (stage 3, raft-internal, snap: package-internal).
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

/-- `countingReadCloser.Close()` (value receiver): closes its `readCloser`, one that never fails. -/
abbrev github_com.hashicorp.raft.countingReadCloser.Close.spec : Prop :=
  ∀ (cr : Loc) (src : GoInterfaceOk) (R : List w8 → IProp GF) (eof : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ readCloserOk src R eof }}
    (App (Val (countingReadCloser.mk cr (GoInterface.ok src) @!! countingReadCloser.ty @!! go!"Close"))
      (Val #()))
  {{ RET #interface.nil; True }}

end spec

end Perennial
