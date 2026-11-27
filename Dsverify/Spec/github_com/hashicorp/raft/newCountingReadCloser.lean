/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/newCountingReadCloser.lean (241f27e).
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

/-- `newCountingReadCloser(rc)`: a fresh `*countingReadCloser` (read-only from now on) whose embedded
`*countingReader` reads `rc` and whose `readCloser` is `rc`. -/
abbrev github_com.hashicorp.raft.newCountingReadCloser.spec : Prop :=
  ∀ (rc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
    (App (Val (@! github_com.hashicorp.raft.newCountingReadCloser)) (Val #rc))
  {{ (crc : Loc), RET #crc; ∃ cr : Loc, crc ↦□ countingReadCloser.mk cr rc ∗ countingReaderIs cr rc }}

end spec

end Perennial
