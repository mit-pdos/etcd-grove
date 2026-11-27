/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/newCountingReader.lean (241f27e).
-/
/-
``newCountingReader(rd)``'s spec (stage 3, raft-internal, snap: package-internal).
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

/-- `newCountingReader(rd)`: a fresh `*countingReader` over `rd`. -/
abbrev github_com.hashicorp.raft.newCountingReader.spec : Prop :=
  ∀ (rd : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
    (App (Val (@! github_com.hashicorp.raft.newCountingReader)) (Val #rd))
  {{ (cr : Loc), RET #cr; countingReaderIs cr rd }}

end spec

end Perennial
