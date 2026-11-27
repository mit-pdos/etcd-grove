/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/snapstore/Sink__Cancel.lean (241f27e).
-/
/-
`snapstore.Sink.Cancel`'s spec (stage 3, package-internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.snapstore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.examples.snapstore

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

/-- `k.Cancel()`: the sink is closed. -/
abbrev github_com.hashicorp.raft.examples.snapstore.Sink.Cancel.spec : Prop :=
  ∀ (k : Loc) (o : Option (List w8)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗ sinkSt k o }}
      (App (Val (k @!! go.GoType.PointerType Sink.ty @!! go!"Cancel")) (Val #()))
    {{ RET #interface.nil; sinkSt k none }}

end spec

end Perennial
