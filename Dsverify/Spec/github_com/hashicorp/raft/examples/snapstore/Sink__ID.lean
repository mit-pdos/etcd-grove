/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/snapstore/Sink__ID.lean (241f27e).
-/
/-
`snapstore.Sink.ID`'s spec (stage 3, package-internal).
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

/-- `k.ID()`: the sink's id. -/
abbrev github_com.hashicorp.raft.examples.snapstore.Sink.ID.spec : Prop :=
  ∀ (k st : Loc) (γ : GName) (eof : GoInterface) (id : GoString) (ver idx term cfgIdx : w64)
    (cfg : Configuration),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗ sinkCore k st γ eof id ver idx term cfgIdx cfg }}
      (App (Val (k @!! go.GoType.PointerType Sink.ty @!! go!"ID")) (Val #()))
    {{ RET #id; True }}

end spec

end Perennial
