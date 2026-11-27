/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/DefaultConfig.lean (241f27e).
-/
/-
`raft.DefaultConfig`'s spec (raft-internal interface, notes/raft-iface.md). A fresh `*Config` holding the defaults.
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

/-- `DefaultConfig`: A fresh `*Config` holding the defaults. -/
abbrev github_com.hashicorp.raft.DefaultConfig.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
    (App (Val (@! github_com.hashicorp.raft.DefaultConfig)) (Val #()))
  {{ (p : Loc), RET #p; p ↦ defaultConfig }}

end spec

end Perennial
