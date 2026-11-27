/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/EncodeConfiguration.lean (241f27e).
-/
/-
`raft.EncodeConfiguration`'s spec (raft-internal interface, notes/raft-iface.md). The verification fork's encoding (`encodeServers`).
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

/-- `EncodeConfiguration`: The verification fork's encoding (`encodeServers`). -/
abbrev github_com.hashicorp.raft.EncodeConfiguration.spec : Prop :=
  ∀ (c : Configuration) (ss : List Server) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ c.Servers' ↦*{dq} ss }}
    (App (Val (@! github_com.hashicorp.raft.EncodeConfiguration)) (Val #c))
  {{ (b : GoSlice), RET #b; c.Servers' ↦*{dq} ss ∗ b ↦* encodeServers ss }}

end spec

end Perennial
