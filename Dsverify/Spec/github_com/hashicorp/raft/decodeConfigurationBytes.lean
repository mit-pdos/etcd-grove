/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/decodeConfigurationBytes.lean (241f27e).
-/
/-
`raft.decodeConfigurationBytes`'s spec (API-internal, encoding.go): the round trip.
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

/-- `decodeConfigurationBytes(b)` on `encodeServers ss`: the configuration of `ss`, nil. -/
abbrev github_com.hashicorp.raft.decodeConfigurationBytes.spec : Prop :=
  ∀ (b : GoSlice) (ss : List Server) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ b ↦*{dq} encodeServers ss }}
    (App (Val (@! github_com.hashicorp.raft.decodeConfigurationBytes)) (Val #b))
  {{ (c : Configuration), RET (PairV #c #interface.nil); b ↦*{dq} encodeServers ss ∗
      c.Servers' ↦* ss }}

end spec

end Perennial
