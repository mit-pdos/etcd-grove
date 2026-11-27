/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/hasVote.lean (241f27e).
-/
/-
`raft.hasVote`'s spec (raft-internal interface, notes/raft-iface.md). On the bootstrap configuration: whether `id` is one of the voters.
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

/-- `hasVote(c, id)` (stage 4; stage 3: on the bootstrap configuration, whether `id` is one of the
fixed voters): on servers with distinct IDs (the first with `id` decides), whether `id` is a voter of
`c`. -/
abbrev github_com.hashicorp.raft.hasVote.spec : Prop :=
  ∀ (c : Configuration) (ss : List Server) (dq : DFrac) (id : ServerID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ c.Servers' ↦*{dq} ss ∗
     ⌜(srvIds ss).Nodup⌝ }}
    (App (App (Val (@! github_com.hashicorp.raft.hasVote)) (Val #c)) (Val #id))
  {{ RET #(decide ((id : List w8) ∈ srvVoters ss)); c.Servers' ↦*{dq} ss }}

end spec

end Perennial
