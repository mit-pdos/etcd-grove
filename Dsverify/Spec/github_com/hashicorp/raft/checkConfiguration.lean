/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/checkConfiguration.lean (241f27e).
-/
/-
`raft.checkConfiguration`'s spec (API-internal): a well-formed bootstrap configuration passes.
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

/-- `checkConfiguration(c)` (stage 4; stage 3: only all-voter configurations, accepted): on servers
with non-empty, pairwise distinct IDs, each its own address: `nil` if there is a voter, else an error
(`fmt.Errorf("need at least one voter in configuration: %v", configuration)`: `nextConfiguration`
refusing a change that leaves no voter, reachable in hr3). -/
abbrev github_com.hashicorp.raft.checkConfiguration.spec : Prop :=
  ∀ (c : Configuration) (ss : List Server) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ c.Servers' ↦*{dq} ss ∗
     ⌜(∀ s ∈ ss, s.Address' = s.ID' ∧ s.ID' ≠ []) ∧ (srvIds ss).Nodup⌝ }}
    (App (Val (@! github_com.hashicorp.raft.checkConfiguration)) (Val #c))
  {{ (err : GoInterface), RET #err; c.Servers' ↦*{dq} ss ∗
      (⌜err = interface.nil ∧ srvVoters ss ≠ []⌝ ∨ ⌜srvVoters ss = []⌝ ∗ errOk err ∗
        ⌜∃ x : Loc, err = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x⌝) }}

end spec

end Perennial
