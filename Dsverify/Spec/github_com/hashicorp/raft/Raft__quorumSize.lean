/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__quorumSize.lean (241f27e).
-/
/-
`raft.(*Raft).quorumSize`'s spec (main goroutine; internal to MAIN-C). On the bootstrap
configuration (all servers voters): a majority of the voters.
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

/-- `(*Raft).quorumSize()`: `len(voters)/2 + 1` for the voters of the latest configuration `ss`
(stage 4; stage 3: of the fixed voters). -/
abbrev github_com.hashicorp.raft.Raft.quorumSize.spec : Prop :=
  ∀ (r : Loc) (ccfg cfg : Configuration) (cidx li : w64) (ss : List Server) (dq dq' : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
      r.[Raft, go!"configurations"] ↦{dq} configurations.mk ccfg cidx cfg li ∗ cfg.Servers' ↦*{dq'} ss ∗
      ⌜ss.length < 2 ^ 63⌝ }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"quorumSize")) (Val #()))
  {{ RET #(W64 ((srvVoters ss).length / 2 + 1 : Nat));
      r.[Raft, go!"configurations"] ↦{dq} configurations.mk ccfg cidx cfg li ∗ cfg.Servers' ↦*{dq'} ss }}

end spec

end Perennial
