/-
`raft.formatConfiguration`'s spec (port P4, 2026-11-27: the fork formats `checkConfiguration`'s
error argument explicitly, #48). Lean-first.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `formatConfiguration(c)` reads `c.Servers` (lent at `dq`, given back) and returns some
string (no panic). -/
abbrev github_com.hashicorp.raft.formatConfiguration.spec : Prop :=
  ∀ (c : github_com.hashicorp.raft.Configuration) (ss : List github_com.hashicorp.raft.Server) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ c.Servers' ↦*{dq} ss }}
    (App (Val (@! github_com.hashicorp.raft.formatConfiguration)) (Val #c))
  {{ (str : GoString), RET #str; c.Servers' ↦*{dq} ss }}

end spec

end Perennial
