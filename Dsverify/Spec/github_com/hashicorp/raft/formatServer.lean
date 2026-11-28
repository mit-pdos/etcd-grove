/-
`raft.formatServer`'s spec (port P4, 2026-11-27: the fork formats `checkConfiguration`'s error
argument explicitly, #48). Lean-first.
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

/-- `formatServer(server)` returns some string (no panic). -/
abbrev github_com.hashicorp.raft.formatServer.spec : Prop :=
  ∀ (sv : github_com.hashicorp.raft.Server),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
    (App (Val (@! github_com.hashicorp.raft.formatServer)) (Val #sv))
  {{ (str : GoString), RET #str; True }}

end spec

end Perennial
