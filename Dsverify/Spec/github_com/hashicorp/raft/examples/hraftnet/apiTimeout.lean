/-
`hraftnet.apiTimeout`'s spec (the hraft kit, notes/dsv-hraft.md, S5f).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet

/-- `apiTimeout()`: a duration (`APITimeoutMs` milliseconds). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.apiTimeout.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet }}
    (App (Val (@! apiTimeout)) (Val #()))
  {{ (d : w64), RET #d; True }}

end spec

end Perennial
