/-
`rserver.bootConfiguration`'s spec (hraft_robust; the copy in `rserver/helpers.go` of hraftnet's `bootConfiguration`): hraftnet's
`bootConfiguration.spec`, at rserver's package.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ServerDefs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rserver.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rserver.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.hraftnet

/-- `bootConfiguration(n0)`, `n0 ≤ 6`: the configuration of servers `1..n0`, voters
(`bootSrvs`), its servers' slice owned. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rserver.bootConfiguration.spec : Prop :=
  ∀ (n0 : Nat), n0 ≤ 6 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rserver }}
      (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.rserver.bootConfiguration)) (Val #(W64 (n0 : Int))))
    {{ (c : Configuration), RET #c; c.Servers' ↦* bootSrvs n0 }}

end spec

end Perennial
