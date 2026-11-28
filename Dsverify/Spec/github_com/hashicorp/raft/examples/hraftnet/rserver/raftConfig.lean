/-
`rserver.raftConfig`'s spec (hraft_robust; the copy in `rserver/helpers.go` of hraftnet's `raftConfig`): hraftnet's
`raftConfig.spec`, at rserver's package.
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

/-- `raftConfig(id)`: a configuration raft runs with as server `sidOf id` (`cfgOk`: what
`ValidateConfig` accepts and the verified scope; its random options are any of the drawn ones). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rserver.raftConfig.spec : Prop :=
  ∀ (id : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rserver }}
      (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.rserver.raftConfig)) (Val #id))
    {{ (p : Loc), RET #p; ∃ c : Config, p ↦ c ∗ ⌜cfgOk c (sidOf id)⌝ }}

end spec

end Perennial
