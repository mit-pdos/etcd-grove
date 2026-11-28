/-
`rserver.serverID`'s spec (hraft_robust; the copy in `rserver/helpers.go` of hraftnet's `serverID`): hraftnet's
`serverID.spec`, at rserver's package.
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

/-- `serverID(s)`: server `s`'s raft ID, its number in decimal (`sidOf`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rserver.serverID.spec : Prop :=
  ∀ (s : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rserver }}
      (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.rserver.serverID)) (Val #s))
    {{ RET #(sidOf s); True }}

end spec

end Perennial
