/-
`rserver.peers`'s spec (hraft_robust; the copy in `rserver/helpers.go` of hraftnet's `peers`): hraftnet's
`peers.spec`, at rserver's package.
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

open github_com.hashicorp.raft.examples.hraftnet

/-- `peers()`: a new map of every server's raft address to its net/rpc address (`peersUpTo 6`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rserver.peers.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rserver }}
    (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.rserver.peers)) (Val #()))
  {{ (m : Loc), RET #m; m ↦$ peersUpTo 6 }}

end spec

end Perennial
