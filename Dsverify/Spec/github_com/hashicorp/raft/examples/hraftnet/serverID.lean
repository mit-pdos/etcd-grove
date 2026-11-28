/-
`hraftnet.serverID`'s spec (the hraft kit, notes/dsv-hraft.md, S5d).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ServerDefs
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

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.hraftnet

/-- `serverID(s)`: server `s`'s raft ID, its number in decimal (`sidOf`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.serverID.spec : Prop :=
  ∀ (s : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet }}
      (App (Val (@! serverID)) (Val #s))
    {{ RET #(sidOf s); True }}

end spec

end Perennial
