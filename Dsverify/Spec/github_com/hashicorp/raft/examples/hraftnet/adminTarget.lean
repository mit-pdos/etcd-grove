/-
`hraftnet.adminTarget`'s spec (the hraft kit's orchestrator, notes/dsv-hraft.md, S5g).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.OrchDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]
variable [π : NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet

/-- `adminTarget(conns)`: the server the admin asks, `1 ≤ j ≤ 6` (a `Status` call to a random server,
through its connection `conns[j-1]`, with what the admin knows, `adminCtx`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.adminTarget.spec : Prop :=
  ∀ (K : HK GF) (sl : GoSlice) (ps : List Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        net.rpc.codecSet (hraftCodec (GF := GF)) ∗ adminCtx K ∗ sl ↦*□ ps ∗ ⌜ps.length = 6⌝ ∗
        [∗list] k ↦ p ∈ ps, rpctransport.isConn p K.W (serverAddrs.getD k go!"") }}
      (App (Val (@! adminTarget)) (Val #sl))
    {{ (j : w64), RET #j; ⌜1 ≤ uint.Z j ∧ uint.Z j ≤ 6⌝ }}

end spec

end Perennial
