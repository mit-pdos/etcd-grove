/-
`hraftnet.remoteCheck`'s spec (the hraft kit's orchestrator, notes/dsv-hraft.md, S5g).
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
variable [ρ : github_com.mit_pdos.etcd_grove.examples.lib.remote.RemoteGS]

open github_com.hashicorp.raft.examples.hraftnet

open github_com.mit_pdos.etcd_grove.examples.lib.remote

/-- `remoteCheck(ops)`, `1 ≤ ops ≤ 2 ^ 20`: remote's `Check` of the five clients' operations, `ops`
each, against the register's porcupine model (`Model()`, `regS`) of the far side's store
`regR g`; it returns (porcupine accepts the history). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.remoteCheck.spec : Prop :=
  ∀ (g : GName) (γp : PendNames) (ops : w64), 1 ≤ uint.Z ops → uint.Z ops ≤ 2 ^ 20 →
    receiptBound GF ≤ 2 ^ 63 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ∗
        ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (regR g) a) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := HIn) ∗
        pendCtx (Gg := hG.goose_globalGS) (regR g) (regS (GF := GF)) γp ∗
        pendLib (Gg := hG.goose_globalGS) (regS (GF := GF)) γp (regS (GF := GF)).M.init ∗
        [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a orchBud }}
      (App (Val (@! remoteCheck)) (Val #ops))
    {{ RET #(); True }}

end spec

end Perennial
