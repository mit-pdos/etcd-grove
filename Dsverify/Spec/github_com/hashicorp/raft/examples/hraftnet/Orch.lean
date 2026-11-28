/-
`hraftnet.Orch`'s spec (the hraft kit's orchestrator, notes/dsv-hraft.md, S5g).
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
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft.examples.hraftnet

/-- `Orch()`: the orchestrator machine (its share of the start, `orchShare K γp`, and net/rpc's codec
unregistered): draws the first configuration's size and sends it to the servers (`kit_draw`,
`configure`), registers the codec, starts the admin, then remote's `Check` of the clients'
operations; it returns (porcupine accepts the history). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.Orch.spec : Prop :=
  ∀ (K : HK GF) (γp : github_com.mit_pdos.etcd_grove.examples.lib.remote.PendNames),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ∗
        isPkgInit (PROP := IProp GF) pkg_id.sync ∗
        sync.isMutex (globalAddr net.rpc.codecMu) (net.rpc.codecInv (GF := GF)) ∗ net.rpc.codecUnset ∗
        orchShare K γp }}
      (App (Val (@! Orch)) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
