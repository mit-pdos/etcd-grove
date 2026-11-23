/-
The EPaxos kit's client machines and orchestrator: their specs (kit.go's `Client(c)`, `Orch()`), in
paxos's shape (`paxosnet/Kit.lean`) over remote's `ServeClient`/`Check` and the far side's store
`epR γ` (`Kit.lean`). A defs module: `ClientProof.lean` proves them, the top level uses them.

* `Client(c)`: client machine `c < 10`, from the replicas' shared facts its `Op` needs
  (`clientInvs γ`), remote's protocol of its address (`remoteAddr (epR γ)`) and remote's map of
  inputs (`mapCtx`); it never returns.
* `Orch()`: the orchestrator, from remote's protocols of the client machines' addresses, the map
  of inputs and the pending library's invariant over porcupine's model `epS0`; it returns
  (porcupine accepts the history).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Kit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote
  github_com.imdea_software.swiftpaxos_epaxos github_com.imdea_software.swiftpaxos_epaxos.kvs

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Assumptions]
variable [π : NetProtoGS]

local notation "kpkg" => pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

/-- `Client(c)`: client machine `c` (`c < NC = 10`); it never returns. -/
abbrev Client.spec [RemoteGS] : Prop :=
  ∀ (γ : EpNames) (c : w64), uint.nat c < 10 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ clientInvs γ ∗
      remoteAddr (Gg := hG.goose_globalGS) (epR γ) (clientAddrs.getD (uint.nat c) []) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := EIn) }}
    (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Client)) (Val #c))
  {{ RET #(); False }}

/-- `Orch()`: the orchestrator; it returns (porcupine accepts the history). -/
abbrev Orch.spec [RemoteGS] : Prop :=
  ∀ (γ : EpNames) (γp : PendNames), receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗
      ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (epR γ) a) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := EIn) ∗
      pendCtx (Gg := hG.goose_globalGS) (epR γ) (epS0 (GF := GF)) γp ∗
      pendLib (Gg := hG.goose_globalGS) (epS0 (GF := GF)) γp (epS0 (GF := GF)).M.init ∗
      [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a 6 }}
    (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Orch)) (Val #()))
  {{ RET #(); True }}

end specs

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
