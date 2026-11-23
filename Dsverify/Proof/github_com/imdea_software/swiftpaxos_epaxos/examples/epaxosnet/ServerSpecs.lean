/-
The kit's server machines, whole (`kit.go`'s `Server(id)` = `serve(id, ServerAddrs(), Port0)`):

* `ServerAddrs()` (`ServerAddrs.spec`): a fresh slice of `serverAddrs`, given read-only;
* `serverRes γ W id`: what server machine `id` gets from the start (`Start.lean`'s `ep_start`):
  `⌜W.SS = rpcSS γ⌝` (the rpc world's services; `ep_start` gives it once, as a pure fact, for
  every machine) and, for the master (`id = 1`), `masterRes γ W`, for a replica node
  (`id ∈ replicaNodes`), `replicaRes γ W id`;
* `serve(1, sl, 7500)` (`serveMaster.spec`): the master's branch (`Register()`, `nodeConfig`,
  `master.New`, `Run`);
* `Server(id)` (`Server.spec`): server `id` (1..6) from its machine's boot resources (net/rpc's
  fresh codec, the unclaimed `DefaultServeMux`, net/rpc's server variables, the bounds) and
  `serverRes`. It returns only on a registration, listen or serve error.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServeDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Start
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos_epaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open github_com.imdea_software.swiftpaxos_epaxos

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions] [master.Assumptions] [epaxos.Assumptions]
variable [log.Assumptions] [net.http.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

local notation "kpkg" => pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

/-- `ServerAddrs()`: a fresh slice of the server addresses (given read-only). -/
abbrev ServerAddrs.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! examples.epaxosnet.ServerAddrs)) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦*□ serverAddrs }}

/-- Server machine `id`'s resources from the start (`ep_start`): the rpc world's services and the
master's (`id = 1`) or replica node `id`'s machine resources. -/
def serverRes [RpcHttpAddr GF] (γ : EpNames) (W : net.rpc.RpcWorld GF) (id : Nat) : IProp GF :=
  iprop(⌜W.SS = rpcSS γ⌝ ∗ if id = 1 then masterRes γ W else replicaRes γ W id)

/-- `serve(1, sl, 7500)`, the master's branch: from net/rpc's fresh codec, the unclaimed
`DefaultServeMux`, net/rpc's server variables, the bounds, the rpc world (`rpcSS γ`) and the
master's machine resources. It returns only if `Run` does (a registration, listen or serve
error). -/
abbrev serveMaster.spec [RpcHttpAddr GF] [RpcHttpHyp GF] : Prop :=
  ∀ (γ : EpNames) (W : net.rpc.RpcWorld GF) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ codecFresh ∗ RpcHttpHyp.muxOwner [] ∗
      net.rpc.srvEnv ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
      ⌜W.SS = rpcSS γ⌝ ∗ masterRes γ W }}
    (App (App (App (Val (@! examples.epaxosnet.serve)) (Val #(W64 1))) (Val #sl))
      (Val #(W64 7500)))
  {{ RET #(); True }}

/-- `Server(id)` for server `id` (1: the master, 2..6: the replica nodes): from the machine's boot
resources (net/rpc's fresh codec, the unclaimed `DefaultServeMux`, net/rpc's server variables, the
bounds of the threads and of the receipts) and its resources from the start (`serverRes`). -/
abbrev Server.spec [RpcHttpAddr GF] [RpcHttpHyp GF] : Prop :=
  ∀ (γ : EpNames) (W : net.rpc.RpcWorld GF) (id : w64), 1 ≤ uint.nat id → uint.nat id ≤ 6 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ codecFresh ∗ RpcHttpHyp.muxOwner [] ∗
      net.rpc.srvEnv ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
      serverRes γ W (uint.nat id) }}
    (App (Val (@! examples.epaxosnet.Server)) (Val #id))
  {{ RET #(); True }}

end specs

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

end Perennial
