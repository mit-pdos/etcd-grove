/-
The server machines' resources and specs (`kit.go`'s `serve(id, addrs)`, `Server(id)`), over
the kit over remote (`ServeProof.lean` proves them):

* `srvBoot γ i`: server node `i + 1`'s boot resources: net/rpc's fresh codec state
  (`codecFresh`), the dialer's state (`cliBoot`), the server's (`net.rpc.srvEnv`, the thread
  bound), net/http's `muxOwner []`, net/rpc's `DefaultServer` with an owned, empty registry
  (`defaultServerO γs γf ∗ svcOwn γf ∅`), the main thread's token (`http.Serve` runs on it), and on
  a replica node the node's fresh ghost (`client.ghostFresh`) and the mutable globals' points-to
  (`swift.mutGlobals`);
* `serverRes γ i`: its share and its boot resources.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Pkg

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

/-- Server node `i + 1`'s boot resources (see the file header). -/
def srvBoot (i : Nat) : IProp netDistGF :=
  iprop(cnode.codecFresh ∗ cnode.cliBoot ∗ ⌜threadBound netDistGF ≤ 2 ^ 31⌝ ∗ net.rpc.srvEnv ∗
    muxOwner [] ∗ (∃ γs γf, net.rpc.defaultServerO γs γf ∗ net.rpc.svcOwn γf ∅) ∗ threadTok ∗
    (if i = 0 then iprop(True) else client.ghostFresh ∗ swift.mutGlobals))

/-- Server node `i + 1`'s start: its share and its boot resources. -/
def serverRes (γ : SwiftNames netDistGF) (i : Nat) : IProp netDistGF :=
  iprop(serverShare γ i ∗ srvBoot i)

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions]
variable [examples.swiftnet.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- `serve(id, addrs)` on server node `id = i + 1`: returns only on the master node, after
`Run` (on a listener error). -/
abbrev serve.spec (γ : SwiftNames netDistGF) (i : Nat) : Prop :=
  ∀ (asl : GoSlice),
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ asl ↦* addrs ∗ serverRes γ i }}
    (App (App (Val (@! examples.swiftnet.serve)) (Val #(W64 ((i + 1 : Nat) : Int)))) (Val #asl))
  {{ RET #(); True }}

/-- `Server(id)`: server machine `id = i + 1` (`i < 6`). -/
abbrev Server.spec : Prop :=
  ∀ (γ : SwiftNames netDistGF) (i : Nat), i < 6 →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ serverRes γ i }}
    (App (Val (@! examples.swiftnet.Server)) (Val #(W64 ((i + 1 : Nat) : Int))))
  {{ RET #(); True }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
