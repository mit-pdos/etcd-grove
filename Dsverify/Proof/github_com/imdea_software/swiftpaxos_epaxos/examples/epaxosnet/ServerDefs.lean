/-
The kit's server machines (`kit.go`'s `Server(id)` = `serve(id, ServerAddrs(), Port0)`): the
vocabulary and the specs of its pieces (the lab's `Proof/examples/epaxosnet/Server.lean`, restated
over Net's net/rpc, `RpcHttpHyp` and the RPC layer `NetRpc/`).

* `Register()` (the kit's codec, `rpc_model_gen.go`): from net/rpc's fresh codec state
  (`codecFresh`, a boot resource of the machine: dsv-craq's finding F2) to `codecSet epCodec`.
* `register(ip, port, maddr)` (replica node `k`'s registration with the master, until it is
  ready): `register.spec`, from node `k`'s token and the registration exchange's invariant, the
  replica id `i`, the final list `L` (`L[i] = peerAddrOf k`), `idTok γ i` and replica `i`'s start
  resources (`repStart γ i`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.RpcHttpHyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.KitVals
public import Net.Spec.net.rpc.SetCodec
public import Net.Spec.net.rpc.Client__Close

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

/-- net/rpc's codec state as its initialization leaves it, before the program's `Register()`
(exclusive: a boot resource of the machine, never `|==>`-made). -/
def codecFresh : IProp GF :=
  iprop(sync.isMutex (globalAddr net.rpc.codecMu) net.rpc.codecInv ∗ net.rpc.codecUnset)

/-- `Register()`: the kit's codec registered. -/
theorem wp_Register (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ codecFresh }}
      (App (Val (@! examples.epaxosnet.Register)) (Val #()))
    {{ RET #(); net.rpc.codecSet epCodec }} := by
  unfold codecFresh
  wp_start as ⟨#Hmu, Hun⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$a0»
  ipersist «$a0»
  wp_apply wp_SetCodec epCodec _ $$ [Hun]
  · isplitr
    · iexact Hmu
    isplitl [Hun]
    · iexact Hun
    isplitr
    · unfold net.rpc.codecIs
      iexists _
      iframe «$a0»
      isplitr
      · iapply epCodec_encOk
      isplitr
      · iapply epCodec_decOk
      · iapply epCodec_rcvOk
    · ipureintro; exact Hnn
  iintro #Hcs
  wp_auto
  iapply HΦ
  iexact Hcs

/-- `register(ip, port, maddr)` as replica node `k`'s `serve` calls it. -/
abbrev register.spec [RpcHttpAddr GF] [RpcHttpHyp GF] : Prop :=
  ∀ (γ : EpNames) (W : net.rpc.RpcWorld GF) (k : Nat), k ∈ replicaNodes →
    W.SS masterAddr go!"Master" = some (masterSvc γ) →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ rpcReady ∗ net.rpc.cliEnv ∗
      ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗
      RpcHttpAddr.rpcAddrP W masterAddr (connectReq defaultRPCPath) connectAns ∗
      nodeTok γ k ∗ inv regXN (regXInv γ (repStart γ)) }}
    (App (App (App (Val (@! examples.epaxosnet.register)) (Val #(replicaIp k)))
      (Val #(portOf k))) (Val #masterAddr))
  {{ (id : w64) (sl : GoSlice), RET (PairV #id #sl);
      ∃ L : List GoString, listFinal γ L ∗ sl ↦* L ∗
        ⌜L[uint.nat id]? = some (peerAddrOf k)⌝ ∗
        idTok γ (uint.nat id) ∗ repStart γ (uint.nat id) }}

end specs

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

end Perennial
