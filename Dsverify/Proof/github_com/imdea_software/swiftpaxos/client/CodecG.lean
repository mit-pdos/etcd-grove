/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/CodecG.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client's frozen `Connect`/`Disconnect` statements over a codec `C` (decision D6,
HUB-REQUEST 2; Proof/swiftnet/KitLike.lean): the frozen texts with the section's codec `C` in
place of the kit's `kitCodec` (their rpc client, `net.rpc.isClient`, and `kitCodecOk` depend on
it). At `C := kitCodec` they are the frozen statements (`failed_of_G`); the link uses them at
`examples.swiftnet.kitCodecC`, whose `kitCodecOk` holds.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Connect
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Disconnect
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitLike

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace client

section failed
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [C : net.rpc.RpcCodec netDistGF]

/-- `client.failed` (Spec/client/Defs.lean) over the codec `C`. -/
def failedG (b : Loc) : IProp netDistGF :=
  iprop(∃ (bv : client.BufferClient) (v : client.Client), b ↦□ bv ∗ bv.Client' ↦ v ∗
    dlog.quiet v.Logger' ∗ ⌜bv.Client' ≠ null⌝ ∗
    (⌜v.master' = null⌝ ∨ ∃ (W : net.rpc.RpcWorld netDistGF) (a : GoString),
      net.rpc.isClient v.master' W a) ∗
    ∃ srvs : List GoInterface, v.servers' ↦* srvs ∗
      [∗list] s ∈ srvs, ⌜s = interface.nil⌝ ∨ ∃ c side, net.rpc.connIface s c side)

theorem failedG_unfold (b : Loc) :
    failedG b ⊣⊢ iprop(∃ (bv : client.BufferClient) (v : client.Client), b ↦□ bv ∗ bv.Client' ↦ v ∗
    dlog.quiet v.Logger' ∗ ⌜bv.Client' ≠ null⌝ ∗
    (⌜v.master' = null⌝ ∨ ∃ (W : net.rpc.RpcWorld netDistGF) (a : GoString),
      net.rpc.isClient v.master' W a) ∗
    ∃ srvs : List GoInterface, v.servers' ↦* srvs ∗
      [∗list] s ∈ srvs, ⌜s = interface.nil⌝ ∨ ∃ c side, net.rpc.connIface s c side) := by
  unfold failedG; exact .rfl

end failed

/-- At the kit's codec, `failedG` is the frozen `failed`. -/
theorem failed_of_G [go_gctx : GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF]
    [sem : go.Semantics] [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
    (b : Loc) : failedG (C := kitCodec) b ⊣⊢ client.failed b := by
  exact (failedG_unfold b).trans (failed_unfold b).symm

end client

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [client.Assumptions] [examples.swiftnet.Assumptions]
variable [C : net.rpc.RpcCodec netDistGF]

/-- The frozen `client.BufferClient.Connect.spec` over the codec `C`. -/
abbrev client.BufferClient.Connect.specG : Prop :=
  ∀ (b : Loc) (cid : w32) (maddr : GoString) (mport : w64) (W : net.rpc.RpcWorld netDistGF)
    (γ : sp.Names) (γc γm γl : GName),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.bufFresh b cid maddr mport ∗ ⌜sp.addrPort maddr mport = masterAddr⌝ ∗
      net.rpc.rpcAddr W masterAddr ∗ ⌜W.SS masterAddr go!"Master" = some (sp.masterSpec γc γm)⌝ ∗
      net.rpc.codecSet net.rpc.RpcCodec.spec ∗ net.rpc.kitCodecOk ∗
      ([∗list] a ∈ replicaAddrs, addrProto a (sp.inP γ γc γm) (sp.outQ γ γc γm)) ∗
      sp.inv γ γc γm γl }}
    (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"Connect")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ N : Nat, client.connected b γ γc γm cid N) ∨
      (⌜err ≠ interface.nil⌝ ∗ client.failedG b) }}

end spec

section frozen
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [client.Assumptions] [examples.swiftnet.Assumptions]

/-- The frozen `Connect` statement from its form at `kitCodec`. -/
theorem client.BufferClient.Connect.spec_of_G
    (h : client.BufferClient.Connect.specG (C := kitCodec)) :
    client.BufferClient.Connect.spec (hG := hG) := by
  intro b cid maddr mport W γ γc γm γl
  iintro %Φ Hpre HΦ
  iapply h b cid maddr mport W γ γc γm γl $$ Hpre
  iintro !> %err Hpost
  iapply HΦ
  icases Hpost with (Hok | ⟨%Herr, Hf⟩)
  · ileft; iexact Hok
  · iright
    isplitr
    · ipureintro; exact Herr
    iapply (client.failed_of_G b).1 $$ Hf

end frozen

section disconnect
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [client.Assumptions]
variable [C : net.rpc.RpcCodec netDistGF]

/-- The frozen `client.BufferClient.Disconnect.spec` over the codec `C`. -/
abbrev client.BufferClient.Disconnect.specG : Prop :=
  ∀ (b : Loc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.failedG b }}
    (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"Disconnect"))
      (Val #()))
  {{ RET #(); True }}

end disconnect

section disconnectFrozen
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [client.Assumptions]

/-- The frozen `Disconnect` statement from its form at `kitCodec`. -/
theorem client.BufferClient.Disconnect.spec_of_G
    (h : client.BufferClient.Disconnect.specG (C := kitCodec)) :
    client.BufferClient.Disconnect.spec (hG := hG) := by
  intro b
  iintro %Φ ⟨Hpkg, Hf⟩ HΦ
  iapply h b $$ [Hpkg Hf] HΦ
  iframe Hpkg
  iapply (client.failed_of_G b).2 $$ Hf

end disconnectFrozen

end Perennial.github_com.imdea_software.swiftpaxos
