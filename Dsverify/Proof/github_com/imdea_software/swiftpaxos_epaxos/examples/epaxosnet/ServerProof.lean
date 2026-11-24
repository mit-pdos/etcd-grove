/-
`Server(id)`'s proof (`ServerSpecs.lean`): `ServerAddrs()` (`ServerAddrs.wp_proof`), the master's
branch of `serve` (`serveMaster.wp_proof`: `Register()`, `nodeConfig(1, 7501)` — a configuration
with no leader, given read-only —, `master.New(5, 7501, cfg, &dlog.Logger{})` — the zero logger,
`masterFresh` —, `m.Run()` with the master's machine resources), and `Server.wp_proof`: the
master's branch for `id = 1`, `serveReplica.spec` for a replica node.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServerSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos_epaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open github_com.imdea_software.swiftpaxos_epaxos

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions] [master.Assumptions] [epaxos.Assumptions]
variable [log.Assumptions] [net.http.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

set_option goose.wp.extras true in
theorem ServerAddrs.wp_proof : ServerAddrs.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := GoString) serverAddrs
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  wp_auto
  iapply HΦ
  iexact Hsl

set_option goose.wp.extras true in
theorem serveMaster.wp_proof [RpcHttpAddr GF] [RpcHttpHyp GF]
    (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG))
    (wp_nodeConfig : nodeConfig.spec (GF := GF) (hG := hG))
    (wp_New : master.New.specM (GF := GF))
    (wp_Run : ∀ γ W, Master.Run.specM (GF := GF) γ W) :
    serveMaster.spec (GF := GF) (hG := hG) := by
  intro γ W sl
  wp_start as ⟨Hcf, Hmux, #Hds, #Hsrv, #Hde, %Hb, %HSS, Hmr⟩
  wp_auto
  wp_apply (wp_Register wp_SetCodec) $$ [$Hcf] as #Hcs
  wp_apply wp_nodeConfig as %cfg ⟨%c, Hcfg, -, %Hc⟩
  rw [show (W64 7500 + W64 1 : w64) = W64 7501 from rfl]
  ipersist Hcfg
  ipersist «$a3»
  ihave #Hmpkg : isPkgInit (PROP := IProp GF)
    pkg_id.github_com.imdea_software.swiftpaxos_epaxos.master $$ []
  · iPkgInit
  wp_apply wp_New cfg «$a3_ptr» c $$ [$Hmpkg $Hcfg] as %m Hm
  · isplitr
    · ipureintro; exact Hc.2.2.2
    iexact «$a3»
  ihave #Hhttp : isPkgInit (PROP := IProp GF) pkg_id.net.http $$ []
  · iPkgInit
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.net.rpc $$ []
  · iPkgInit
  unfold masterRes masterLis hsReq hsAns
  icases Hmr with ⟨HlU, #Hml, #Hrr, -⟩
  wp_apply wp_Run γ W m cfg «$a3_ptr» $$ [$Hmpkg $Hhttp $Hm $HlU $Hmux $Hds $Hsrv $Hde]
  · isplitr
    · ipureintro; exact HSS
    isplitr
    · iexact Hml
    isplitr
    · unfold replicaRpcs; iexact Hrr
    isplitr
    · unfold rpcReady; iframe #
    ipureintro; exact Hb
  iapply HΦ; itrivial

set_option goose.wp.extras true in
theorem Server.wp_proof [RpcHttpAddr GF] [RpcHttpHyp GF]
    (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG))
    (wp_nodeConfig : nodeConfig.spec (GF := GF) (hG := hG))
    (wp_New : master.New.specM (GF := GF))
    (wp_Run : ∀ γ W, Master.Run.specM (GF := GF) γ W)
    (wp_serveReplica : serveReplica.spec (GF := GF) (hG := hG)) :
    Server.spec (GF := GF) (hG := hG) := by
  intro γ W id h1 h6
  wp_start as ⟨Hcf, Hmux, #Hds, #Hsrv, #Hde, %Hb, Hres⟩
  wp_auto
  wp_apply ServerAddrs.wp_proof as %sl #Hsl
  unfold Port0 serverRes
  icases Hres with ⟨%HSS, Hres⟩
  by_cases hid : uint.nat id = 1
  · have hid' : id = W64 1 := by word
    subst hid'
    simp only [hid, ↓reduceIte]
    wp_apply serveMaster.wp_proof wp_SetCodec wp_nodeConfig wp_New wp_Run γ W sl
      $$ [$Hpkg $Hcf $Hmux $Hds $Hsrv $Hde $Hres]
    · iframe; ipureintro; exact ⟨Hb, HSS⟩
    iapply HΦ; itrivial
  · simp only [hid, ↓reduceIte]
    have hk : uint.nat id ∈ replicaNodes := by
      simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false]; omega
    have hidw : W64 ((uint.nat id : Nat) : Int) = id := by word
    have hS := wp_serveReplica γ W (uint.nat id) sl hk
    rw [hidw] at hS
    unfold replicaRes hsReq hsAns
    icases Hres with ⟨Hnt, #Hrx, #Hci, #Hma, #Hlis, -⟩
    wp_apply hS $$ [$Hpkg $Hcf $Hmux $Hds $Hsrv $Hde $Hsl $Hma $Hlis $Hnt $Hrx $Hci]
    · ipureintro; exact ⟨Hb, HSS⟩
    iapply HΦ; itrivial

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

end Perennial
