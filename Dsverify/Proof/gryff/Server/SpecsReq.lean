/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/SpecsReq.lean (run gryff-bump-1,
lab master 915f964; notes/dsv-gryff.md).

The server specs over the nodes' shares (`Shares.lean`): each is the internal spec with what a
node's share gives (the rpc listeners' protocols `rpcLises`, hence each rpc address's `rpcAddrP`,
`rpcLisP_addr`; the start's `masterStartRes` / `replicaRegRes`), proved from the internal specs
(`wp_NewMaster'`, `wp_Master_Serve'`, `wp_RegisterWithMaster'`, `wp_Serve'`). Net's specs and the
codec's laws are premises (discharged at linking).
-/
module

public import Dsverify.Proof.gryff.Server.SpecsDefs
public import Dsverify.Proof.gryff.Server.MasterBoot
public import Dsverify.Proof.gryff.Server.RegisterProof
public import Dsverify.Proof.gryff.Server.ServeProof

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [mA : gryff.src.masterlib.Assumptions] [sA : gryff.src.serverlib.Assumptions]
variable [kA : examples.gryffnet.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [H : RpcHttpHyp GF]
variable [nS : netN.NetSpecs GF]
variable (L : CodecLaws (GF := GF)) (RL : RcvLaws (GF := GF))
variable (wp_Call : net.rpc.Client.Call.spec (GF := GF) (hG := hG))
variable (wp_DialHTTP : net.rpc.DialHTTP.spec (GF := GF) (hG := hG))

omit mA sA kA nS in
theorem masterRpcAddr_lis : lisAccepts masterRpcLis masterRpcAddr ∧ addrOk masterRpcAddr = true :=
  ⟨lisAcceptsB_iff.1 (by decide), by decide⟩

omit mA sA kA nS in
theorem replicaRpcAddr_ok (k : Nat) (hk : k < 3) : addrOk (replicaRpcAddr k) = true := by
  rcases k with _|_|_|k
  · decide
  · decide
  · decide
  · omega

omit mA sA kA nS in
/-- The rpc addresses a node dials, from its share's listeners' protocols. -/
theorem rpcAddrs_of_share (γ : GryffNames GF) :
    rpcLises γ ⊢ net.rpc.rpcAddrP (Gg := hG.goose_globalGS) γ.rpc masterRpcAddr
        (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns ∗
      □ [∗list] k ∈ [0, 1, 2], replicaRpcOk γ k := by
  unfold rpcLises
  iintro #⟨Hm, Hrs⟩
  ihave ⟨#H0, #Hrs⟩ := BigSepL.bigSepL_cons.1 $$ Hrs
  ihave ⟨#H1, #Hrs⟩ := BigSepL.bigSepL_cons.1 $$ Hrs
  ihave ⟨#H2, -⟩ := BigSepL.bigSepL_cons.1 $$ Hrs
  isplitr
  · iapply H.rpcLisP_addr _ _ _ _ _ masterRpcAddr_lis.2 masterRpcAddr_lis.1 $$ Hm
  iintro !>
  unfold replicaRpcOk
  iapply BigSepL.bigSepL_cons.2
  isplitr
  · iapply H.rpcLisP_addr _ _ _ _ _ (replicaRpcAddr_ok 0 (by decide))
      (replicaRpcAddr_lis 0 (by decide)).1 $$ H0
  iapply BigSepL.bigSepL_cons.2
  isplitr
  · iapply H.rpcLisP_addr _ _ _ _ _ (replicaRpcAddr_ok 1 (by decide))
      (replicaRpcAddr_lis 1 (by decide)).1 $$ H1
  iapply BigSepL.bigSepL_cons.2
  isplitr
  · iapply H.rpcLisP_addr _ _ _ _ _ (replicaRpcAddr_ok 2 (by decide))
      (replicaRpcAddr_lis 2 (by decide)).1 $$ H2
  iapply BigSepL.bigSepL_nil.2
  iempintro

theorem Master.Serve.wp_req (γ : GryffNames GF) (m : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.masterlib ∗ masterOk γ m }}
      (App (Val (m @!! go.GoType.PointerType gryff.src.masterlib.Master.ty @!! go!"Serve"))
        (Val #()))
    {{ RET #(); True }} := by
  unfold masterOk
  exact wp_Master_Serve' γ m

include L RL wp_Call wp_DialHTTP in
theorem NewMaster.wp_req (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.masterlib ∗ □ sharedInvs γ ∗ netShare γ ∗
        masterStartRes γ ∗ net.rpc.codecSet gryffCodec ∗ net.rpc.srvEnv ∗
        H.muxFree net.rpc.defaultRPCPath ∗ dialEnv (GF := GF) ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http }}
      (App (App (Val (@! gryff.src.masterlib.NewMaster)) (Val #(W64 3))) (Val #(W64 7501)))
    {{ (m : Loc), RET #m; masterOk γ m }} := by
  iintro %Φ ⟨#Hpkg, #Hinv, #Hsh, Hstart, #Hcs, #Hse, Hmux, #Hde, %Hth, #Hkit, #Hrpc, #Hhttp⟩ HΦ
  unfold masterStartRes deployStartDef
  icases Hstart with ⟨Hreg, #Hdep, %Hw⟩
  unfold netShare
  icases Hsh with ⟨-, #Hrl⟩
  ihave ⟨-, #Hras⟩ := rpcAddrs_of_share γ $$ Hrl
  ihave #Hrlm : H.rpcLisP γ.rpc masterRpcLis (net.rpc.connectReq net.rpc.defaultRPCPath)
      net.rpc.connectAns $$ [Hrl]
  · unfold rpcLises; iintro; icases Hrl with ⟨#Hm, -⟩; iexact Hm
  unfold sharedInvs protoInvs
  icases Hinv with ⟨⟨#Hg, -⟩, -⟩
  iapply (wp_NewMaster' L RL wp_Call wp_DialHTTP γ) $$ [Hmux Hreg]
  · iframe
    iframe #
    ipureintro; exact ⟨Hw, Hth⟩
  inext
  iintro %m Hm
  iapply HΦ
  unfold masterOk
  iexact Hm

include L wp_Call wp_DialHTTP in
theorem RegisterWithMaster.wp_req (γ : GryffNames GF) (k : Nat) (ws : List w64) (hk : k < 3) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.serverlib ∗ netShare γ ∗
        replicaRegRes γ k ∗ predIs γ.proto k ws ∗ net.rpc.codecSet gryffCodec ∗
        dialEnv (GF := GF) }}
      (App (App (App (Val (@! gryff.src.serverlib.RegisterWithMaster)) (Val #(ipOf k)))
        (Val #(portNum k))) (Val #masterRpcAddr))
    {{ (id : w64) (sl : GoSlice) (nodes : List GoString), RET (PairV #id #sl);
        sl ↦* nodes ∗ registeredAs γ k id nodes }} := by
  iintro %Φ ⟨#Hpkg, #Hsh, Hrr, #Hpi, #Hcs, #Hde⟩ HΦ
  unfold replicaRegRes deployRegResDef
  icases Hrr with ⟨#Hdep, %Hw⟩
  ihave #Hcar : regCarry γ.proto k $$ []
  · unfold regCarry; iexists ws; iexact Hpi
  unfold netShare
  icases Hsh with ⟨-, #Hrl⟩
  ihave ⟨#Hra, -⟩ := rpcAddrs_of_share γ $$ Hrl
  have hW : γ.rpc.SS masterRpcAddr go!"Master" = some (masterSvc γ.deploy (regCarry γ.proto)) := by
    rw [Hw.1]; unfold rpcServicesDef; rw [if_pos ⟨masterRpcAddr_lis.1, rfl⟩]
  iapply (wp_RegisterWithMaster' L wp_Call wp_DialHTTP γ k hk hW) $$ []
  · iframe #
  inext
  iintro %id %sl %nodes ⟨Hsl, #Hr, #Hid, #Hps, #Hrp⟩
  iapply HΦ
  iframe
  unfold registeredAs registeredAsDef
  iframe #
  ipureintro; exact hk

theorem Serve.wp_req (γ : GryffNames GF) (k : Nat) (port : w64) (γs : GName) (hk : k < 3)
    (hport : sint.Z port = 8502 + k) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.serverlib ∗ netShare γ ∗
        net.rpc.codecSet gryffCodec ∗ net.rpc.srvEnv ∗ H.muxFree net.rpc.defaultRPCPath ∗
        H.defaultServer γs ∗ net.rpc.svcReg γs gryffCodec go!"Replica" replicaSvc ∗
        replicaRegRes γ k ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ }}
      (App (Val (@! gryff.src.serverlib.Serve)) (Val #port))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hpkg, #Hsh, #Hcs, #Hse, Hmux, #Hds, #Hsreg, Hrr, %Hth⟩ HΦ
  unfold replicaRegRes deployRegResDef
  icases Hrr with ⟨-, %Hw⟩
  unfold netShare
  icases Hsh with ⟨-, #Hrl⟩
  ihave #Hrlk : H.rpcLisP γ.rpc (replicaRpcLis k) (net.rpc.connectReq net.rpc.defaultRPCPath)
      net.rpc.connectAns $$ [Hrl]
  · unfold rpcLises
    icases Hrl with ⟨-, #Hrs⟩
    ihave ⟨#H0, #Hrs⟩ := BigSepL.bigSepL_cons.1 $$ Hrs
    ihave ⟨#H1, #Hrs⟩ := BigSepL.bigSepL_cons.1 $$ Hrs
    ihave ⟨#H2, -⟩ := BigSepL.bigSepL_cons.1 $$ Hrs
    rcases k with _|_|_|k
    · iexact H0
    · iexact H1
    · iexact H2
    · omega
  iapply (wp_Serve' γ k hk port hport γs) $$ [Hmux]
  · iframe
    iframe #
    ipureintro; exact ⟨Hw, Hth⟩
  iexact HΦ

end specs

end Perennial.gryff
