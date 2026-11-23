/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Serve.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
kit.go's `serve(id, addrs)` on server node `id = i + 1`: wait for the configuration
(`awaitConf` in a goroutine, the first valid one over the channel), register the codec, then run
the master (node 1), or (replica node `k + 2`, `k < N`) register with the master, build the
replica (`swift.New`) and serve its rpc methods, or idle. Never returns.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.AwaitConf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServeShare
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.registerRPC
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.New
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.Master__Run
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Run
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NameOkFor
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.New
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Pkg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Pkg

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

-- The codec of the linked results (decision D6, HUB-REQUEST 2, Proof/swiftnet/KitLike.lean):
-- `kitCodecC`, whose `kitCodecOk` holds (`kitCodecOkC_holds`).
attribute [local instance 2000] examples.swiftnet.kitCodecC

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [examples.swiftnet.Assumptions] [net.model.Assumptions]
  [io.ExtraAssumptions]

set_option goose.wp.extras true

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- Server node `i + 1` for `1 ≤ i < 6` (node `7 + i`) is a replica node. -/
theorem swift.replicaNode_host (i : Nat) (h1 : 1 ≤ i) (h2 : i < 6) :
    swift.replicaNode (nodeHost (7 + i)) := by
  match i, h1, h2 with
  | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ =>
    unfold swift.replicaNode nodeHost; decide

/-- What the configuration's future carries to server node `i + 1`: nothing for the master,
replica node `i - 1`'s registration otherwise. -/
def srvR (γ : SwiftNames netDistGF) (i : Nat) : IProp netDistGF :=
  if i = 0 then iprop(True) else client.nodeGhostOk γ.sp (sp.PNode.rep (i - 1))

/-- `awaitConf` at server node `i + 1`'s configuration port (node `7 + i`). -/
theorem wp_awaitConf_srv (wp_claim : client.claimGhost.spec) (γ : SwiftNames netDistGF) (i : Nat)
    (hi : i < 6) (ch : Loc) (γf : FutureNames) :
    {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗
        addrTok (atStr (7 + i) (W64 2000)) ∗ common γ ∗
        (if i = 0 then iprop(True)
         else sp.predTok γ.sp (sp.PNode.rep (i - 1)) ∗ client.ghostFresh) ∗
        isFuture examples.swiftnet.msg γf ch ∗
        Fulfill γf (confMsg γ (fun _ cs => cs = []) (srvR γ i)) }}
      (App (App (Val (@! examples.swiftnet.awaitConf)) (Val #(atStr (7 + i) (W64 2000))))
        (Val #ch))
    {{ RET #(); False }} := by
  iintro %Φ ⟨#Hpkg, Htok, #Hcom, Hpt, #Hfut, Hful⟩ HΦ
  unfold srvR
  by_cases h0 : i = 0
  · subst h0
    simp only [↓reduceIte]
    ihave #Hcp := common_confProto_master γ $$ Hcom
    iapply (wp_awaitConf_master γ (atStr 7 (W64 2000)) ch γf) $$ [Htok Hful] HΦ
    iframe Hpkg Htok Hcp Hfut Hful
  · simp only [h0, ↓reduceIte]
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [show 7 + (k + 1) = 8 + k from by omega]
    ihave #Hcp := common_confProto_replica γ k (by omega) $$ Hcom
    ihave ⟨-, -, #Hinv⟩ := common_rest γ $$ Hcom
    icases Hpt with ⟨Hpt, Hfr⟩
    iapply (wp_awaitConf_replica wp_claim γ k (atStr (8 + k) (W64 2000)) ch γf)
      $$ [Htok Hful Hpt Hfr] HΦ
    iframe Hpkg Htok Hcp Hfut Hful Hinv Hpt Hfr

theorem wp_serve (wp_claim : client.claimGhost.spec) (γ : SwiftNames netDistGF) (i : Nat)
    (hi : i < 6) (sl : GoSlice)
    (hat : at.spec (GF := netDistGF)) (hport : port.spec (GF := netDistGF))
    (hhost : host.spec (GF := netDistGF)) (hnc : nodeConfig.spec (GF := netDistGF))
    (hreg : registerRPC.spec (GF := netDistGF))
    (hMNew : master.New.spec) (hMRun : master.Master.Run.spec')
    (hregister : register.spec) (hmax : setMaxDesc.spec (GF := netDistGF))
    (hSNew : swift.New.spec)
    (hcodec : ⊢ net.rpc.kitCodecOk (GF := netDistGF)) :
    {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ sl ↦* addrs ∗ serverShare γ i ∗
        nodeIp (nodeHost (7 + i)) ∗ net.http.muxOwner [] ∗
        -- change log C14: on a replica node, the mutable globals
        swift.mutGlobalsAt (nodeHost (7 + i)) ∗
        -- D90 (R-E1): on a replica node, the node's fresh ghost
        client.freshAt (nodeHost (7 + i)) }}
      (App (App (Val (@! examples.swiftnet.serve)) (Val #(W64 (i + 1)))) (Val #sl))
    {{ RET #(); False }} := by
  wp_start as ⟨Hsl, Hsh, #Hip, Hmux, Hglob, Hfr⟩
  ihave ⟨Hct, #Hcom, Hpt, Hrole⟩ := serverShare_split γ i hi $$ Hsh
  ihave Hpt : (if i = 0 then iprop(True)
      else sp.predTok γ.sp (sp.PNode.rep (i - 1)) ∗ client.ghostFresh) $$ [Hpt Hfr]
  · by_cases h0 : i = 0
    · simp only [h0, ↓reduceIte]; itrivial
    · have h1 : 1 ≤ i := by omega
      simp only [h0, ↓reduceIte]
      unfold client.freshAt
      rw [if_pos (swift.replicaNode_host i h1 hi)]
      iframe Hpt Hfr
  wp_auto
  wp_apply (chan.wp_make2 (V := examples.swiftnet.msg) (W64 1)) as %chl %γch ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  imod start_future (V := examples.swiftnet.msg) chl γch _ (Or.inr rfl) $$ Hch Hoc
    with ⟨%γf, #Hfut, Haw⟩
  imod future_alloc_promise γf chl (confMsg γ (fun _ cs => cs = []) (srvR γ i)) [] $$ Hfut Haw
    with ⟨Hful, Haw⟩
  have e7 : (W64 6 + W64 (↑i + 1) : w64) = W64 ((7 + i : Nat) : Int) := by word
  have hu : uint.nat (W64 ((7 + i : Nat) : Int)) = 7 + i := by word
  rw [e7]
  wp_apply hat sl (DFrac.own 1) (W64 ((7 + i : Nat) : Int)) (W64 2000) (by word) $$ [$Hsl] as Hsl
  rw [hu]
  wp_apply wp_fork $$ [Hct Hful Hpt]
  · wp_apply wp_awaitConf_srv wp_claim γ i hi chl γf $$ [$Hct $Hcom $Hpt $Hfut $Hful]
    iintro %Hf; exact Hf.elim
  wp_apply (wp_future_await (t := examples.swiftnet.msg.ty) γf chl _) $$ [$Hfut $Haw]
    as %v %P %pre %post ⟨%Hpend, HP, -⟩
  have hP : P = confMsg γ (fun _ cs => cs = []) (srvR γ i) := by
    rcases pre with _ | ⟨_, _ | _⟩ <;> simp_all
  subst hP
  iunfold confMsg at HP
  icases HP with ⟨%c, %cs, #Hc, %Hv, -, HR⟩
  obtain ⟨Hv, -, -, Hvc⟩ := Hv
  rw [Hvc]
  wp_apply hreg as ⟨#Hcs, #Hgcs⟩
  rw [e7]
  have hl : addrs.length = 13 := rfl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  have hs : sint.Z sl.len = 13 := by
    have h1 := Hlen.1; rw [hl] at h1; word
  obtain ⟨a, ha⟩ : ∃ a, addrs[7 + i]? = some a := ⟨_, List.getElem?_eq_getElem (by rw [hl]; omega)⟩
  have hz : sint.Z (W64 ((7 + i : Nat) : Int)) = 7 + i := by word
  have hzn : (sint.Z (W64 ((7 + i : Nat) : Int))).toNat = 7 + i := by rw [hz]; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hz]; omega, by rw [hz, hs]; omega⟩)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 ((7 + i : Nat) : Int))) addrs (DFrac.own 1) a
    (by rw [hz]; omega) $$ [$Hsl] as Hsl
  · ipureintro; rw [hzn]; exact ha
  wp_apply hport (7 + i) a ha
  wp_apply hnc as %cfgp %cv ⟨#Hcfg, #Hcv⟩
  wp_if_destruct
  · -- node 1: the master
    have hi0 : i = 0 := by
      have h := congrArg uint.Z Hif; word
    subst hi0
    icases Hrole with (⟨-, Hmt, Hmw⟩ | ⟨%Hlt, -⟩)
    rotate_left
    · omega
    ihave %Hv := ((conf.is_confIs γ c).1.trans (confIs_valid γ.conf c)) $$ Hc
    ipersist «$a3»
    ihave #Hlg : dlog.quiet (GF := netDistGF) «$a3_ptr» $$ [«$a3»]
    · unfold dlog.quiet
      ihave %Hnn := typedPointsto_not_null $$ «$a3»
      iframe «$a3»
      ipureintro; exact Hnn
    have hN : uint.nat (W64 (c.n : Int)) = c.n := by have := Conf.valid_lt Hv; word
    have hp7 : (W64 ((nodePort (7 + 0) : Nat) : Int) : w64) = W64 7001 := rfl
    rw [hp7]
    iunfold mem.writer at Hmw
    ihave #Hc' := (conf.is_confIs γ c).1 $$ Hc
    wp_apply hMNew (W64 (c.n : Int)) (W64 7001) cfgp «$a3_ptr» γ.conf γ.mem c _
      $$ [$Hmw $Hcfg $Hlg $Hc'] as %m Hm
    · ipureintro; exact hN
    ihave ⟨%HSS, #Hrpcs, -⟩ := common_rest γ $$ Hcom
    ihave #Hko : net.rpc.kitCodecOk (GF := netDistGF) $$ []
    · iapply hcodec
    have hSS1 : ∀ svc, γ.W.SS masterAddr svc =
        if svc = go!"Master" then some (sp.masterSpec γ.conf γ.mem) else none := by
      -- change log C7: the whole service map at `masterAddr`
      intro svc
      have hm : masterAddr ∉ replicaRpcAddrs := by decide
      rw [HSS]; by_cases h : svc = go!"Master" <;> simp [services, h, hm]
    have hSS2 : ∀ a ∈ replicaRpcAddrs, γ.W.SS a go!"Replica" = some (sp.replicaRpcSpec γ.conf γ.mem) := by
      intro a ha
      have hm : a ≠ masterAddr := by
        intro h; subst h; revert ha; decide
      rw [HSS]; simp [services, hm, ha]
    wp_apply hMRun m γ.conf γ.mem (uint.nat (W64 (c.n : Int))) γ.W
      $$ [$Hm $Hmt $Hmux $Hrpcs $Hcs $Hko] as %Hf
    · icases Hip with %Hipe
      isplitr
      · ipureintro; rw [Hipe]; rfl
      ipureintro; exact ⟨hSS1, hSS2⟩
    exact Hf.elim
  · -- replica nodes and idle nodes
    have hi0 : i ≠ 0 := by
      intro h; subst h; exact Hif rfl
    icases Hrole with (⟨%Hi0, -⟩ | ⟨-, Hrt, Hrr, Hrs⟩)
    · omega
    ihave %Hv := ((conf.is_confIs γ c).1.trans (confIs_valid γ.conf c)) $$ Hc
    have hcl := Conf.valid_lt Hv
    wp_if_destruct
    · -- a replica of the configuration: node `i + 1`, replica `i - 1 < N`
      have hk : i - 1 < c.n := by
        have h1 : 1 ≤ i := by omega
        have h2 := hcl.1
        word
      rw [e7]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hz]; omega, by rw [hz, hs]; omega⟩)]
      wp_apply wp_load_slice_index sl (sint.Z (W64 ((7 + i : Nat) : Int))) addrs (DFrac.own 1) a
        (by rw [hz]; omega) $$ [$Hsl] as Hsl
      · ipureintro; rw [hzn]; exact ha
      wp_apply hhost (7 + i) a ha
      have h1z : sint.Z (W64 6 + W64 1) = 7 := rfl
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [h1z]; omega, by rw [h1z, hs]; omega⟩)]
      wp_apply wp_load_slice_index sl (sint.Z (W64 6 + W64 1)) addrs (DFrac.own 1) masterAddr
        (by rw [h1z]; omega) $$ [$Hsl] as Hsl
      · ipureintro; rfl
      ihave ⟨%HSS, #Hrpcs, #Hinv⟩ := common_rest γ $$ Hcom
      ihave #Hko : net.rpc.kitCodecOk (GF := netDistGF) $$ []
      · iapply hcodec
      ihave #Hmrpc := BigSepL.bigSepL_mem (Φ := fun a => net.rpc.rpcAddr (GF := netDistGF) γ.W a)
        (show masterAddr ∈ rpcAddrs from List.mem_cons_self) $$ Hrpcs
      have hra := replicaAddrs_addrPort (i - 1) (by omega)
      rw [show 8 + (i - 1) = 7 + i from by omega] at hra
      wp_apply hregister γ (nodeHost (7 + i)) (W64 ((nodePort (7 + i) : Nat) : Int)) (i - 1) c hra hk
        $$ [$Hc $Hmrpc $Hcs $Hko] as %rid %nl %nodes %fr ⟨Hnl, #Hcfgv, %Hrid⟩
      · ipureintro; exact HSS
      ihave Hglob : swift.mutGlobals $$ [Hglob]
      · unfold swift.mutGlobalsAt
        rw [if_pos (swift.replicaNode_host i (by omega) hi)]
        iexact Hglob
      iunfold swift.mutGlobals at Hglob
      icases Hglob with ⟨%d0, %v0, %n0, HMax, HPool, HShard⟩
      wp_apply hmax (W64 (c.desc : Int)) d0
        (by obtain ⟨-, -, -, h⟩ := Hv; have := hcl.2.2.2; word) $$ [$HMax] as HMax
      iStructNamed Hcv
      wp_auto
      ipersist «$a10»
      ihave #Hlg : dlog.quiet (GF := netDistGF) «$a10_ptr» $$ [«$a10»]
      · unfold dlog.quiet
        ihave %Hnn := typedPointsto_not_null $$ «$a10»
        iframe «$a10»
        ipureintro; exact Hnn
      ipersist Hnl
      ihave #Hc' := (conf.is_confIs γ c).1 $$ Hc
      ihave %Hcc := sp.cfg_conf (γc := γ.conf) (γm := γ.mem) nodes.length fr nodes c $$ [Hcfgv Hc']
      · iframe Hcfgv Hc'
      obtain ⟨hN, hfr⟩ := Hcc
      have hfr' : fr = decide (W64 (c.fastRead : Int) = W64 1) := by
        rw [hfr]
        have := hcl.2.1
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, decide_eq_true_eq]
        constructor
        · intro h; rw [h]; rfl
        · intro he; have := congrArg uint.Z he; word
      subst hfr'
      ihave #Hprotos := common_replicaProtos γ $$ Hcom
      have hsr : srvR γ i = client.nodeGhostOk γ.sp (sp.PNode.rep (i - 1)) := by
        unfold srvR; rw [if_neg (by omega)]
      rw [hsr]
      ihave #Hng := HR
      wp_apply hSNew cv.Alias' rid nl nodes nodes.length (i - 1) _ (W64 (c.pool : Int))
        ((W64 (c.n : Int) - W64 1) / W64 2) cfgp «$a10_ptr» γ.sp γ.conf γ.mem γ.lin
        (sp.addrPort (nodeHost (7 + i)) (W64 ((nodePort (7 + i) : Nat) : Int))) (nodeHost (7 + i))
        $$ [$Hinv $Hcfgv $Hnl $Hrs $Hrt $Hip $Hprotos $Hcfg $Hlg $Hgcs $Hng HMax HPool HShard]
        as %rep ⟨#Hrok, Hmeth, %Hname⟩
      · isplitr [HMax HPool HShard]
        · ipureintro
          refine ⟨hra, Hrid, ?_⟩
          unfold sp.addrPort; exact List.prefix_append _ _
        isplitr [HMax HPool HShard]
        · ipureintro
          refine ⟨?_, ?_⟩
          · obtain ⟨-, -, h, -⟩ := Hv; have := hcl.2.2.1; word
          · rw [← hN]; have := hcl.1; obtain ⟨h, -⟩ := Hv; word
        · iexists _, _, _
          iframe
          ipureintro
          obtain ⟨-, -, -, h⟩ := Hv; have := hcl.2.2.2; word
      -- `swift.New`'s frozen facts are about `kitCodec`; the same at `kitCodecC` (D6)
      ihave #Hrok := rcvrOk_of examples.swiftnet.kitCodecC _ _ $$ Hrok
      ihave Hmeth := methods_of examples.swiftnet.kitCodecC _ $$ Hmeth
      ihave #Hrpc : isPkgInit (PROP := IProp netDistGF) pkg_id.net.rpc $$ []
      · iPkgInit
      ihave #Hno : net.rpc.nameOkFor (GF := netDistGF) (net.rpc.kitFn go!"rpcName")
          (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #rep) $$ []
      · iapply kitNameOkFor_replica
      wp_apply net.rpc.Register.wp_proof' (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #rep)
        $$ [$Hcs $Hko $Hno $Hmeth] as %err Hres
      icases Hres with (⟨%Herr, #Hsreg⟩ | %Herr)
      rotate_left
      · -- registration failed: idle
        cases err with
        | nil => exact absurd rfl Herr
        | ok ie =>
          wp_auto
          wp_for
          wp_apply time.wp_Sleep
          wp_for_post
          iframe
      subst Herr
      wp_auto
      wp_apply net.rpc.HandleHTTP.wp_proof [] $$ [$Hmux] as ⟨Hmux, %s, #Hds, #Hroute⟩
      · ipureintro; simp
      rw [e7]
      wp_apply hat sl (DFrac.own 1) (W64 ((7 + i : Nat) : Int)) (W64 1000) (by word) $$ [$Hsl] as Hsl
      rw [hu]
      have hra' : atStr (7 + i) (W64 1000) ∈ replicaRpcAddrs := by
        have := atStr_rpc (i - 1) (by omega)
        rw [show 8 + (i - 1) = 7 + i from by omega] at this
        exact List.mem_of_getElem? this
      wp_apply net.Listen.wp_proof (atStr (7 + i) (W64 1000)) $$ [$Hrr] as %lv %lerr ⟨Hrr, Hlres⟩
      icases Hlres with (⟨%l, %lid, %Hlv, #Hl⟩ | ⟨%li, %Hlv, -⟩) <;> obtain ⟨rfl, rfl⟩ := Hlv
      rotate_left
      · -- listen failed: idle
        wp_auto
        wp_for
        wp_apply time.wp_Sleep
        wp_for_post
        iframe
      wp_auto
      ihave #Hra := BigSepL.bigSepL_mem (Φ := fun a => net.rpc.rpcAddr (GF := netDistGF) γ.W a)
        (show atStr (7 + i) (W64 1000) ∈ rpcAddrs from List.mem_cons_of_mem _ hra') $$ Hrpcs
      ihave #Hserves := net.rpc.defaultServes_intro γ.W (atStr (7 + i) (W64 1000)) $$ [$Hrpc]
      · iintro !> %svc %S %HS
        rw [HSS] at HS
        have hm : atStr (7 + i) (W64 1000) ≠ masterAddr := by
          intro h; rw [h] at hra'; revert hra'; decide
        simp only [services, hm, false_and, ↓reduceIte, hra', true_and] at HS
        by_cases hsv : svc = go!"Replica"
        · simp only [hsv, ↓reduceIte, Option.some.injEq] at HS
          subst HS hsv
          iexists interface.mkOk (go.GoType.PointerType swift.Replica.ty) #rep
          rw [← Hname]
          iframe Hsreg Hrok
        · simp [hsv] at HS
      ihave ⟨#Hhttp, Hl', #Hp, #Hr, #Hh, %Hwf⟩ := net.rpc.rpc_Serve_pre γ.W (atStr (7 + i) (W64 1000))
        s l lid $$ [$Hrpc $Hcs $Hko $Hserves $Hds $Hroute $Hl $Hra]
      wp_apply net.http.Serve.wp_proof l lid (atStr (7 + i) (W64 1000)) net.rpc.rpcPath
        (net.rpc.serverHandler s) _ _ $$ [$Hhttp $Hl' $Hp $Hr $Hh] as %serr %Hf
      · ipureintro; exact Hwf
      exact Hf.elim
    · -- a node outside the configuration: idle
      wp_for
      wp_apply time.wp_Sleep
      wp_for_post
      iframe


end proof

end Perennial.github_com.imdea_software.swiftpaxos
