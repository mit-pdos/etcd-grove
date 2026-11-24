/-
kit.go's `serve(id, addrs)` on server node `id = i + 1` (the lab's `Serve.lean`, redone for the kit
over remote and `RpcHttpHyp`, as dsv-epaxos's `ServerProof`/`ServeReplica`): wait for the
configuration (`awaitConf` in a goroutine, the first valid one over the channel), register the
codec, then run the master (node 1), or (replica node `k + 2`, `k < N`) register with the master,
build the replica (`swift.New`) and serve its rpc methods over HTTP, or idle.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServeDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeShare
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitDeps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Addr
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.New
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.Master__Run
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.New
public import Perennial.Proof.time

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [SwiftNetPkgState netDistGF]

theorem dialP_fullX (γ : SwiftNames netDistGF) (cid : Nat) (bs : List w8)
    (hl : bs.length = confLen) :
    conf.dialP γ cid bs ⊢ ∃ c cs, conf.is γ c ∗ iprop(True) ∗
      ⌜bs = c.encodeC cs ∧ c.valid ∧ c.changesOk cs ∧ cs = []⌝ := by
  iintro H
  ihave ⟨%c, %cs, #Hc, %Hp⟩ := conf.dialP_full γ cid bs hl $$ H
  iexists c, cs
  iframe Hc
  isplitr
  · itrivial
  ipureintro; exact Hp

theorem srvAckQ_ok (γ : SwiftNames netDistGF) (i : Nat) (cid : Nat) :
    (if i = 0 then iprop(True) else sp.predReg γ.sp (sp.PNode.rep (i - 1))) ⊢
      srvAckQ γ i cid [confAck] := by
  unfold srvAckQ
  by_cases h : i = 0
  · simp only [h, ↓reduceIte]; unfold conf.ackQ; iintro -; ipureintro; exact List.prefix_refl _
  · simp only [h, ↓reduceIte]
    unfold conf.ackQP
    iintro #H
    isplitl []
    · ipureintro; exact List.prefix_refl _
    iright; iexact H

end laws

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
  [net.http.Assumptions] [io.Assumptions] [client.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

set_option goose.wp.extras true

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- What the configuration's future carries to server node `i + 1`: nothing for the master,
replica node `i - 1`'s claimed ghost otherwise. -/
def srvR (γ : SwiftNames netDistGF) (i : Nat) : IProp netDistGF :=
  if i = 0 then iprop(True) else client.nodeGhostOk γ.sp (sp.PNode.rep (i - 1))

/-- `awaitConf` at server node `i + 1`'s configuration port. -/
theorem wp_awaitConf_srv (wp_awaitConf : awaitConf.spec (hG := hG))
    (wp_claim : client.claimGhost.spec) (γ : SwiftNames netDistGF) (i : Nat)
    (a : GoString) (ch : Loc) (γf : FutureNames) :
    {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗
        addrProto (Gg := hG.goose_globalGS) a (conf.dialP γ) (srvAckQ γ i) ∗
        (if i = 0 then iprop(True)
         else sp.inv γ.sp γ.conf γ.mem γ.lin ∗ sp.predTok γ.sp (sp.PNode.rep (i - 1)) ∗
           client.ghostFresh) ∗
        isFuture examples.swiftnet.msg γf ch ∗
        Fulfill γf (confMsg γ (fun _ cs => cs = []) (srvR γ i)) }}
      (App (App (Val (@! examples.swiftnet.awaitConf)) (Val #a)) (Val #ch))
    {{ RET #(); False }} := by
  iintro %Φ ⟨#Hpkg, #Hcp, Hpt, #Hfut, Hful⟩ HΦ
  iapply (wp_awaitConf γ a ch γf (conf.dialP γ) (srvAckQ γ i) (fun _ cs => cs = [])
    iprop(if i = 0 then iprop(True)
     else iprop(sp.inv γ.sp γ.conf γ.mem γ.lin ∗ sp.predTok γ.sp (sp.PNode.rep (i - 1)) ∗
       client.ghostFresh))
    iprop(if i = 0 then iprop(True) else sp.predReg γ.sp (sp.PNode.rep (i - 1)))
    (srvR γ i) iprop(True)
    (conf.dialP_closed γ) (dialP_fullX γ) (srvAckQ_ok γ i) ?_) $$ [Hpt Hful] HΦ
  · iintro #Hk Hpre -
    unfold srvR
    by_cases h0 : i = 0
    · simp only [h0, ↓reduceIte]
      iintro !>
      isplitl []
      · iintro !>; itrivial
      itrivial
    · simp only [h0, ↓reduceIte]
      icases Hpre with ⟨#Hinv, Htok, Hfresh⟩
      ihave #Hcl : isPkgInit (PROP := IProp netDistGF)
          pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
      · iPkgInit
      imod wp_claim γ.sp γ.conf γ.mem γ.lin (sp.PNode.rep (i - 1)) $$ Hcl Hinv Hfresh Htok
        with ⟨#Hreg, Hok⟩
      imodintro
      iframe Hok
      iexact Hreg
  · iframe Hpkg Hcp Hfut Hful Hpt

theorem srv_digitChar_toNat (n : Nat) (h : n < 10) : (Nat.digitChar n).toNat = 48 + n := by
  match n, h with
  | 0, _ => rw [Nat.digitChar_eq_zero.2 rfl]; rfl
  | 1, _ => rw [Nat.digitChar_eq_one.2 rfl]; rfl
  | 2, _ => rw [Nat.digitChar_eq_two.2 rfl]; rfl
  | 3, _ => rw [Nat.digitChar_eq_three.2 rfl]; rfl
  | 4, _ => rw [Nat.digitChar_eq_four.2 rfl]; rfl
  | 5, _ => rw [Nat.digitChar_eq_five.2 rfl]; rfl
  | 6, _ => rw [Nat.digitChar_eq_six.2 rfl]; rfl
  | 7, _ => rw [Nat.digitChar_eq_seven.2 rfl]; rfl
  | 8, _ => rw [Nat.digitChar_eq_eight.2 rfl]; rfl
  | 9, _ => rw [Nat.digitChar_eq_nine.2 rfl]; rfl

/-- A replica node's peer address and its wildcard listener. -/
theorem wildOf_lis (k : Nat) (hk : k < 5) :
    replica.wildOf (replicaAddrs.getD k go!"") = replicaLis.getD k go!"" := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp [replica.wildOf, replicaAddrs, replicaLis, strings.split, strings.splitAux]

theorem replicaAddrs_addrPort (k : Nat) (hk : k < 5) :
    replicaAddrs[k]? = some (sp.addrPort (nodeHost (8 + k)) (W64 ((nodePort (8 + k) : Nat) : Int))) := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp [replicaAddrs, sp.addrPort, nodeHost, nodePort, Nat.toDigits_of_base_le,
      Nat.toDigits_of_lt_base, srv_digitChar_toNat]

theorem lis7001_not_rpc (a : GoString) (h : lisAccepts go!":7001" a) : a ∉ replicaRpcAddrs := by
  intro hm
  have : lisAcceptsB go!":7001" a = true := lisAcceptsB_iff.2 h
  revert this
  simp only [replicaRpcAddrs, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide

theorem worldOk_of (γ : SwiftNames netDistGF) (W : net.rpc.RpcWorld netDistGF)
    (h : W.SS = services γ.conf γ.mem) : master.worldOk γ.conf γ.mem W := by
  refine ⟨fun a svc ha => ?_, fun a ha => ?_⟩
  · rw [h]; unfold services
    have hb : lisAcceptsB go!":7001" a = true := lisAcceptsB_iff.2 ha
    have hn := lis7001_not_rpc a ha
    by_cases hs : svc = go!"Master"
    · rw [if_pos ⟨hb, hs⟩, if_pos hs]
    · rw [if_neg (fun h' => hs h'.2), if_neg (fun h' => hn h'.1), if_neg hs]
  · rw [h]; unfold services
    have hb : lisAcceptsB go!":7001" a = false := by
      simp only [replicaRpcAddrs, List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [if_neg (by simp [hb]), if_pos ⟨ha, rfl⟩]

/-- The replicas' rpc addresses over HTTP, from their exact listeners' protocols and a dialer's
boot state. -/
theorem srv_rpcHttp_all (W : net.rpc.RpcWorld netDistGF) :
    ∀ l : List GoString, (∀ a ∈ l, addrOk a = true) → cnode.cliBoot (hG := hG) ⊢
      ([∗list] a ∈ l, RpcHttpAddr.rpcLisP W a (connectReq defaultRPCPath) connectAns) -∗
      [∗list] a ∈ l, rpcHttp W a
  | [], _ => by iintro - -; iapply BigSepL.bigSepL_nil.2; itrivial
  | a :: l, hok => by
    iintro #Hb Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨#Ha, Hl⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · iunfold cnode.cliBoot at Hb
      icases Hb with ⟨%Hrb, #Hce, #Hde⟩
      have ha : addrOk a = true := hok a (by simp)
      iunfold rpcHttp; iframe Hce Hde
      isplitr
      · ipureintro; exact Hrb
      iapply RpcHttpAddr.rpcLisP_addr W a _ _ a ha ((lisAccepts_addrOk ha).2 rfl) $$ Ha
    · iapply srv_rpcHttp_all W l (fun x hx => hok x (by simp [hx])) $$ Hb Hl

theorem serve.wp_proof (D : SwNetDeps (hG := hG)) (γ : SwiftNames netDistGF) (i : Nat) (hi : i < 6)
    (wp_awaitConf : awaitConf.spec (hG := hG)) (wp_claim : client.claimGhost.spec)
    (wp_Register : cnode.Register.spec)
    (hMNew : master.New.spec) (hMRun : master.Master.Run.spec)
    (hregister : register.spec (hG := hG)) (hmax : setMaxDesc.spec (GF := netDistGF))
    (hSNew : swift.New.spec) :
    serve.spec γ i := by
  intro sl
  wp_start as ⟨Hsl, Hres⟩
  iunfold serverRes at Hres
  icases Hres with ⟨Hsh, Hboot⟩
  iunfold serverShare at Hsh
  icases Hsh with ⟨-, Hrole, #Hcom⟩
  iunfold srvBoot at Hboot
  icases Hboot with ⟨Hcfr, #Hcb, %Hthr, #Hsrv, Hmux, #Hds0, Hrep⟩
  ihave #Henv := common_confEnv γ $$ Hcom
  iunfold confEnv at Henv
  icases Henv with ⟨#HconfP, -, -⟩
  ihave #Hcom' := Hcom
  iunfold common at Hcom'
  icases Hcom' with ⟨-, #Hlis, %HSS, #Hrpc, #Hinv⟩
  ihave Hpt : (if i = 0 then iprop(True)
      else sp.inv γ.sp γ.conf γ.mem γ.lin ∗ sp.predTok γ.sp (sp.PNode.rep (i - 1)) ∗
        client.ghostFresh) ∗
      (if i = 0 then mem.writer γ else sp.replicaStart γ.sp (i - 1)) ∗
      (if i = 0 then iprop(True) else swift.mutGlobals) $$ [Hrole Hrep]
  · by_cases h0 : i = 0
    · simp only [h0, ↓reduceIte]; iframe Hrole; try (isplitl [] <;> itrivial)
    · simp only [h0, ↓reduceIte]
      icases Hrole with ⟨Hrs, Hpt⟩
      icases Hrep with ⟨Hfr, Hglob⟩
      iframe Hinv Hpt Hfr Hrs Hglob
  icases Hpt with ⟨Hpt, Hrole, Hglob⟩
  wp_auto
  wp_apply (chan.wp_make2 (V := examples.swiftnet.msg) (W64 1)) as %chl %γch ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  iapply fupd_wp
  imod start_future (V := examples.swiftnet.msg) chl γch _ (Or.inr rfl) $$ Hch Hoc
    with ⟨%γf, #Hfut, Haw⟩
  imod future_alloc_promise γf chl (confMsg γ (fun _ cs => cs = []) (srvR γ i)) [] $$ Hfut Haw
    with ⟨Hful, Haw⟩
  imodintro
  have e7 : (W64 6 + W64 ((i + 1 : Nat) : Int) : w64) = W64 ((7 + i : Nat) : Int) := by word
  have hu : uint.nat (W64 ((7 + i : Nat) : Int)) = 7 + i := by word
  rw [e7]
  wp_apply wp_at sl (DFrac.own 1) (W64 ((7 + i : Nat) : Int)) (W64 2000) (by word) $$ [$Hsl] as Hsl
  rw [hu]
  have hcidx := atStr_conf i hi
  rw [show 7 + i = 7 + i from rfl] at hcidx
  ihave #Hcp := BigSepL.bigSepL_lookup
    (Φ := fun k a => addrProto a (conf.dialP γ) (srvAckQ γ k)) hcidx $$ HconfP
  wp_apply wp_fork $$ [Hful Hpt]
  · wp_apply wp_awaitConf_srv wp_awaitConf wp_claim γ i _ chl γf $$ [$Hcp $Hpt $Hfut $Hful]
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
  wp_apply wp_Register $$ [$Hcfr] as #Hcs
  rw [e7]
  have hl : addrs.length = 13 := rfl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  have hs : sint.Z sl.len = 13 := by
    have h1 := Hlen.1; rw [hl] at h1; word
  obtain ⟨a, ha⟩ : ∃ a, addrs[7 + i]? = some a := ⟨_, List.getElem?_eq_getElem (by rw [hl]; omega)⟩
  have hz : sint.Z (W64 ((7 + i : Nat) : Int)) = 7 + i := by word
  have hzn : (sint.Z (W64 ((7 + i : Nat) : Int))).toNat = 7 + i := by rw [hz]; omega
  have hb7 : 0 ≤ sint.Z (W64 ((7 + i : Nat) : Int)) ∧
      sint.Z (W64 ((7 + i : Nat) : Int)) < sint.Z sl.len := by rw [hz, hs]; omega
  rw [if_pos hb7]
  wp_apply wp_load_slice_index sl (sint.Z (W64 ((7 + i : Nat) : Int))) addrs (DFrac.own 1) a
    (by rw [hz]; omega) $$ [$Hsl] as Hsl
  · ipureintro; rw [hzn]; exact ha
  wp_apply wp_port (7 + i) a ha
  wp_apply wp_nodeConfig as %cfgp %cv ⟨#Hcfg, #Hcv⟩
  ihave %Hcv := ((conf.is_confIs γ c).1.trans (confIs_valid γ.conf c)) $$ Hc
  have hcl := Conf.valid_lt Hcv
  wp_if_destruct
  · -- node 1: the master
    have hi0 : i = 0 := by have h := congrArg uint.Z Hif; word
    subst hi0
    simp only [↓reduceIte]
    iunfold mem.writer at Hrole
    have hp7 : (W64 ((nodePort (7 + 0) : Nat) : Int) : w64) = W64 7001 := rfl
    rw [hp7]
    try wp_auto
    ipersist «$a3»
    ihave #Hlg : dlog.quiet (GF := netDistGF) «$a3_ptr» $$ [«$a3»]
    · unfold dlog.quiet
      ihave %Hnn := typedPointsto_not_null $$ «$a3»
      iframe «$a3»
      ipureintro; exact Hnn
    have hN : uint.nat (W64 (c.n : Int)) = c.n := by word
    ihave #Hc' := (conf.is_confIs γ c).1 $$ Hc
    ihave #Hmpkg : isPkgInit (PROP := IProp netDistGF)
        pkg_id.github_com.imdea_software.swiftpaxos.master $$ []
    · iPkgInit
    wp_apply hMNew (W64 (c.n : Int)) (W64 7001) cfgp «$a3_ptr» γ.conf γ.mem c _
      $$ [$Hrole $Hcfg $Hlg $Hc'] as %m Hm
    · ipureintro; exact hN
    unfold rpcLis
    icases BigSepL.bigSepL_cons.1 $$ Hrpc with ⟨#Hm7, #Hrr⟩
    ihave #Hrh := srv_rpcHttp_all γ.W replicaRpcAddrs (by decide) $$ Hcb Hrr
    ihave #Hrpcp : isPkgInit (PROP := IProp netDistGF) pkg_id.net.rpc $$ []
    · iPkgInit
    ihave #Hhttp : isPkgInit (PROP := IProp netDistGF) pkg_id.net.http $$ []
    · iPkgInit
    wp_apply hMRun m γ.conf γ.mem (uint.nat (W64 (c.n : Int))) γ.W
      $$ [$Hm $Hmux]
    · iframe Hsrv Hds0 Hm7 Hrh Hcs
      isplitr
      · ipureintro; exact Hthr
      ipureintro; exact worldOk_of γ γ.W HSS
    try wp_auto
    iapply HΦ; itrivial
  · -- replica nodes and idle nodes
    have hi0 : i ≠ 0 := by intro h; subst h; exact Hif rfl
    simp only [hi0, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    · -- a replica of the configuration: node `i + 1`, replica `k = i - 1 < N`
      have hk : i - 1 < c.n := by
        have h1 : 1 ≤ i := by omega
        have h2 := hcl.1
        word
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hk ⊢
      rw [e7, if_pos hb7]
      wp_apply wp_load_slice_index sl (sint.Z (W64 ((7 + (k + 1) : Nat) : Int))) addrs (DFrac.own 1) a
        (by rw [hz]; omega) $$ [$Hsl] as Hsl
      · ipureintro; rw [hzn]; exact ha
      wp_apply wp_host (7 + (k + 1)) a ha
      have h1z : sint.Z (W64 6 + W64 1) = 7 := rfl
      rw [if_pos (show 0 ≤ sint.Z (W64 6 + W64 1) ∧ sint.Z (W64 6 + W64 1) < sint.Z sl.len by
        rw [h1z, hs]; omega)]
      wp_apply wp_load_slice_index sl (sint.Z (W64 6 + W64 1)) addrs (DFrac.own 1) masterAddr
        (by rw [h1z]; omega) $$ [$Hsl] as Hsl
      · ipureintro; rfl
      unfold rpcLis
      icases BigSepL.bigSepL_cons.1 $$ Hrpc with ⟨#Hm7, #Hrr⟩
      ihave #Hmh : rpcHttp γ.W masterAddr $$ []
      · iunfold cnode.cliBoot at Hcb
        icases Hcb with ⟨%Hrb, #Hce, #Hde⟩
        iunfold rpcHttp; iframe Hce Hde
        isplitr
        · ipureintro; exact Hrb
        iapply RpcHttpAddr.rpcLisP_addr γ.W go!":7001" _ _ masterAddr cnode.masterAddr_ok
          cnode.masterAddr_lis $$ Hm7
      ihave #Hko : net.rpc.kitCodecOk (GF := netDistGF) $$ []
      · iunfold net.rpc.kitCodecOk; itrivial
      have hra := replicaAddrs_addrPort k (by omega)
      rw [show 8 + k = 7 + (k + 1) from by omega] at hra
      wp_apply hregister γ (nodeHost (7 + (k + 1))) (W64 ((nodePort (7 + (k + 1)) : Nat) : Int)) k c
          hra hk $$ [$Hc $Hmh $Hcs $Hko] as %rid %nl %nodes %fr ⟨Hnl, #Hcfgv, %Hrid⟩
      · ipureintro; exact HSS
      iunfold swift.mutGlobals at Hglob
      icases Hglob with ⟨%d0, %v0, %n0, HMax, HPool, HShard⟩
      wp_apply hmax (W64 (c.desc : Int)) d0
        (by obtain ⟨-, -, -, h⟩ := Hcv; have := hcl.2.2.2; word) $$ [$HMax] as HMax
      iStructNamed Hcv
      wp_auto
      ipersist «$a10»
      ihave #Hlg : dlog.quiet (GF := netDistGF) «$a10_ptr» $$ [«$a10»]
      · unfold dlog.quiet
        ihave %Hnn := typedPointsto_not_null $$ «$a10»
        iframe «$a10»
        ipureintro; exact Hnn
      iapply fupd_wp
      imod ownSlice_persist $$ Hnl with #Hnl
      imodintro
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
      ihave #Hprotos := cnode.lis_replicaAddrs (sp.inP γ.sp γ.conf γ.mem) (sp.outQ γ.sp γ.conf γ.mem) $$ Hlis
      have hrak : replicaAddrs.getD k go!"" =
          sp.addrPort (nodeHost (7 + (k + 1))) (W64 ((nodePort (7 + (k + 1)) : Nat) : Int)) := by
        rw [List.getD_eq_getElem?_getD, hra, Option.getD_some]
      have hlk : replicaLis[k]? = some (replicaLis.getD k go!"") := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [replicaLis]; omega)]
        rfl
      ihave #Hlk := BigSepL.bigSepL_lookup
        (Φ := fun _ la => lisProto la (sp.inP γ.sp γ.conf γ.mem) (sp.outQ γ.sp γ.conf γ.mem))
        hlk $$ Hlis
      rw [← wildOf_lis k (by omega), hrak] at *
      have hsr : srvR γ (k + 1) = client.nodeGhostOk γ.sp (sp.PNode.rep k) := by
        unfold srvR; rw [if_neg (by omega)]; rfl
      rw [hsr]
      ihave #Hng := HR
      ihave #Hip := nodeIp_intro (GF := netDistGF) (nodeHost (7 + (k + 1)))
      wp_apply hSNew cv.Alias' rid nl nodes nodes.length k _ (W64 (c.pool : Int))
        ((W64 (c.n : Int) - W64 1) / W64 2) cfgp «$a10_ptr» γ.sp γ.conf γ.mem γ.lin
        (sp.addrPort (nodeHost (7 + (k + 1))) (W64 ((nodePort (7 + (k + 1)) : Nat) : Int)))
        (nodeHost (7 + (k + 1)))
        $$ [$Hinv $Hcfgv $Hnl $Hrole $Hip $Hlk $Hprotos $Hcfg $Hlg $Hng $Hcs HMax HPool HShard]
        as %rep Hrok
      · isplitr [HMax HPool HShard]
        · ipureintro
          refine ⟨hra, Hrid, ?_⟩
          unfold sp.addrPort; exact List.prefix_append _ _
        isplitr [HMax HPool HShard]
        · ipureintro
          refine ⟨?_, ?_⟩
          · obtain ⟨-, -, h, -⟩ := Hcv; have := hcl.2.2.1; word
          · rw [← hN]; have := hcl.1; obtain ⟨h, -⟩ := Hcv; word
        isplitl [HMax HPool HShard]
        · iexists _, _, _
          iframe
          ipureintro
          obtain ⟨-, -, -, h⟩ := Hcv; have := hcl.2.2.2; word
        unfold encoding.gob.codecSet; itrivial
      icases Hds0 with ⟨%γs, #Hds⟩
      wp_apply (H.Register_spec γs net.rpc.RpcCodec.spec
          (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #rep)
          (withErr (sp.replicaRpcSpec γ.conf γ.mem)) go!"Replica" (W8 82) go!"eplica" rfl
          ⟨by decide, by decide⟩) $$ [$Hds $Hcs Hrok] as %err Hreg
      · simp only [net.rpc.RpcCodec.spec] at *
        iexact Hrok
      icases Hreg with (⟨%He, #Hsr⟩ | %He)
      rotate_left
      · rcases err with ei | _
        · wp_auto
          wp_for
          try rw [if_pos (decide_eq_true rfl)]
          wp_apply time.wp_Sleep
          wp_for_post
          iframe
        · exact absurd rfl He
      subst He
      wp_auto
      have hrpc := atStr_rpc k (by omega)
      have hra' : atStr (8 + k) (W64 1000) ∈ replicaRpcAddrs := List.mem_of_getElem? hrpc
      have hrok : addrOk (atStr (8 + k) (W64 1000)) = true :=
        cnode.replicaRpcAddrs_ok _ hra'
      ihave #Hss : (□ ∀ a, ⌜lisAccepts (atStr (8 + k) (W64 1000)) a⌝ →
          net.rpc.srvServes γs net.rpc.RpcCodec.spec γ.W a : IProp netDistGF) $$ []
      · iintro !> %a %ha
        have ha' := (lisAccepts_addrOk hrok).1 ha
        subst ha'
        unfold net.rpc.srvServes
        iintro !> %svc %S %hS
        rw [HSS] at hS
        have hb : lisAcceptsB go!":7001" (atStr (8 + k) (W64 1000)) = false := by
          simp only [replicaRpcAddrs, List.mem_cons, List.not_mem_nil, _root_.or_false] at hra'
          rcases hra' with h | h | h | h | h <;> rw [h] <;> decide
        unfold services at hS
        rw [if_neg (fun h => by have h1 := h.1; rw [hb] at h1; exact absurd h1 (by decide))] at hS
        by_cases hsv : svc = go!"Replica"
        · rw [if_pos ⟨hra', hsv⟩] at hS
          cases hS
          subst hsv
          iframe Hsr
          iapply withErr_errOk
        · rw [if_neg (fun h => hsv h.2)] at hS
          cases hS
      wp_apply (H.HandleHTTP_spec γs net.rpc.RpcCodec.spec γ.W
          (lisAccepts (atStr (8 + k) (W64 1000))) []) $$ [$Hmux $Hds $Hss $Hsrv $Hcs]
        as ⟨-, #Hmh'⟩
      · ipureintro; exact ⟨Hthr, by simp, by simp⟩
      rw [e7]
      wp_apply wp_at sl (DFrac.own 1) (W64 ((7 + (k + 1) : Nat) : Int)) (W64 1000) (by word)
        $$ [$Hsl] as Hsl
      rw [hu, show 7 + (k + 1) = 8 + k from by omega]
      ihave #Hrl := BigSepL.bigSepL_lookup
        (Φ := fun _ la => RpcHttpAddr.rpcLisP γ.W la (connectReq defaultRPCPath) connectAns)
        hrpc $$ Hrr
      ihave %Hlok := RpcHttpAddr.rpcLisP_ok γ.W _ _ _ $$ Hrl
      wp_apply (D.listen go!"tcp" net.tcpNet_tcp (atStr (8 + k) (W64 1000))) as %lv %lerr Hl
      · isplitr
        · ipureintro; exact Hlok
        iapply RpcHttpAddr.rpcLisP_lis
        iexact Hrl
      icases Hl with (⟨%He, %l, #Hli, Hnl, #Hon⟩ | ⟨%x, -, #Hre⟩)
      rotate_left
      · ihave %Hne := net.resErr_netErr $$ Hre
        have hne := net.netErr_ne_nil (Hne.2 (by simp))
        rcases lerr with ei | _
        · wp_auto
          wp_for
          try rw [if_pos (decide_eq_true rfl)]
          wp_apply time.wp_Sleep
          wp_for_post
          iframe
        · exact absurd rfl hne
      subst He
      wp_auto
      iapply fupd_wp
      imod (lisInv_alloc ⊤ _ l (atStr (8 + k) (W64 1000)) true) $$ Hnl with #Hli2
      imodintro
      wp_apply (H.Serve_spec γ.W (atStr (8 + k) (W64 1000)) defaultRPCPath lv l)
        $$ [$Hrl $Hmh' $Hli $Hon $Hli2] as %e2 -
      · ipureintro; exact Hthr
      try wp_auto
      wp_for
      try rw [if_pos (decide_eq_true rfl)]
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · -- a node outside the configuration: idle
      wp_for
      try rw [if_pos (decide_eq_true rfl)]
      wp_apply time.wp_Sleep
      wp_for_post
      iframe


theorem Server.wp_proof (wp_serve : ∀ γ i, i < 6 → serve.spec (hG := hG) γ i)
    (wp_Addrs : cnode.AddrsC.spec) : Server.spec (hG := hG) := by
  intro γ i hi
  wp_start as Hres
  wp_auto
  wp_apply wp_Addrs as %asl Hasl
  wp_apply wp_serve γ i hi asl $$ [$Hasl $Hres]
  iapply HΦ; itrivial

end proof

end Perennial.github_com.imdea_software.swiftpaxos
