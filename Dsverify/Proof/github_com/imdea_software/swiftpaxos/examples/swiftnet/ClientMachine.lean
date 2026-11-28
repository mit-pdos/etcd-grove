/-
Client machine `c` (`kit.go`'s `newClient`, `clientNode`, `Client`; the lab's `ClientNodeNew.lean`
and `ClientNode.lean`, for the kit over remote):

* `newClient(addrs, c)`: it waits for the configuration on the node's configuration port
  (`awaitConf` over a one-slot channel, a future whose contract carries the configuration fact,
  the node's leader changes and the node's claimed ghost, which `awaitConf` registered before its
  first acknowledgment, `client.claimGhost.spec`), then for the start message on its start port
  (a second `awaitConf`, whose future carries every predicted node's registration,
  `sp.allPredsReg`), registers the rpc codec, builds the `Sys` (read-only `addrs`, `conf`; `mu`
  over `done`; `opMu` over `ops` = 0 and `b` = nil with the client's sequence number 0) and starts
  the node's leader changes;
* `clientNode(addrs, caddr, c)`: `newClient`, then remote's `ServeClient` with `op` (`op.spec`)
  over `isSysL` and the link invariant;
* `Client(c)`: `clientNode(Addrs(), ClientAddrs()[c], c)`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeShare
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitDeps
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.imdea_software.swiftpaxos.examples.swiftnet

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

/-- A valid change of a valid configuration is at a replica's server node (2..6). -/
theorem changes_node (cf : Conf) (cs : List Change) (hv : cf.valid) (hcs : cf.changesOk cs) :
    ∀ ch ∈ cs.map goChange, 2 ≤ uint.nat ch.Node' ∧ uint.nat ch.Node' ≤ 6 := by
  intro ch hch
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hch
  have h := hcs.2 x hx
  unfold Change.valid at h
  have hn : cf.n ≤ 5 := by rcases hv.1 with h | h <;> omega
  simp only [goChange]
  have : uint.nat (W64 (x.node : Int)) = x.node := by
    have : x.node < 2 ^ 64 := by omega
    word
  omega

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [SwiftNetPkgState netDistGF]

/-- The acknowledgment of predicted node `n`'s configuration port, once it registered. -/
theorem ackQP_of_reg (γ : SwiftNames netDistGF) (n : sp.PNode) (cid : Nat) :
    sp.predReg γ.sp n ⊢ conf.ackQP γ n cid [confAck] := by
  unfold conf.ackQP
  iintro #H
  isplitl []
  · ipureintro; exact List.prefix_refl _
  iright; iexact H

theorem ackQ_ok (cid : Nat) : (iprop(True) : IProp netDistGF) ⊢ conf.ackQ cid [confAck] := by
  unfold conf.ackQ; iintro -; ipureintro; exact List.prefix_refl _

theorem dialPC_fullX (γ : SwiftNames netDistGF) (cid : Nat) (bs : List w8)
    (hl : bs.length = confLen) :
    conf.dialPC γ cid bs ⊢ ∃ c cs, conf.is γ c ∗ iprop(True) ∗
      ⌜bs = c.encodeC cs ∧ c.valid ∧ c.changesOk cs ∧ True⌝ := by
  iintro H
  ihave ⟨%c, %cs, #Hc, %Hp⟩ := conf.dialPC_full γ cid bs hl $$ H
  iexists c, cs
  iframe Hc
  isplitr
  · itrivial
  ipureintro; exact Hp

end laws

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
  [net.http.Assumptions] [client.Assumptions] [examples.swiftnet.Assumptions] [io.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]
variable [ρ : RemoteGS]

/-- A dialer's boot state and the addresses' protocols: each address over HTTP. -/
theorem rpcHttp_all (W : net.rpc.RpcWorld netDistGF) :
    ∀ l : List GoString, cliBoot (hG := hG) ⊢
      ([∗list] a ∈ l, RpcHttpAddr.rpcAddrP W a (connectReq defaultRPCPath) connectAns) -∗
      [∗list] a ∈ l, rpcHttp W a
  | [] => by iintro - -; iapply BigSepL.bigSepL_nil.2; itrivial
  | a :: l => by
    iintro #Hb Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨#Ha, Hl⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · iunfold cliBoot at Hb
      icases Hb with ⟨%Hrb, #Hce, #Hde⟩
      iunfold rpcHttp; iframe Hce Hde Ha; ipureintro; exact Hrb
    · iapply rpcHttp_all W l $$ Hb Hl

set_option goose.wp.extras true

theorem newClient.wp_proof (γ : SwiftNames netDistGF) (c : Nat) (hc : c < 6)
    (wp_awaitConf : awaitConf.spec (hG := hG))
    (wp_atConf : atConf.spec) (wp_atStart : atStart.spec)
    (wp_claim : client.claimGhost.spec)
    (wp_Register : Register.spec)
    (wp_changeLeaders : Sys.changeLeaders.spec γ c) :
    newClient.spec γ c := by
  intro asl
  wp_start as ⟨Hasl, Hsh, Hfr, Hcfr, #Hboot, #Hpool⟩
  ihave ⟨#Hcp, #Hsp, Hseq, Hpt, #Hm, #Hrpcs, %HSS, #Hreps, #Hinv⟩ :=
    clientNodeShare_split γ c hc $$ Hsh
  ihave #Hcpkg : isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
  · iPkgInit
  wp_auto
  -- the configuration
  wp_apply (chan.wp_make2 (V := examples.swiftnet.msg) (W64 1)) as %chl %γch ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  imod start_future (V := examples.swiftnet.msg) chl γch _ (Or.inr rfl) $$ Hch Hoc
    with ⟨%γf, #Hfut, Haw⟩
  imod future_alloc_promise γf chl
    (confMsg γ (fun _ _ => True) (client.nodeGhostOk γ.sp (sp.PNode.cl c))) [] $$ Hfut Haw
    with ⟨Hful, Haw⟩
  wp_apply wp_atConf asl (DFrac.own 1) c hc $$ [$Hasl] as Hasl
  wp_apply wp_fork $$ [Hful Hpt Hfr]
  · wp_apply wp_awaitConf γ (confAddrC c) chl γf (conf.dialPC γ) (conf.ackQP γ (sp.PNode.cl c))
      (fun _ _ => True)
      iprop(sp.inv γ.sp γ.conf γ.mem γ.lin ∗ sp.predTok γ.sp (sp.PNode.cl c) ∗ client.ghostFresh)
      (sp.predReg γ.sp (sp.PNode.cl c)) (client.nodeGhostOk γ.sp (sp.PNode.cl c)) iprop(True)
      (conf.dialPC_closed γ) (dialPC_fullX γ) (ackQP_of_reg γ (sp.PNode.cl c)) ?_
      $$ [Hful Hpt Hfr]
    · iintro #Hpkg ⟨#Hi, Htok, Hfresh⟩ -
      ihave #Hcl : isPkgInit (PROP := IProp netDistGF)
          pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
      · iPkgInit
      imod wp_claim γ.sp γ.conf γ.mem γ.lin (sp.PNode.cl c) $$ Hcl Hi Hfresh Htok
        with ⟨#Hreg, Hok⟩
      imodintro
      iframe Hok
      iexact Hreg
    · iframe Hcp Hfut Hful Hinv Hpt Hfr
    · iintro %Hf; exact Hf.elim
  wp_apply (wp_future_await (t := examples.swiftnet.msg.ty) γf chl _) $$ [$Hfut $Haw]
    as %v %P %pre %post ⟨%Hpend, HP, -⟩
  have hP : P = confMsg γ (fun _ _ => True) (client.nodeGhostOk γ.sp (sp.PNode.cl c)) := by
    rcases pre with _ | ⟨_, _ | _⟩ <;> simp_all
  subst hP
  iunfold confMsg at HP
  icases HP with ⟨%cf, %cs, #Hcf, %Hv, Hcs, #Hgok⟩
  obtain ⟨hcv, hcs, -, hvc⟩ := Hv
  -- the start message
  try wp_auto
  wp_apply (chan.wp_make2 (V := examples.swiftnet.msg) (W64 1)) as %chs %γch2 ⟨#Hch2, %Hcap2, Hoc2⟩
  · ipureintro; decide
  imod start_future (V := examples.swiftnet.msg) chs γch2 _ (Or.inr rfl) $$ Hch2 Hoc2
    with ⟨%γf2, #Hfut2, Haw2⟩
  imod future_alloc_promise γf2 chs
    (confMsg γ (fun _ cs => cs = []) (sp.allPredsReg γ.sp γ.conf)) [] $$ Hfut2 Haw2
    with ⟨Hful2, Haw2⟩
  wp_apply wp_atStart asl (DFrac.own 1) c hc $$ [$Hasl] as Hasl
  wp_apply wp_fork $$ [Hful2]
  · wp_apply wp_awaitConf γ (startAddrC c) chs γf2 (conf.startP γ) conf.ackQ
      (fun _ cs => cs = []) iprop(True) iprop(True) (sp.allPredsReg γ.sp γ.conf)
      (sp.allPredsReg γ.sp γ.conf)
      (conf.startP_closed γ) (conf.startP_full γ) ackQ_ok ?_ $$ [Hful2]
    · iintro - - #Hr
      imodintro
      iframe Hr
      iintro !>; itrivial
    · iframe Hsp Hfut2 Hful2
    · iintro %Hf; exact Hf.elim
  wp_apply (wp_future_await (t := examples.swiftnet.msg.ty) γf2 chs _) $$ [$Hfut2 $Haw2]
    as %v2 %P2 %pre2 %post2 ⟨%Hpend2, HP2, -⟩
  have hP2 : P2 = confMsg γ (fun _ cs => cs = []) (sp.allPredsReg γ.sp γ.conf) := by
    rcases pre2 with _ | ⟨_, _ | _⟩ <;> simp_all
  subst hP2
  iunfold confMsg at HP2
  icases HP2 with ⟨%cf2, %cs2, -, -, -, #Hreg⟩
  -- the codec, the `Sys`
  try wp_auto
  wp_apply wp_Register $$ [$Hcfr] as #HcodecSet
  ihave HS := typedPointsto_split _ _ _ $$ «$r0»
  simp only [TypedPointsto.typedPointstoDef]
  icases HS with ⟨Haddrs, Hconf, Hb, Hmu, Hdone, Hopmu, Hops, -⟩
  rw [show goConf cf = confV cf from rfl] at hvc
  rw [hvc]
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ Haddrs with #Haddrs
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ Hconf with #Hconf
  imod ownSlice_persist $$ Hasl with #Hasl
  imod ownSlice_persist $$ Hcs with #Hcs
  imod sync.init_Mutex iprop(∃ d : w64, «$r0_ptr».[examples.swiftnet.Sys, go!"done"] ↦ d) ⊤
    _ $$ Hmu [Hdone] with #Hmutex
  · inext; iexists _; iexact Hdone
  imod sync.init_Mutex (opInv γ «$r0_ptr» c) ⊤ _ $$ Hopmu [Hops Hb Hseq] with #Hopmutex
  · inext
    iunfold opInv
    iexists _
    iframe Hops
    isplitr
    · ipureintro; unfold maxOps; simp
    iunfold clSt
    ileft
    iframe Hb
    unfold cidOf
    iexact Hseq
  ihave #HsysL : isSysL γ c «$r0_ptr» $$ []
  · iunfold isSysL
    iexists cf, asl
    iframe Haddrs Hasl Hconf Hcf Hmutex Hopmutex Hgok Hreg
    iunfold nodeEnv
    iunfold cliBoot at Hboot
    icases Hboot with ⟨%Hrb, #Hce, #Hde⟩
    iframe HcodecSet Hreps Hinv Hpool
    isplitr
    · iunfold rpcHttp; iframe Hce Hde Hm; ipureintro; exact Hrb
    isplitr
    · iapply rpcHttp_all γ.W replicaRpcAddrs $$ [] Hrpcs
      iunfold cliBoot; iframe Hce Hde; ipureintro; exact Hrb
    isplitr
    · ipureintro; exact HSS
    iunfold net.rpc.kitCodecOk; itrivial
  wp_apply wp_fork $$ []
  · wp_apply wp_changeLeaders «$r0_ptr» v.cs' (cs.map goChange) (changes_node cf cs hcv hcs) $$ []
    · iframe HsysL Hcs
    itrivial
  iapply HΦ
  iframe HsysL

theorem clientNode.wp_proof (γ : SwiftNames netDistGF) (γk : GName) (c : Nat) (hc : c < 6)
    (wp_newClient : newClient.spec γ c) (wp_op : op.spec γ γk c)
    (wp_Codec : Codec.spec (GF := netDistGF) (hG := hG))
    (wp_ServeClient : github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient.spec
      (GF := netDistGF) (hG := hG) (I := KIn) (O := BStr)) :
    clientNode.spec γ γk c := by
  intro asl
  wp_start as ⟨Hasl, Hres⟩
  iunfold clientRes at Hres
  icases Hres with ⟨Hsh, Hfr, Hcfr, #Hboot, #Hpool, #Hlink, #Hra, #Hmap⟩
  ihave #Hrp : isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_newClient asl $$ [$Hasl $Hsh $Hfr $Hcfr] as %s #Hs
  · iframe #
  ipersist s
  ipersist c
  wp_apply (wp_Codec (sysK γk) swEop) as %cd #Hcd
  wp_apply wp_callTime as %d -
  wp_apply wp_ServeClient (RBase.svc (Gg := hG.goose_globalGS) (swRK γk)) _ _ _ _ cd d
    (fun sys => iprop(⌜sys = sysV s⌝)) $$ [] as ⟨⟩
  iframe #
  isplit
  · iapply codecOk_wireOk $$ Hcd
  isplit
  · iapply opMaybe_svcOp
    unfold opMaybe
    iintro %sys %i %Ψ
    iintro !> %Φr ⟨%Hsys, Hupd, -⟩ HΦr
    subst Hsys
    wp_auto
    wp_apply wp_op s i Ψ $$ [$Hupd] as %o Ho
    · iframe #
    try wp_auto
    iapply HΦr
    isplitr
    · itrivial
    icases Ho with (%Ho | ⟨%w, %Hw, HΨ⟩)
    · subst Ho
      iright
      ipureintro; rfl
    · subst Hw
      ileft
      iexists w
      iframe HΨ
      ipureintro; rfl
  · iintro %Φr HΦr
    wp_auto
    iapply HΦr
    ipureintro; rfl

theorem Client.wp_proof (wp_clientNode : ∀ γ γk c, c < 6 → clientNode.spec γ γk c)
    (wp_Addrs : AddrsC.spec) (wp_ClientAddrs : ClientAddrs.spec) :
    Client.spec (hG := hG) := by
  intro γ γk c hc
  wp_start as Hres
  wp_auto
  wp_apply wp_Addrs as %asl Hasl
  wp_apply wp_ClientAddrs as %csl Hcsl
  have hlen : clientAddrs.length = 6 := rfl
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcsl
  have hcsl : sint.Z csl.len = 6 := by have := Hcl.1; rw [hlen] at this; word
  list_elem clientAddrs c as a
  have hca : a = clientAddrs.getD c go!"" := by
    simp [List.getD_eq_getElem?_getD, Ha_lookup]
  subst hca
  rw [ite_eq_left ⟨by word, by rw [hcsl]; word⟩]
  wp_apply wp_load_slice_index csl (sint.Z (W64 (c : Int))) clientAddrs _ _ (by word) $$ [Hcsl]
    as Hcsl
  · iframe; ipureintro
    rw [show (sint.Z (W64 (c : Int))).toNat = c by word]; exact Ha_lookup
  wp_apply wp_clientNode γ γk c hc asl $$ [$Hasl $Hres] as Hf
  iexfalso; iexact Hf

end proof

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
