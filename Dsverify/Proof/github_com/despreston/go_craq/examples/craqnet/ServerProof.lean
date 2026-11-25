/-
The craq kit's server machines (kit.go's `Server`, `runNode`) and the codec's registration
(`Register`): over Net's `SetCodec`, go-craq's packages' specs (`Specs.lean`, taken as theorem
arguments as paxos's `KitProof.lean` does), the bindings' receivers (`Netrpc/BindingsProof.lean`)
and net/rpc over HTTP's server side (Net's `RegisterName.spec_fresh` and `HandleHTTP.spec`, proved,
and `RpcHttpServe`'s `ListenAndServe`, H3).

Preconditions from the machine's boot (`rpcBootRes`, `BootLinked.lean`): its codec registry at its
initial state (`codecFresh`: `codecUnset` and `codecMu`'s mutex), its mux at its initial state
(`muxOwner []`), its `DefaultServer` with an owned, empty registry (`defaultSrvFresh`), and its
net/rpc and net/http variables (`rpcEnv`); and the machine's thread bound `threadBound ≤ 2 ^ 31`
(`HandleHTTP`, `ListenAndServe`: net/rpc's server).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.KitSpecs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.BindingsProof
public import Net.Spec.net.rpc.SetCodec
public import Net.Spec.net.rpc.RegisterName
public import Net.Spec.net.rpc.HandleHTTP

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.despreston.go_craq.examples.craqnet

open github_com.despreston.go_craq github_com.despreston.go_craq.netrpcP

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions]
variable [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

/-- The coordinator's methods accept the server's error answers. -/
theorem coordSpec_errOk (γ : CraqNames) (ch : List GoString) :
    ⊢ net.rpc.errOk (coordSpec (G := hG.goose_globalGS) γ ch) := by
  unfold net.rpc.errOk
  iintro !> %m %args %Φ %msg %Hmsg HS
  by_cases h1 : m = go!"AddNode"
  · subst h1
    rw [coordSpec_AddNode]
    icases HS with ⟨%a, -, -, ⟨-, HE⟩⟩
    imodintro
    unfold errOk
    iapply HE
    ipureintro; exact net.rpc.srvErrMsg_ne msg Hmsg
  by_cases h2 : m = go!"Write"
  · subst h2
    rw [coordSpec_Write]
    icases HS with ⟨%k, %x, %Q, -, -, ⟨-, HE⟩⟩
    imodintro
    unfold errOk
    iapply HE
    ipureintro; exact net.rpc.srvErrMsg_ne msg Hmsg
  by_cases h3 : m = go!"RemoveNode"
  · subst h3
    rw [coordSpec_RemoveNode]
    icases HS with ⟨%a, -, ⟨-, HE⟩⟩
    imodintro
    iapply HE
  · have hF : coordSpec (G := hG.goose_globalGS) γ ch m args Φ = iprop(False) := by
      unfold coordSpec; simp [h1, h2, h3]
    rw [hF]
    icases HS with ⟨⟩

/-- Node.Read's not-found message is not one of net/rpc's server's own error answers (F3). -/
theorem notFoundMsg_not_srv : ¬ net.rpc.srvErrMsg notFoundMsg := by
  unfold net.rpc.srvErrMsg net.rpc.rdErrMsg net.opErrMsg notFoundMsg
  rintro (⟨sm, h⟩ | ⟨sm, h⟩ | ⟨sm, h⟩ | h | h | h | h | ⟨s1, s2, h⟩) <;>
    (revert h; simp (config := { decide := true }) [List.append_assoc])

/-- **F3, discharged**: the chain node's methods accept the server's own error answers
(`srvErrMsg`): each method's `errOk` (every non-empty message), and Read's other messages, which
exclude its not-found (`notFoundMsg_not_srv`). -/
theorem nodeSpec_errOk (γ : CraqNames) (ch : List GoString) (a : GoString) :
    ⊢ net.rpc.errOk (nodeSpec (G := hG.goose_globalGS) γ ch a) := by
  unfold net.rpc.errOk
  iintro !> %m %args %Φ %msg %Hmsg HS
  have hne : msg ≠ [] := net.rpc.srvErrMsg_ne msg Hmsg
  by_cases h1 : m = go!"Ping"
  · subst h1
    rw [nodeSpec_Ping]
    icases HS with ⟨-, ⟨-, HE⟩⟩
    imodintro
    unfold errOk
    iapply HE
    ipureintro; exact hne
  by_cases h2 : m = go!"Update"
  · subst h2
    rw [nodeSpec_Update]
    icases HS with ⟨%md, %r, -, -, -, ⟨-, HE⟩⟩
    imodintro
    unfold errOk
    iapply HE
    ipureintro; exact hne
  by_cases h3 : m = go!"Write"
  · subst h3
    rw [nodeSpec_Write]
    icases HS with ⟨%k, %x, %v, -, -, ⟨-, HE⟩⟩
    imodintro
    unfold errOk
    iapply HE
    ipureintro; exact hne
  by_cases h4 : m = go!"Commit"
  · subst h4
    rw [nodeSpec_Commit]
    icases HS with ⟨%k, %v, -, -, ⟨-, HE⟩⟩
    imodintro
    unfold errOk
    iapply HE
    ipureintro; exact hne
  by_cases h5 : m = go!"LatestVersion"
  · subst h5
    rw [nodeSpec_LatestVersion]
    icases HS with ⟨%k, %Q, -, -, ⟨-, HE⟩⟩
    imodintro
    unfold errOk
    iapply HE
    ipureintro; exact hne
  by_cases h6 : m = go!"Read"
  · subst h6
    rw [nodeSpec_Read]
    icases HS with ⟨%k, %Q, -, -, HC⟩
    unfold readCont
    icases HC with ⟨-, ⟨-, HE⟩⟩
    imodintro
    iapply HE
    ipureintro
    exact ⟨hne, fun h => notFoundMsg_not_srv (h ▸ Hmsg)⟩
  by_cases h7 : m = go!"FwdPropagate"
  · subst h7
    rw [nodeSpec_Fwd]
    icases HS with ⟨%req, -, ⟨-, HE⟩⟩
    imodintro
    unfold errOk
    iapply HE
    ipureintro; exact hne
  by_cases h8 : m = go!"BackPropagate"
  · subst h8
    rw [nodeSpec_Back]
    icases HS with ⟨%req, %L, -, -, ⟨-, HE⟩⟩
    imodintro
    unfold errOk
    iapply HE
    ipureintro; exact hne
  · have hF : nodeSpec (G := hG.goose_globalGS) γ ch a m args Φ = iprop(False) := by
      unfold nodeSpec; simp [h1, h2, h3, h4, h5, h6, h7, h8]
    rw [hF]
    icases HS with ⟨⟩

/-- The coordinator's registration serves its address. -/
theorem srvServes_coord (cfg : Cfg GF) (γs : GName)
    (hss : cfg.W.SS = craqSS cfg.γ cfg.cAddr cfg.chain) :
    net.rpc.svcReg γs craqCodec go!"RPC" (coordSpec cfg.γ cfg.chain) ⊢
      net.rpc.srvServes γs craqCodec cfg.W cfg.cAddr := by
  iintro #Hreg
  unfold net.rpc.srvServes
  iintro !> %svc %S %Hs
  rw [hss] at Hs
  unfold craqSS at Hs
  by_cases hsvc : svc = go!"RPC"
  · subst hsvc
    simp only [if_true] at Hs
    cases Hs
    iframe Hreg
    iapply coordSpec_errOk
  · simp [hsvc] at Hs

/-- **The coordinator's machine**, `Server(1)`. -/
theorem wp_Server1 [rs : RpcHttpServe GF]
    (wp_RegisterName : net.rpc.RegisterName.spec_fresh (GF := GF) (hG := hG))
    (wp_HandleHTTP : net.rpc.HandleHTTP.spec (GF := GF) (hG := hG))
    (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG))
    (wp_cNew : coordinator.wp_New.spec (GF := GF) (hG := hG))
    (wp_cStart : coordinator.wp_Start.spec (GF := GF) (hG := hG))
    (h_csvc : coordinator.coord_svc.spec (GF := GF) (hG := hG))
    (h_fact : netrpc.factory.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (htb : threadBound GF ≤ 2 ^ 31)
    (hc : cfg.cAddr = go!"127.0.0.1:7501") (hlen : cfg.chain.length < 2 ^ 31 - 1) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ codecFresh ∗ muxOwner [] ∗
        rpcEnv ∗ defaultSrvFresh ∗ craqCtx cfg ∗ coordRes cfg }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.Server)) (Val #(W64 1)))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, #Hre, Hfresh, #Hctx, Hres⟩
  iunfold defaultSrvFresh at Hfresh
  icases Hfresh with ⟨%γs, %γf, #Hdsv, Hso⟩
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.net.rpc $$ []
  · iPkgInit
  ihave #Hhttp : isPkgInit (PROP := IProp GF) pkg_id.net.http $$ []
  · iPkgInit
  ihave #Hco : isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator $$ []
  · iPkgInit
  ihave #Hnr : isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Register wp_SetCodec $$ [Hcf] as #Hcs
  · iframe
  wp_apply wp_ServerAddrs as %sl Hsl
  ihave %Hal := ownSlice_len _ _ _ $$ Hsl
  have hb : 0 ≤ sint.Z (W64 1 - W64 1) ∧ sint.Z (W64 1 - W64 1) < sint.Z sl.len := by
    have := Hal.1; simp only [serverAddrs, List.length_cons, List.length_nil] at this; word
  simp only [hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl (sint.Z (W64 1 - W64 1)) serverAddrs _ go!"127.0.0.1:7501" hb.1
    $$ [Hsl] with Hsl
  · iframe; ipureintro; rfl
  (try wp_auto)
  ihave #Hready : rpcReady $$ []
  · unfold rpcReady; iframe Hrpc Hcs Hre
  ihave #Hfact := h_fact cfg $$ [Hnr Hready Hctx]
  · iframe Hnr Hready Hctx
  wp_apply wp_cNew cfg _ $$ [Hres] as %c #Hc
  · iframe Hctx Hfact Hres
    ipureintro; exact hlen
  (try wp_auto)
  ipersist «cb»
  ihave #Hsvc := h_csvc cfg c $$ [Hco Hc]
  · iframe Hco Hc
  ihave #HcB : coordB cfg cb_ptr (ptrIface coordinator.Coordinator.ty c) $$ []
  · unfold coordB
    iframe Hnr Hpkg Hcs Hsvc
    iexact «cb»
  ihave #Hrcv := coordRcv_ok cfg cb_ptr _ $$ HcB
  wp_apply wp_RegisterName γs γf ∅ craqCodec go!"RPC" _ (coordSpec cfg.γ cfg.chain) go!"CoordinatorBinding"
    false (by decide) $$ [Hso] as %err ⟨%Herr, #Hreg, -⟩
  · iframe Hcs Hrcv Hdsv Hso
    ipureintro; simp [GMap.mem_iff]
  subst Herr
  wp_auto
  unfold craqCtx
  icases Hctx with ⟨-, %Hss, Haddrs⟩
  icases BigSepL.bigSepL_cons.1 $$ Haddrs with ⟨#Ha, -⟩
  ihave #Hserves := srvServes_coord cfg γs Hss.1 $$ Hreg
  unfold rpcEnv
  icases Hre with ⟨%Hrb, #Hse, #Hhe, #Hcon⟩
  rw [hc]
  wp_apply wp_HandleHTTP γs craqCodec cfg.W (fun x => x = go!"127.0.0.1:7501") [] (by simp) (by simp) $$ [Hmux]
    as ⟨Hmux, #Hmh⟩
  · isplitr
    · ipureintro; exact htb
    isplitr
    · iexact Hhttp
    isplitl [Hmux]
    · iexact Hmux
    isplitr
    · iapply net.rpc.defaultServerO_any $$ Hdsv
    isplitr
    · iintro !> %x %hx
      subst hx
      iframe Hserves
      iapply httpRpcAddr_hs $$ Ha
    isplitr
    · iexact Hse
    isplitr
    · iexact Hcs
    · iexact Hcon
  (try wp_auto)
  wp_apply wp_fork $$ []
  · wp_apply wp_cStart cfg c $$ []
    · iframe Hc
    ipureintro; first | rfl | simp | decide
  (try wp_auto)
  wp_apply rs.ListenAndServe cfg.W (fun x => x = go!"127.0.0.1:7501") go!"127.0.0.1:7501" $$ []
    as %e -
  · isplitr
    · ipureintro; exact htb
    isplitr
    · ipureintro; exact ⟨by decide, rfl⟩
    isplitr
    · iexact Ha
    · iexact Hmh
  (try wp_auto)
  iapply HΦ
  itrivial

/-- The chain node's registration serves its address (given that its methods accept the
server's error answers: finding F3). -/
theorem srvServes_node (cfg : Cfg GF) (a : GoString) (γs : GName)
    (hss : cfg.W.SS = craqSS cfg.γ cfg.cAddr cfg.chain) (ha : a ∈ cfg.chain) (hac : a ≠ cfg.cAddr) :
    net.rpc.svcReg γs craqCodec go!"RPC" (nodeSpec cfg.γ cfg.chain a) ∗
      net.rpc.errOk (nodeSpec cfg.γ cfg.chain a) ⊢
      net.rpc.srvServes γs craqCodec cfg.W a := by
  iintro ⟨#Hreg, #HE⟩
  unfold net.rpc.srvServes
  iintro !> %svc %S %Hs
  rw [hss] at Hs
  unfold craqSS at Hs
  by_cases hsvc : svc = go!"RPC"
  · subst hsvc
    simp only [if_true, hac, if_false, ha] at Hs
    cases Hs
    iframe Hreg HE
  · simp [hsvc] at Hs

theorem rpcReady_codecSet : rpcReady (hG := hG) ⊢ net.rpc.codecSet craqCodec := by
  unfold rpcReady; iintro ⟨-, #H, -⟩; iexact H

theorem rpcReady_env : rpcReady (hG := hG) ⊢ rpcEnv := by
  unfold rpcReady; iintro ⟨-, -, #H⟩; iexact H

/-- `runNode(id, a, conf)`: chain machine `id`'s node at `a`. -/
theorem wp_runNode [rs : RpcHttpServe GF]
    (wp_RegisterName : net.rpc.RegisterName.spec_fresh (GF := GF) (hG := hG))
    (wp_HandleHTTP : net.rpc.HandleHTTP.spec (GF := GF) (hG := hG))
    (wp_kvNew : kv.wp_New.spec (GF := GF) (hG := hG))
    (wp_nNew : node.wp_New.spec (GF := GF) (hG := hG))
    (wp_nStart : node.wp_Start.spec (GF := GF) (hG := hG))
    (h_nsvc : node.node_svc.spec (GF := GF) (hG := hG))
    (h_fact : netrpc.factory.spec (GF := GF) (hG := hG))
    (wp_NewCC : netrpc.wp_NewCoordinatorClient.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (id : w64) (a : GoString) (conf : Conf) (htb : threadBound GF ≤ 2 ^ 31)
    (hc : cfg.cAddr = go!"127.0.0.1:7501") (ha : a ∈ cfg.chain) (hok : addrOk a = true) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ rpcReady ∗ muxOwner [] ∗
        defaultSrvFresh ∗ craqCtx cfg ∗ nodeRes cfg a ∗ joinTicket cfg.γ a ∗
        net.rpc.errOk (nodeSpec cfg.γ cfg.chain a) }}
      (App (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.runNode)) (Val #id))
        (Val #a)) (Val #conf))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hready, Hmux, Hfresh, #Hctx, Hres, Htk, #HE⟩
  iunfold defaultSrvFresh at Hfresh
  icases Hfresh with ⟨%γs, %γf, #Hdsv, Hso⟩
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.net.rpc $$ []
  · iPkgInit
  ihave #Hhttp : isPkgInit (PROP := IProp GF) pkg_id.net.http $$ []
  · iPkgInit
  ihave #Hno : isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node $$ []
  · iPkgInit
  ihave #Hkv : isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store.kv $$ []
  · iPkgInit
  ihave #Hnr : isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_ServerAddrs as %sl Hsl
  ihave %Hal := ownSlice_len _ _ _ $$ Hsl
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    have := Hal.1; simp only [serverAddrs, List.length_cons, List.length_nil] at this; word
  simp only [hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl (sint.Z (W64 0)) serverAddrs _ go!"127.0.0.1:7501" hb.1
    $$ [Hsl] with Hsl
  · iframe; ipureintro; rfl
  (try wp_auto)
  wp_apply wp_kvNew as %st ⟨%γst, #Hst, Hso⟩
  (try wp_auto)
  wp_apply wp_NewCC cfg as %cc Hcc
  · iframe Hready Hctx
  (try wp_auto)
  ihave #Hfact := h_fact cfg $$ [Hnr Hready Hctx]
  · iframe Hnr Hready Hctx
  rw [← hc]
  wp_apply wp_nNew cfg a _ γst _ cc $$ [Hres Hso Hcc] as %n ⟨#Hn, Hnst⟩
  · iframe Hctx Hres Hso Hcc Hfact Hst
    ipureintro; exact ha
  (try wp_auto)
  ipersist «nb»
  ihave #Hsvc := h_nsvc cfg n a $$ [Hno Hn]
  · iframe Hno Hn
  ihave #Hcs := rpcReady_codecSet $$ Hready
  ihave #Hre := rpcReady_env $$ Hready
  ihave #HnB : nodeB cfg nb_ptr (ptrIface node.Node.ty n) a $$ []
  · unfold nodeB
    iframe Hnr Hpkg Hcs Hsvc
    iexact «nb»
  ihave #Hrcv := nodeRcv_ok cfg nb_ptr _ a $$ HnB
  wp_apply wp_RegisterName γs γf ∅ craqCodec go!"RPC" _ (nodeSpec cfg.γ cfg.chain a) go!"NodeBinding"
    false (by decide) $$ [Hso] as %err ⟨%Herr, #Hreg, -⟩
  · iframe Hcs Hrcv Hdsv Hso
    ipureintro; simp [GMap.mem_iff]
  subst Herr
  wp_auto
  unfold craqCtx
  icases Hctx with ⟨-, %Hss, Haddrs⟩
  icases BigSepL.bigSepL_cons.1 $$ Haddrs with ⟨-, Haddrs⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
  ihave #Ha := BigSepL.bigSepL_lookup hi $$ Haddrs
  have hac : a ≠ cfg.cAddr := fun h => Hss.2.2.1 (h ▸ ha)
  ihave #Hserves := srvServes_node cfg a γs Hss.1 ha hac $$ [Hreg HE]
  · iframe Hreg HE
  unfold rpcEnv
  icases Hre with ⟨%Hrb, #Hse, #Hhe, #Hcon⟩
  wp_apply wp_HandleHTTP γs craqCodec cfg.W (fun x => x = a) [] (by simp) (by simp) $$ [Hmux] as ⟨Hmux, #Hmh⟩
  · isplitr
    · ipureintro; exact htb
    isplitr
    · iexact Hhttp
    isplitl [Hmux]
    · iexact Hmux
    isplitr
    · iapply net.rpc.defaultServerO_any $$ Hdsv
    isplitr
    · iintro !> %x %hx
      subst hx
      iframe Hserves
      iapply httpRpcAddr_hs $$ Ha
    isplitr
    · iexact Hse
    isplitr
    · iexact Hcs
    · iexact Hcon
  (try wp_auto)
  wp_apply wp_fork $$ [Hnst Htk «id» «conf» «n»]
  · wp_auto
    wp_func_call
    wp_call
    repeat (first | wp_auto | (wp_if_destruct))
    all_goals (
      wp_apply time.wp_Sleep
      (try wp_auto)
      wp_apply wp_nStart cfg n a $$ [Hnst Htk]
      · iframe Hn Hnst Htk
      iintro %err -
      wp_auto
      ipureintro; first | rfl | simp)
  (try wp_auto)
  wp_apply rs.ListenAndServe cfg.W (fun x => x = a) a $$ [] as %e -
  · isplitr
    · ipureintro; exact htb
    isplitr
    · ipureintro; exact ⟨hok, rfl⟩
    isplitr
    · iexact Ha
    · iexact Hmh
  (try wp_auto)
  iapply HΦ
  itrivial

/-- The server addresses are valid listen addresses. -/
theorem serverAddrs_addrOk : serverAddrs.all addrOk = true := by decide

/-- **A server machine**, `Server(id)`: the coordinator (`wp_Server1`), or chain machine `id`:
its codec registered, it waits for the configuration (`awaitConf` in a goroutine), runs its node
(`wp_runNode`) if `id ≤ N + 1`, then idles. The finding's premise: the nodes' `errOk` (F3, `HE`;
discharged by `nodeSpec_errOk`). F1 is discharged: RemoveNode's method obligation is proved
(`cnewArg_RemoveNode`, over `callRet`'s `errAny` branch). -/
theorem Server.wp_proof [rs : RpcHttpServe GF]
    (wp_RegisterName : net.rpc.RegisterName.spec_fresh (GF := GF) (hG := hG))
    (wp_HandleHTTP : net.rpc.HandleHTTP.spec (GF := GF) (hG := hG))
    (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG))
    (wp_cNew : coordinator.wp_New.spec (GF := GF) (hG := hG))
    (wp_cStart : coordinator.wp_Start.spec (GF := GF) (hG := hG))
    (h_csvc : coordinator.coord_svc.spec (GF := GF) (hG := hG))
    (h_fact : netrpc.factory.spec (GF := GF) (hG := hG))
    (wp_kvNew : kv.wp_New.spec (GF := GF) (hG := hG))
    (wp_nNew : node.wp_New.spec (GF := GF) (hG := hG))
    (wp_nStart : node.wp_Start.spec (GF := GF) (hG := hG))
    (h_nsvc : node.node_svc.spec (GF := GF) (hG := hG))
    (wp_NewCC : netrpc.wp_NewCoordinatorClient.spec (GF := GF) (hG := hG))
    (wp_awaitConf : awaitConf.spec (GF := GF) (hG := hG))
    (HE : ∀ (cfg : Cfg GF) (a : GoString),
      ⊢ net.rpc.errOk (nodeSpec (G := hG.goose_globalGS) cfg.γ cfg.chain a)) :
    Server.spec (GF := GF) (hG := hG) := by
  intro cfg id htb hcfg h1 h6
  have hc : cfg.cAddr = go!"127.0.0.1:7501" := hcfg.1
  by_cases hid : id = W64 1
  · subst hid
    have hres : serverRes cfg (uint.nat (W64 1)) = coordRes cfg := by simp [serverRes]
    rw [hres]
    exact wp_Server1 wp_RegisterName wp_HandleHTTP wp_SetCodec wp_cNew wp_cStart h_csvc h_fact cfg htb hc
      (by rw [hcfg.2]; decide)
  have hn1 : uint.nat id ≠ 1 := fun h => hid (by word)
  obtain ⟨a, ha, hmem⟩ := serverAddrs_chain (uint.nat id - 1) (by omega) (by omega)
  have hga : serverAddrs.getD (uint.nat id - 1) [] = a := by
    simp [List.getD_eq_getElem?_getD, ha]
  have hres : serverRes cfg (uint.nat id) = iprop(nodeRes cfg a ∗ joinTicket cfg.γ a ∗
      addrProto (Gg := hG.goose_globalGS) (confAddrs.getD (5 + uint.nat id - 1) []) confProto
        confProto) := by
    unfold serverRes; rw [if_neg hn1, hga]
  rw [hres]
  wp_start as ⟨Hcf, Hmux, #Henv, Hdsv, #Hctx, Hres, Htk, #Hca⟩
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.net.rpc $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Register wp_SetCodec $$ [Hcf] as #Hcs
  · iframe
  wp_apply wp_ServerAddrs as %sl Hsl
  ihave %Hal := ownSlice_len _ _ _ $$ Hsl
  have hsl : sint.Z sl.len = 6 := by
    have := Hal.1; simp only [serverAddrs, List.length_cons, List.length_nil] at this; word
  rw [ite_eq_left ⟨by word, by rw [hsl]; word⟩]
  wp_apply wp_load_slice_index sl (sint.Z (id - W64 1)) serverAddrs _ a (by word) $$ [Hsl]
    with Hsl
  · iframe; ipureintro; rw [show (sint.Z (id - W64 1)).toNat = uint.nat id - 1 by word]; exact ha
  (try wp_auto)
  wp_if_destruct
  · exact absurd (by word) hn1
  wp_apply wp_make_conf_chan as %ch ⟨%γch, #Hbag⟩
  wp_apply wp_ConfAddrs as %cfgs Hcfgs
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcfgs
  have hcl : sint.Z cfgs.len = 11 := by
    have := Hcl.1; simp only [confAddrs, List.length_cons, List.length_nil] at this; word
  have hidx : (sint.Z (W64 5 + id - W64 1)).toNat = 5 + uint.nat id - 1 := by word
  have hcn : 5 + uint.nat id - 1 < confAddrs.length := by
    simp only [confAddrs, List.length_cons, List.length_nil]; omega
  list_elem confAddrs (5 + uint.nat id - 1) as ca
  have hca : ca = confAddrs.getD (5 + uint.nat id - 1) [] := by
    rw [List.getD_eq_getElem?_getD, Hca_lookup]; rfl
  subst hca
  rw [ite_eq_left ⟨by word, by rw [hcl]; word⟩]
  wp_apply wp_load_slice_index cfgs (sint.Z (W64 5 + id - W64 1)) confAddrs _ _ (by word)
    $$ [Hcfgs] with Hcfgs
  · iframe; ipureintro; rw [hidx]; exact Hca_lookup
  wp_apply wp_fork $$ []
  · wp_apply wp_awaitConf _ γch ch $$ [] as %hf
    · iframe #
    exact hf.elim
  wp_apply wp_recv_msg γch ch $$ [] as %m Hm
  · iframe #
  unfold msgOk
  icases Hm with ⟨%Hcok, -⟩
  (try wp_auto)
  wp_if_destruct
  · wp_apply wp_runNode wp_RegisterName wp_HandleHTTP wp_kvNew wp_nNew wp_nStart h_nsvc h_fact wp_NewCC cfg id a _ htb hc
      (by rw [hcfg.2]; exact hmem)
      (List.all_eq_true.1 serverAddrs_addrOk a (List.mem_of_mem_tail hmem)) $$ [Hmux Hdsv Hres Htk]
    · iframe Hmux Hdsv Hres Htk
      iframe #
      isplitr
      · unfold rpcReady; iframe #
      iapply HE
    (try wp_auto)
    ihave HI : (True : IProp GF) $$ []
    · itrivial
    wp_for HI
    (try rw [if_pos (by simp)])
    (try wp_auto)
    wp_apply time.wp_Sleep
    wp_for_post
    iframe
  · ihave HI : (True : IProp GF) $$ []
    · itrivial
    wp_for HI
    (try rw [if_pos (by simp)])
    (try wp_auto)
    wp_apply time.wp_Sleep
    wp_for_post
    iframe

end proof

end github_com.despreston.go_craq.examples.craqnet
end Perennial
