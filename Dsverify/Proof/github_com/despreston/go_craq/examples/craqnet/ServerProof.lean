/-
The craq kit's server machines (kit.go's `Server`, `runNode`) and the codec's registration
(`Register`): over Net's `SetCodec`, go-craq's packages' specs (`Specs.lean`, taken as theorem
arguments as paxos's `KitProof.lean` does), the bindings' receivers (`Netrpc/BindingsProof.lean`)
and net/rpc over HTTP's server side (`RpcHttpServe`, H2/H3).

Open points carried as preconditions (notes/dsv-craq.md, P5): a machine's codec registry at its
initial state (`codecFresh`: `codecUnset` and `codecMu`'s mutex, from net/rpc's initialization,
which Net has not proved), its mux at its initial state (`muxOwner []`, H4 open point 2), and
net/rpc's server variables (`srvEnv`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.KitDefs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.BindingsProof
public import Net.Spec.net.rpc.SetCodec

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
variable [ra : RpcHttpAddr GF] [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

/-- A machine's codec registry at its initial state (net/rpc's initialization's; open point). -/
def codecFresh : IProp GF :=
  iprop(sync.isMutex (globalAddr net.rpc.codecMu) net.rpc.codecInv ∗ net.rpc.codecUnset)

/-- `Register()`: the kit's codec registered. -/
theorem wp_Register (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ codecFresh }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.Register)) (Val #()))
    {{ RET #(); net.rpc.codecSet craqCodec }} := by
  unfold codecFresh
  wp_start as ⟨#Hmu, Hun⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$a0»
  ipersist «$a0»
  wp_apply wp_SetCodec craqCodec _ $$ [Hun]
  · isplitr
    · iexact Hmu
    isplitl [Hun]
    · iexact Hun
    isplitr
    · unfold net.rpc.codecIs
      iexists _
      iframe «$a0»
      isplitr
      · iapply craqCodec_encOk
      isplitr
      · iapply craqCodec_decOk
      · iapply craqCodec_rcvOk
    · ipureintro; exact Hnn
  iintro #Hcs
  wp_auto
  iapply HΦ
  iexact Hcs

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
    ipureintro; exact Hmsg
  by_cases h2 : m = go!"Write"
  · subst h2
    rw [coordSpec_Write]
    icases HS with ⟨%k, %x, %Q, -, -, ⟨-, HE⟩⟩
    imodintro
    unfold errOk
    iapply HE
    ipureintro; exact Hmsg
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

instance muxRoute_persistent [rs : RpcHttpServe GF] (p : GoString) (h : GoInterface) :
    Persistent (RpcHttpServe.muxRoute (GF := GF) p h) := rs.muxRoute_pers p h

instance handlerOk_persistent [rs : RpcHttpServe GF] (h : GoInterface) (p : GoString)
    (W : net.rpc.RpcWorld GF) (a : GoString) :
    Persistent (RpcHttpServe.handlerOk (GF := GF) h p W a) := rs.handlerOk_pers h p W a

/-- RemoveNode's method obligation (finding F1: a premise until Net's `callRet` admits `errAny`). -/
abbrev removeNodeOk.spec (cfg : Cfg GF) : Prop :=
  ∀ (b : Loc) (svc : GoInterface), coordB cfg b svc ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.CoordinatorBinding.ty b)
      (coordSpec cfg.γ cfg.chain go!"RemoveNode")
      (mOf examples.craqnet.rpcNewArg_r1_RemoveNode examples.craqnet.rpcNewReply_r1_RemoveNode
        examples.craqnet.rpcCall_r1_RemoveNode)

/-- **The coordinator's machine**, `Server(1)`. -/
theorem wp_Server1 [rs : RpcHttpServe GF]
    (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG))
    (wp_cNew : coordinator.wp_New.spec (GF := GF) (hG := hG))
    (wp_cStart : coordinator.wp_Start.spec (GF := GF) (hG := hG))
    (h_csvc : coordinator.coord_svc.spec (GF := GF) (hG := hG))
    (h_fact : netrpc.factory.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (HRN : removeNodeOk.spec cfg)
    (hc : cfg.cAddr = go!"127.0.0.1:7501") (hlen : cfg.chain.length < 2 ^ 31 - 1) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ codecFresh ∗ RpcHttpServe.muxOwner [] ∗
        net.rpc.srvEnv ∗ craqCtx cfg ∗ coordRes cfg }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.Server)) (Val #(W64 1)))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, #Henv, #Hctx, Hres⟩
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
  · unfold rpcReady; iframe Hrpc Hcs
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
  ihave #Hrcv := coordRcv_ok cfg cb_ptr _ (HRN _ _) $$ HcB
  wp_apply rs.RegisterName craqCodec go!"RPC" _ (coordSpec cfg.γ cfg.chain) go!"CoordinatorBinding" false
    (by decide) $$ [] as %err Herr
  · iframe Hcs Hrcv
  icases Herr with (⟨%Herr, %srv, %γs, #Hds, #Hsrv, #Hreg⟩ | %Herr)
  · subst Herr
    wp_auto
    wp_apply rs.HandleHTTP [] $$ [Hmux] as ⟨Hmux, %srv', #Hds', #Hroute⟩
    · iframe Hmux
      ipureintro; simp
    ihave %Hss := typedPointsto_agree_wand _ _ _ _ _ $$ Hds Hds'
    subst Hss
    (try wp_auto)
    wp_apply wp_fork $$ []
    · wp_apply wp_cStart cfg c $$ []
      · iframe Hc
      ipureintro; first | rfl | simp | decide
    (try wp_auto)
    unfold craqCtx
    icases Hctx with ⟨-, %Hss, Haddrs⟩
    icases BigSepL.bigSepL_cons.1 $$ Haddrs with ⟨#Ha, -⟩
    ihave #Hserves := srvServes_coord cfg γs Hss.1 $$ Hreg
    rw [hc]
    ihave #Hh := rs.ServeHTTP srv γs craqCodec cfg.W go!"127.0.0.1:7501" $$ [Hsrv Hserves Henv Hcs]
    · iframe Hsrv Hserves Henv Hcs
    wp_apply rs.ListenAndServe cfg.W go!"127.0.0.1:7501" defaultRPCPath (serverHandler srv) $$ []
      as %e -
    · iframe Ha Hroute Hh
      ipureintro; decide
    (try wp_auto)
    iapply HΦ
    itrivial
  · have hne : err ≠ interface.nil := Herr
    cases err with
    | nil => exact absurd rfl hne
    | ok e =>
      wp_auto
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
  unfold rpcReady; iintro ⟨-, #H⟩; iexact H

/-- `runNode(id, a, conf)`: chain machine `id`'s node at `a`. -/
theorem wp_runNode [rs : RpcHttpServe GF]
    (wp_kvNew : kv.wp_New.spec (GF := GF) (hG := hG))
    (wp_nNew : node.wp_New.spec (GF := GF) (hG := hG))
    (wp_nStart : node.wp_Start.spec (GF := GF) (hG := hG))
    (h_nsvc : node.node_svc.spec (GF := GF) (hG := hG))
    (h_fact : netrpc.factory.spec (GF := GF) (hG := hG))
    (wp_NewCC : netrpc.wp_NewCoordinatorClient.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (id : w64) (a : GoString) (conf : Conf)
    (hc : cfg.cAddr = go!"127.0.0.1:7501") (ha : a ∈ cfg.chain) (hok : addrOk a = true) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ rpcReady ∗ RpcHttpServe.muxOwner [] ∗
        net.rpc.srvEnv ∗ craqCtx cfg ∗ nodeRes cfg a ∗ joinTicket cfg.γ a ∗
        net.rpc.errOk (nodeSpec cfg.γ cfg.chain a) }}
      (App (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.runNode)) (Val #id))
        (Val #a)) (Val #conf))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hready, Hmux, #Henv, #Hctx, Hres, Htk, #HE⟩
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.net.rpc $$ []
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
  ihave #HnB : nodeB cfg nb_ptr (ptrIface node.Node.ty n) a $$ []
  · unfold nodeB
    iframe Hnr Hpkg Hcs Hsvc
    iexact «nb»
  ihave #Hrcv := nodeRcv_ok cfg nb_ptr _ a $$ HnB
  wp_apply rs.RegisterName craqCodec go!"RPC" _ (nodeSpec cfg.γ cfg.chain a) go!"NodeBinding" false
    (by decide) $$ [] as %err Herr
  · iframe Hcs Hrcv
  icases Herr with (⟨%Herr, %srv, %γs, #Hds, #Hsrv, #Hreg⟩ | %Herr)
  · subst Herr
    wp_auto
    wp_apply rs.HandleHTTP [] $$ [Hmux] as ⟨Hmux, %srv', #Hds', #Hroute⟩
    · iframe Hmux
      ipureintro; simp
    ihave %Hss := typedPointsto_agree_wand _ _ _ _ _ $$ Hds Hds'
    subst Hss
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
    unfold craqCtx
    icases Hctx with ⟨-, %Hss, Haddrs⟩
    icases BigSepL.bigSepL_cons.1 $$ Haddrs with ⟨-, Haddrs⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
    ihave #Ha := BigSepL.bigSepL_lookup hi $$ Haddrs
    have hac : a ≠ cfg.cAddr := fun h => Hss.2.2.1 (h ▸ ha)
    ihave #Hserves := srvServes_node cfg a γs Hss.1 ha hac $$ [Hreg HE]
    · iframe Hreg HE
    ihave #Hh := rs.ServeHTTP srv γs craqCodec cfg.W a $$ [Hsrv Hserves Henv Hcs]
    · iframe Hsrv Hserves Henv Hcs
    wp_apply rs.ListenAndServe cfg.W a defaultRPCPath (serverHandler srv) $$ []
      as %e -
    · iframe Ha Hroute Hh
      ipureintro; exact hok
    (try wp_auto)
    iapply HΦ
    itrivial
  · have hne : err ≠ interface.nil := Herr
    cases err with
    | nil => exact absurd rfl hne
    | ok e =>
      wp_auto
      iapply HΦ
      itrivial

end proof

end github_com.despreston.go_craq.examples.craqnet
end Perennial
