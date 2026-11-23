/-
The craq kit's top-level result (`Spec/github_com/despreston/go_craq/examples/craqnet/TopLevelRobustness.lean`),
proved (as paxos's and rabia's): from the deployment's start (the registry, the addresses unset),
the protocol's ghost start (`craq_alloc`), the net/rpc world at the server addresses (`rpcAlloc`,
H4), remote's map of operations, the client addresses' remote protocols, the configuration
addresses' `confProto`, remote's pending library over the key-value state, and each machine's
boot from its share through `robust_of_distProtoRB`; the orchestrator's boot by its generated
initializer spec, every other machine's by `RpcBoot` (F2), whose boot resources give the codec
registry, the mux and net/rpc's server variables.
-/
module

public import Dsverify.Spec.github_com.despreston.go_craq.examples.craqnet.TopLevelRobustness
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Link
public import Net.Statement.DistBridge
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.orch.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.orch.Init
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client0.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client0.Init
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client1.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client1.Init
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client2.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client2.Init
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client3.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client3.Init
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client4.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client4.Init
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server1.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server1.Init
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server2.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server2.Init
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server3.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server3.Init
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server4.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server4.Init
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server5.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server5.Init
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server6.PkgTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server6.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness

namespace github_com.despreston.go_craq.examples.craqnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.despreston.go_craq
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section boot
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A command's boot program, from its initializer's spec from the empty package state (its
result `R` handed to `main`) and a spec of its `main` with precondition `P ∗ R`. -/
theorem wp_bootR [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    (init : val) (main pkg : GoString) [IsPkgInit (IProp GF) pkg] (getIs : GoString → IProp GF)
    (R : IProp GF)
    (Hinit : {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getIs ∗ isPkgInit (PROP := IProp GF) pkg ∗ R }})
    (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF) pkg ∗ P ∗ R }}
        (App (Val (@! main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP (boot init main) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold boot
  wp_apply Hinit $$ [Hgs] as ⟨-, #Hpkg, HR⟩
  · iexact Hgs
  wp_pures
  wp_apply Hf $$ [HP HR]
  · iframe
  ipureintro; rfl

/-- The generated initializer spec, from the empty package state. -/
theorem init_of_gen [hG : HeapGS .hasLC GF] (init : val) (pkg : GoString)
    [IsPkgInit (IProp GF) pkg] (getIs : GoString → IProp GF)
    (Hinit : {{ ownInitializing getIs }}
        (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getIs ∗ isPkgInit (PROP := IProp GF) pkg }}) :
    {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getIs ∗ isPkgInit (PROP := IProp GF) pkg ∗ True }} := by
  iintro %Φ Hgs HΦ
  wp_apply Hinit $$ [Hgs] as ⟨Hi, #Hpkg⟩
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  iapply HΦ
  isplitl [Hi]
  · iexact Hi
  isplitr
  · iexact Hpkg
  itrivial

end boot

section env
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

/-- net/rpc's package fact is the client's variables (`cliEnv`). -/
theorem rpcPkg_cliEnv : isPkgInit (PROP := IProp GF) pkg_id.net.rpc ⊢ net.rpc.cliEnv := by
  iintro #H
  ihave #Hd := isPkgInit_access _ $$ H
  unfold net.rpc.cliEnv
  iexact Hd

end env

/-- **The craq kit, closed** (see the statement's file). -/
theorem craq_remote_robust : craq_remote_robust.spec := by
  intro gctx lctx sem s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fsem bvi
    hri hhi hlog ra rd rs halloc hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hrn he σ g threads
  refine robust_of_distProtoRB (GF := remoteGF) craqKitAddrs (system σ) g threads (2 ^ 63) ?_
  intro G π hrb
  letI := ra G
  iintro #Hreg Hs
  unfold craqKitAddrs
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hs, Hsf⟩
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hss, Hsc⟩
  imod craq_alloc.wp_proof (G := G) serverAddrs.tail (by decide) with
    ⟨%γ, #Hcraq, Hown, Htail, Hnext, Hnodes⟩
  imod halloc G π (craqSS γ (serverAddrs.headD []) serverAddrs.tail) serverAddrs $$ Hreg Hss
    with ⟨%W, %HW, #Hra⟩
  imod mapCtx_alloc (Gg := G) (I := KIn) ⊤ with ⟨%ρ, #Hmap⟩
  imod addrs_set_proto (Gg := G) ⊤ (fun _ => reqP (Gg := G) (RBase.svc (kvR γ)))
    (fun _ => repP (Gg := G) (RBase.svc (kvR γ))) clientAddrs $$ Hreg Hsc with #Hpc
  imod addrs_set_proto (Gg := G) ⊤ (fun _ => confProto) (fun _ => confProto) confAddrs
    $$ Hreg Hsf with #Hpf
  have hv : ownState (G := G) γ KvM.init ⊢ (kvR (Gg := G) γ).sysState (kvR (Gg := G) γ).B.init := .rfl
  ihave Hown := hv $$ Hown
  imod pend_alloc (Gg := G) (kvR γ) ⊤ (kvS0 (GF := remoteGF)) rfl $$ Hown with ⟨%γp, #Hpend, Hlib⟩
  let cfg : Cfg remoteGF := ⟨γ, W, serverAddrs.headD [], serverAddrs.tail⟩
  have hcfg : cfgKit cfg := ⟨rfl, rfl⟩
  ihave #Hctx : craqCtx (G := G) cfg $$ []
  · unfold craqCtx
    iframe Hcraq
    isplitr
    · ipureintro
      exact ⟨HW, (by decide : serverAddrs.tail.Nodup),
        (by decide : serverAddrs.headD [] ∉ serverAddrs.tail), (by decide : go!"" ∉ serverAddrs.tail)⟩
    · rw [show cfg.cAddr :: cfg.chain = serverAddrs from rfl]
      iexact Hra
  rw [show serverAddrs.tail = [serverAddrs.getD 1 [], serverAddrs.getD 2 [], serverAddrs.getD 3 [],
      serverAddrs.getD 4 [], serverAddrs.getD 5 []] from rfl]
  icases BigSepL.bigSepL_cons.1 $$ Hnodes with ⟨⟨Hr0, Hq0, Hn0, Ht0⟩, Hnodes⟩
  icases BigSepL.bigSepL_cons.1 $$ Hnodes with ⟨⟨Hr1, Hq1, Hn1, Ht1⟩, Hnodes⟩
  icases BigSepL.bigSepL_cons.1 $$ Hnodes with ⟨⟨Hr2, Hq2, Hn2, Ht2⟩, Hnodes⟩
  icases BigSepL.bigSepL_cons.1 $$ Hnodes with ⟨⟨Hr3, Hq3, Hn3, Ht3⟩, Hnodes⟩
  icases BigSepL.bigSepL_cons.1 $$ Hnodes with ⟨⟨Hr4, Hq4, Hn4, Ht4⟩, Hnodes⟩
  ihave #Hra' : [∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (kvR γ) a $$ [Hpc]
  · unfold remoteAddr svcAddr; iexact Hpc
  ihave #Hrc0 : remoteAddr (Gg := G) (kvR γ) (clientAddrs.getD 0 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 0) rfl $$ Hra'
  ihave #Hpc0 : addrProto (Gg := G) (confAddrs.getD 0 []) confProto confProto $$ []
  · iapply BigSepL.bigSepL_lookup (i := 0) rfl $$ Hpf
  ihave #Hrc1 : remoteAddr (Gg := G) (kvR γ) (clientAddrs.getD 1 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 1) rfl $$ Hra'
  ihave #Hpc1 : addrProto (Gg := G) (confAddrs.getD 1 []) confProto confProto $$ []
  · iapply BigSepL.bigSepL_lookup (i := 1) rfl $$ Hpf
  ihave #Hrc2 : remoteAddr (Gg := G) (kvR γ) (clientAddrs.getD 2 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 2) rfl $$ Hra'
  ihave #Hpc2 : addrProto (Gg := G) (confAddrs.getD 2 []) confProto confProto $$ []
  · iapply BigSepL.bigSepL_lookup (i := 2) rfl $$ Hpf
  ihave #Hrc3 : remoteAddr (Gg := G) (kvR γ) (clientAddrs.getD 3 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 3) rfl $$ Hra'
  ihave #Hpc3 : addrProto (Gg := G) (confAddrs.getD 3 []) confProto confProto $$ []
  · iapply BigSepL.bigSepL_lookup (i := 3) rfl $$ Hpf
  ihave #Hrc4 : remoteAddr (Gg := G) (kvR γ) (clientAddrs.getD 4 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 4) rfl $$ Hra'
  ihave #Hpc4 : addrProto (Gg := G) (confAddrs.getD 4 []) confProto confProto $$ []
  · iapply BigSepL.bigSepL_lookup (i := 4) rfl $$ Hpf
  ihave #Hps2 : addrProto (Gg := G) (confAddrs.getD (5 + 2 - 1) []) confProto confProto $$ []
  · iapply BigSepL.bigSepL_lookup (i := 5 + 2 - 1) rfl $$ Hpf
  ihave #Hps3 : addrProto (Gg := G) (confAddrs.getD (5 + 3 - 1) []) confProto confProto $$ []
  · iapply BigSepL.bigSepL_lookup (i := 5 + 3 - 1) rfl $$ Hpf
  ihave #Hps4 : addrProto (Gg := G) (confAddrs.getD (5 + 4 - 1) []) confProto confProto $$ []
  · iapply BigSepL.bigSepL_lookup (i := 5 + 4 - 1) rfl $$ Hpf
  ihave #Hps5 : addrProto (Gg := G) (confAddrs.getD (5 + 5 - 1) []) confProto confProto $$ []
  · iapply BigSepL.bigSepL_lookup (i := 5 + 5 - 1) rfl $$ Hpf
  ihave #Hps6 : addrProto (Gg := G) (confAddrs.getD (5 + 6 - 1) []) confProto confProto $$ []
  · iapply BigSepL.bigSepL_lookup (i := 5 + 6 - 1) rfl $$ Hpf
  imodintro
  iexists fun i => if i = 0 then iprop(([∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (kvR γ) a) ∗ mapCtx (Gg := G) (I := KIn) ∗ pendCtx (Gg := G) (kvR γ) (kvS0 (GF := remoteGF)) γp ∗ pendLib (Gg := G) (kvS0 (GF := remoteGF)) γp (kvS0 (GF := remoteGF)).M.init ∗ [∗list] a ∈ confAddrs, addrProto (Gg := G) a confProto confProto)
      else if i = 1 then iprop(craqCtx (G := G) cfg ∗ addrProto (Gg := G) (confAddrs.getD 0 []) confProto confProto ∗ remoteAddr (Gg := G) (kvR γ) (clientAddrs.getD 0 []) ∗ mapCtx (Gg := G) (I := KIn))
      else if i = 2 then iprop(craqCtx (G := G) cfg ∗ addrProto (Gg := G) (confAddrs.getD 1 []) confProto confProto ∗ remoteAddr (Gg := G) (kvR γ) (clientAddrs.getD 1 []) ∗ mapCtx (Gg := G) (I := KIn))
      else if i = 3 then iprop(craqCtx (G := G) cfg ∗ addrProto (Gg := G) (confAddrs.getD 2 []) confProto confProto ∗ remoteAddr (Gg := G) (kvR γ) (clientAddrs.getD 2 []) ∗ mapCtx (Gg := G) (I := KIn))
      else if i = 4 then iprop(craqCtx (G := G) cfg ∗ addrProto (Gg := G) (confAddrs.getD 3 []) confProto confProto ∗ remoteAddr (Gg := G) (kvR γ) (clientAddrs.getD 3 []) ∗ mapCtx (Gg := G) (I := KIn))
      else if i = 5 then iprop(craqCtx (G := G) cfg ∗ addrProto (Gg := G) (confAddrs.getD 4 []) confProto confProto ∗ remoteAddr (Gg := G) (kvR γ) (clientAddrs.getD 4 []) ∗ mapCtx (Gg := G) (I := KIn))
      else if i = 6 then iprop(craqCtx (G := G) cfg ∗ coordRes (G := G) cfg)
      else if i = 7 then iprop(craqCtx (G := G) cfg ∗ nodeRes (G := G) cfg (serverAddrs.getD 1 []) ∗ joinTicket (G := G) γ (serverAddrs.getD 1 []) ∗ addrProto (Gg := G) (confAddrs.getD (5 + 2 - 1) []) confProto confProto)
      else if i = 8 then iprop(craqCtx (G := G) cfg ∗ nodeRes (G := G) cfg (serverAddrs.getD 2 []) ∗ joinTicket (G := G) γ (serverAddrs.getD 2 []) ∗ addrProto (Gg := G) (confAddrs.getD (5 + 3 - 1) []) confProto confProto)
      else if i = 9 then iprop(craqCtx (G := G) cfg ∗ nodeRes (G := G) cfg (serverAddrs.getD 3 []) ∗ joinTicket (G := G) γ (serverAddrs.getD 3 []) ∗ addrProto (Gg := G) (confAddrs.getD (5 + 4 - 1) []) confProto confProto)
      else if i = 10 then iprop(craqCtx (G := G) cfg ∗ nodeRes (G := G) cfg (serverAddrs.getD 4 []) ∗ joinTicket (G := G) γ (serverAddrs.getD 4 []) ∗ addrProto (Gg := G) (confAddrs.getD (5 + 5 - 1) []) confProto confProto)
      else if i = 11 then iprop(craqCtx (G := G) cfg ∗ nodeRes (G := G) cfg (serverAddrs.getD 5 []) ∗ joinTicket (G := G) γ (serverAddrs.getD 5 []) ∗ addrProto (Gg := G) (confAddrs.getD (5 + 6 - 1) []) confProto confProto)
      else iprop(True)
  isplitr
  · ipureintro
    intro i m hm hG hGG hctx
    obtain ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    dsimp only at hGG hctx
    subst hGG hctx
    letI hG : HeapGS .hasLC remoteGF := ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    letI : net.rpc.InitHyp remoteGF := hri G' hG.goose_localGS
    letI : net.http.InitHyp remoteGF := hhi G' hG.goose_localGS
    letI : LogHyp remoteGF := hlog G' hG.goose_localGS
    letI : RpcHttpDial remoteGF := rd G' hG.goose_localGS π
    letI : RpcHttpServe remoteGF := rs G' hG.goose_localGS π
    have HRN := hrn G' hG.goose_localGS π
    have HE := he G' hG.goose_localGS π
    match i, hm with
    | 0, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Has, #Hmap0, #Hpend0, Hlib0, #Hpf0⟩ Hgs
      iapply wp_bootR cmd.orch.initialize' cmd.orch.main _ cmd.orch.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.orch.wp_initialize' _ cmd.orch.getIsPkgInit_wf)) (P := iprop(([∗list] a ∈ clientAddrs, remoteAddr (Gg := G') (kvR γ) a) ∗ mapCtx (Gg := G') (I := KIn) ∗ pendCtx (Gg := G') (kvR γ) (kvS0 (GF := remoteGF)) γp ∗ pendLib (Gg := G') (kvS0 (GF := remoteGF)) γp (kvS0 (GF := remoteGF)).M.init ∗ [∗list] a ∈ confAddrs, addrProto (Gg := G') a confProto confProto))
          (by
            iintro %Φ ⟨#Hpkg, Hp, -⟩ HΦ
            iapply (cmd.orch.wp_main EtcdGrove.dsvcraq.wp_Orch γ γp hrb) $$ [Hp] HΦ
            iframe Hpkg Hp) $$ [Hlib0] Hgs
      all_goals try iframe #
      all_goals try iframe Hlib0
    | 1, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Hctx0, #Hpc0, #Hrc0, #Hmap0⟩ Hgs
      iapply wp_bootR cmd.client0.initialize' cmd.client0.main _ cmd.client0.getIsPkgInit rpcBootRes
          (hb1 G' hG.goose_localGS π _ cmd.client0.getIsPkgInit_wf) (P := iprop(craqCtx (G := G') cfg ∗ addrProto (Gg := G') (confAddrs.getD 0 []) confProto confProto ∗ remoteAddr (Gg := G') (kvR γ) (clientAddrs.getD 0 []) ∗ mapCtx (Gg := G') (I := KIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hpa, #Hrr, #Hm⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, -, -⟩
            iapply (cmd.client0.wp_main EtcdGrove.dsvcraq.wp_Client cfg hcfg) $$ [Hcf] HΦ
            iframe #
            iframe Hcf) $$ [] Hgs
      all_goals try iframe #
    | 2, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Hctx0, #Hpc0, #Hrc0, #Hmap0⟩ Hgs
      iapply wp_bootR cmd.client1.initialize' cmd.client1.main _ cmd.client1.getIsPkgInit rpcBootRes
          (hb2 G' hG.goose_localGS π _ cmd.client1.getIsPkgInit_wf) (P := iprop(craqCtx (G := G') cfg ∗ addrProto (Gg := G') (confAddrs.getD 1 []) confProto confProto ∗ remoteAddr (Gg := G') (kvR γ) (clientAddrs.getD 1 []) ∗ mapCtx (Gg := G') (I := KIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hpa, #Hrr, #Hm⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, -, -⟩
            iapply (cmd.client1.wp_main EtcdGrove.dsvcraq.wp_Client cfg hcfg) $$ [Hcf] HΦ
            iframe #
            iframe Hcf) $$ [] Hgs
      all_goals try iframe #
    | 3, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Hctx0, #Hpc0, #Hrc0, #Hmap0⟩ Hgs
      iapply wp_bootR cmd.client2.initialize' cmd.client2.main _ cmd.client2.getIsPkgInit rpcBootRes
          (hb3 G' hG.goose_localGS π _ cmd.client2.getIsPkgInit_wf) (P := iprop(craqCtx (G := G') cfg ∗ addrProto (Gg := G') (confAddrs.getD 2 []) confProto confProto ∗ remoteAddr (Gg := G') (kvR γ) (clientAddrs.getD 2 []) ∗ mapCtx (Gg := G') (I := KIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hpa, #Hrr, #Hm⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, -, -⟩
            iapply (cmd.client2.wp_main EtcdGrove.dsvcraq.wp_Client cfg hcfg) $$ [Hcf] HΦ
            iframe #
            iframe Hcf) $$ [] Hgs
      all_goals try iframe #
    | 4, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Hctx0, #Hpc0, #Hrc0, #Hmap0⟩ Hgs
      iapply wp_bootR cmd.client3.initialize' cmd.client3.main _ cmd.client3.getIsPkgInit rpcBootRes
          (hb4 G' hG.goose_localGS π _ cmd.client3.getIsPkgInit_wf) (P := iprop(craqCtx (G := G') cfg ∗ addrProto (Gg := G') (confAddrs.getD 3 []) confProto confProto ∗ remoteAddr (Gg := G') (kvR γ) (clientAddrs.getD 3 []) ∗ mapCtx (Gg := G') (I := KIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hpa, #Hrr, #Hm⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, -, -⟩
            iapply (cmd.client3.wp_main EtcdGrove.dsvcraq.wp_Client cfg hcfg) $$ [Hcf] HΦ
            iframe #
            iframe Hcf) $$ [] Hgs
      all_goals try iframe #
    | 5, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Hctx0, #Hpc0, #Hrc0, #Hmap0⟩ Hgs
      iapply wp_bootR cmd.client4.initialize' cmd.client4.main _ cmd.client4.getIsPkgInit rpcBootRes
          (hb5 G' hG.goose_localGS π _ cmd.client4.getIsPkgInit_wf) (P := iprop(craqCtx (G := G') cfg ∗ addrProto (Gg := G') (confAddrs.getD 4 []) confProto confProto ∗ remoteAddr (Gg := G') (kvR γ) (clientAddrs.getD 4 []) ∗ mapCtx (Gg := G') (I := KIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hpa, #Hrr, #Hm⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, -, -⟩
            iapply (cmd.client4.wp_main EtcdGrove.dsvcraq.wp_Client cfg hcfg) $$ [Hcf] HΦ
            iframe #
            iframe Hcf) $$ [] Hgs
      all_goals try iframe #
    | 6, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Hctx0, Hres0⟩ Hgs
      iapply wp_bootR cmd.server1.initialize' cmd.server1.main _ cmd.server1.getIsPkgInit rpcBootRes
          (hb6 G' hG.goose_localGS π _ cmd.server1.getIsPkgInit_wf) (P := iprop(craqCtx (G := G') cfg ∗ coordRes (G := G') cfg))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Hinv, Hmux⟩
            ihave #Hrp : isPkgInit (PROP := IProp remoteGF) pkg_id.net.rpc $$ []
            · iPkgInit
            ihave #Hce := rpcPkg_cliEnv $$ Hrp
            iapply (cmd.server1.wp_main (EtcdGrove.dsvcraq.wp_Server HRN HE) cfg hcfg) $$
              [Hr Hcf Hmux] HΦ
            unfold net.rpc.srvEnv
            iframe Hpkg Hc Hcf Hmux Hce Hinv
            unfold serverRes
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ [Hres0] Hgs
      all_goals try iframe #
      all_goals try iframe Hres0
    | 7, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Hctx0, Hres0⟩ Hgs
      iapply wp_bootR cmd.server2.initialize' cmd.server2.main _ cmd.server2.getIsPkgInit rpcBootRes
          (hb7 G' hG.goose_localGS π _ cmd.server2.getIsPkgInit_wf) (P := iprop(craqCtx (G := G') cfg ∗ nodeRes (G := G') cfg (serverAddrs.getD 1 []) ∗ joinTicket (G := G') γ (serverAddrs.getD 1 []) ∗ addrProto (Gg := G') (confAddrs.getD (5 + 2 - 1) []) confProto confProto))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Hinv, Hmux⟩
            ihave #Hrp : isPkgInit (PROP := IProp remoteGF) pkg_id.net.rpc $$ []
            · iPkgInit
            ihave #Hce := rpcPkg_cliEnv $$ Hrp
            iapply (cmd.server2.wp_main (EtcdGrove.dsvcraq.wp_Server HRN HE) cfg hcfg) $$
              [Hr Hcf Hmux] HΦ
            unfold net.rpc.srvEnv
            iframe Hpkg Hc Hcf Hmux Hce Hinv
            unfold serverRes
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ [Hres0] Hgs
      all_goals try iframe #
      all_goals try iframe Hres0
    | 8, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Hctx0, Hres0⟩ Hgs
      iapply wp_bootR cmd.server3.initialize' cmd.server3.main _ cmd.server3.getIsPkgInit rpcBootRes
          (hb8 G' hG.goose_localGS π _ cmd.server3.getIsPkgInit_wf) (P := iprop(craqCtx (G := G') cfg ∗ nodeRes (G := G') cfg (serverAddrs.getD 2 []) ∗ joinTicket (G := G') γ (serverAddrs.getD 2 []) ∗ addrProto (Gg := G') (confAddrs.getD (5 + 3 - 1) []) confProto confProto))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Hinv, Hmux⟩
            ihave #Hrp : isPkgInit (PROP := IProp remoteGF) pkg_id.net.rpc $$ []
            · iPkgInit
            ihave #Hce := rpcPkg_cliEnv $$ Hrp
            iapply (cmd.server3.wp_main (EtcdGrove.dsvcraq.wp_Server HRN HE) cfg hcfg) $$
              [Hr Hcf Hmux] HΦ
            unfold net.rpc.srvEnv
            iframe Hpkg Hc Hcf Hmux Hce Hinv
            unfold serverRes
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ [Hres0] Hgs
      all_goals try iframe #
      all_goals try iframe Hres0
    | 9, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Hctx0, Hres0⟩ Hgs
      iapply wp_bootR cmd.server4.initialize' cmd.server4.main _ cmd.server4.getIsPkgInit rpcBootRes
          (hb9 G' hG.goose_localGS π _ cmd.server4.getIsPkgInit_wf) (P := iprop(craqCtx (G := G') cfg ∗ nodeRes (G := G') cfg (serverAddrs.getD 3 []) ∗ joinTicket (G := G') γ (serverAddrs.getD 3 []) ∗ addrProto (Gg := G') (confAddrs.getD (5 + 4 - 1) []) confProto confProto))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Hinv, Hmux⟩
            ihave #Hrp : isPkgInit (PROP := IProp remoteGF) pkg_id.net.rpc $$ []
            · iPkgInit
            ihave #Hce := rpcPkg_cliEnv $$ Hrp
            iapply (cmd.server4.wp_main (EtcdGrove.dsvcraq.wp_Server HRN HE) cfg hcfg) $$
              [Hr Hcf Hmux] HΦ
            unfold net.rpc.srvEnv
            iframe Hpkg Hc Hcf Hmux Hce Hinv
            unfold serverRes
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ [Hres0] Hgs
      all_goals try iframe #
      all_goals try iframe Hres0
    | 10, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Hctx0, Hres0⟩ Hgs
      iapply wp_bootR cmd.server5.initialize' cmd.server5.main _ cmd.server5.getIsPkgInit rpcBootRes
          (hb10 G' hG.goose_localGS π _ cmd.server5.getIsPkgInit_wf) (P := iprop(craqCtx (G := G') cfg ∗ nodeRes (G := G') cfg (serverAddrs.getD 4 []) ∗ joinTicket (G := G') γ (serverAddrs.getD 4 []) ∗ addrProto (Gg := G') (confAddrs.getD (5 + 5 - 1) []) confProto confProto))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Hinv, Hmux⟩
            ihave #Hrp : isPkgInit (PROP := IProp remoteGF) pkg_id.net.rpc $$ []
            · iPkgInit
            ihave #Hce := rpcPkg_cliEnv $$ Hrp
            iapply (cmd.server5.wp_main (EtcdGrove.dsvcraq.wp_Server HRN HE) cfg hcfg) $$
              [Hr Hcf Hmux] HΦ
            unfold net.rpc.srvEnv
            iframe Hpkg Hc Hcf Hmux Hce Hinv
            unfold serverRes
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ [Hres0] Hgs
      all_goals try iframe #
      all_goals try iframe Hres0
    | 11, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#Hctx0, Hres0⟩ Hgs
      iapply wp_bootR cmd.server6.initialize' cmd.server6.main _ cmd.server6.getIsPkgInit rpcBootRes
          (hb11 G' hG.goose_localGS π _ cmd.server6.getIsPkgInit_wf) (P := iprop(craqCtx (G := G') cfg ∗ nodeRes (G := G') cfg (serverAddrs.getD 5 []) ∗ joinTicket (G := G') γ (serverAddrs.getD 5 []) ∗ addrProto (Gg := G') (confAddrs.getD (5 + 6 - 1) []) confProto confProto))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Hinv, Hmux⟩
            ihave #Hrp : isPkgInit (PROP := IProp remoteGF) pkg_id.net.rpc $$ []
            · iPkgInit
            ihave #Hce := rpcPkg_cliEnv $$ Hrp
            iapply (cmd.server6.wp_main (EtcdGrove.dsvcraq.wp_Server HRN HE) cfg hcfg) $$
              [Hr Hcf Hmux] HΦ
            unfold net.rpc.srvEnv
            iframe Hpkg Hc Hcf Hmux Hce Hinv
            unfold serverRes
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ [Hres0] Hgs
      all_goals try iframe #
      all_goals try iframe Hres0
  · simp only [system]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hlib]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hlib
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitl [Htail Hnext Hr0 Hr1 Hr2 Hr3 Hr4]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      unfold coordRes
      iframe Htail Hnext
      rw [show cfg.chain = [serverAddrs.getD 1 [], serverAddrs.getD 2 [], serverAddrs.getD 3 [],
        serverAddrs.getD 4 [], serverAddrs.getD 5 []] from rfl]
      iapply BigSepL.bigSepL_cons.2; iframe Hr0
      iapply BigSepL.bigSepL_cons.2; iframe Hr1
      iapply BigSepL.bigSepL_cons.2; iframe Hr2
      iapply BigSepL.bigSepL_cons.2; iframe Hr3
      iapply BigSepL.bigSepL_cons.2; iframe Hr4
      iapply BigSepL.bigSepL_nil.2
      iempintro
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hq0 Hn0 Ht0]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      unfold nodeRes
      iframe Hq0 Hn0 Ht0
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hq1 Hn1 Ht1]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      unfold nodeRes
      iframe Hq1 Hn1 Ht1
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hq2 Hn2 Ht2]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      unfold nodeRes
      iframe Hq2 Hn2 Ht2
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hq3 Hn3 Ht3]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      unfold nodeRes
      iframe Hq3 Hn3 Ht3
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hq4 Hn4 Ht4]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      unfold nodeRes
      iframe Hq4 Hn4 Ht4
    iapply BigSepL.bigSepL_nil.2
    iempintro

#print axioms craq_remote_robust

end github_com.despreston.go_craq.examples.craqnet
end Perennial
