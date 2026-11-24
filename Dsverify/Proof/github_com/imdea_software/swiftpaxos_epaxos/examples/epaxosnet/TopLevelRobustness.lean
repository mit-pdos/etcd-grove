/-
The EPaxos kit's top-level result (`Spec/github_com/imdea_software/swiftpaxos_epaxos/examples/epaxosnet/TopLevelRobustness.lean`),
proved (as craq's and paxos's): from the deployment's start (the registry, the addresses unset, the
master's wildcard listener unset: `robust_of_distProtoLisRBT`, with each machine's thread bound),
the kit's start (`ep_start`: the names, the rpc world, the store's state, the master's and the
replicas' machine resources, `clientInvs`), remote's map of operations, the client addresses'
remote protocols, remote's pending library over the store `epR γ`, and each machine's boot from
its share; the orchestrator's and the client machines' boots by their generated initializer
specs, the server machines' by `RpcBoot`, whose boot resources give the codec state, the mux and
net/rpc's server variables.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.TopLevelRobustness
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Mains
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Bridge
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.KeyComparator
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.orch.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.orch.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client0.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client0.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client1.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client1.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client2.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client2.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client3.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client3.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client4.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client4.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client5.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client5.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client6.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client6.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client7.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client7.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client8.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client8.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client9.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client9.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server1.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server1.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server2.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server2.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server4.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server4.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server5.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server5.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server6.PkgTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server6.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote
  github_com.imdea_software.swiftpaxos_epaxos github_com.imdea_software.swiftpaxos_epaxos.kvs
  github_com.imdea_software.swiftpaxos_epaxos.model
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section boot
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A command's boot program, from its initializer's spec from the empty package state (its
result `R` handed to `main`) and a spec of its `main` with precondition `P ∗ R` (craq's). -/
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

/-- The generated initializer spec, from the empty package state (craq's). -/
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

theorem clientAddrs_eq : clientAddrs = epClientAddrs := rfl

/-- **The EPaxos kit, closed** (see the statement's file). -/
theorem epaxos_remote_robust : epaxos_remote_robust.spec := by
  intro gctx lctx sem s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 fsem bvi hri hhi ra rh hb1 hb2 hb3 hb4 hb5 hb6 σ g
  refine robust_of_distProtoLisRBT (GF := remoteGF) epAddrs epLas (system σ) g (2 ^ 31) (2 ^ 63)
    epLas_pairwise epLas_disj ?_
  intro G π hrb
  letI := ra G π
  iintro #Hreg Hs Hl
  unfold epAddrs
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hss, Hsc⟩
  unfold epLas
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hml, -⟩
  imod ep_start (G := G) $$ Hreg Hss Hml with ⟨%γ, %W, %HW, Hown, Hmr, Hrr, #Hci⟩
  imod mapCtx_alloc (Gg := G) (I := EIn) ⊤ clientAddrs 6 (by decide) with ⟨%ρ, -, #Hmap, Hbud⟩
  imod addrs_set_proto (Gg := G) ⊤ (fun a => reqP (Gg := G) (RBase.svc (epR γ)) a)
    (fun _ => repP (Gg := G) (RBase.svc (epR γ))) epClientAddrs $$ Hreg Hsc with #Hpc
  have hv : own_state (G := G) γ (kvScan w8).init ⊢
      (epR (Gg := G) γ).sysState (epR (Gg := G) γ).B.init := .rfl
  ihave Hown := hv $$ Hown
  imod pend_alloc (Gg := G) (epR γ) ⊤ (epS0 (GF := remoteGF)) rfl $$ Hown with ⟨%γp, #Hpend, Hlib⟩
  ihave #Hra : [∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (epR γ) a $$ [Hpc]
  · rw [clientAddrs_eq]; unfold remoteAddr svcAddr; iexact Hpc

  ihave #Hra0 : remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 0 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 0) rfl $$ Hra
  ihave #Hra1 : remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 1 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 1) rfl $$ Hra
  ihave #Hra2 : remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 2 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 2) rfl $$ Hra
  ihave #Hra3 : remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 3 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 3) rfl $$ Hra
  ihave #Hra4 : remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 4 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 4) rfl $$ Hra
  ihave #Hra5 : remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 5 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 5) rfl $$ Hra
  ihave #Hra6 : remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 6 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 6) rfl $$ Hra
  ihave #Hra7 : remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 7 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 7) rfl $$ Hra
  ihave #Hra8 : remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 8 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 8) rfl $$ Hra
  ihave #Hra9 : remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 9 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 9) rfl $$ Hra
  unfold replicaNodes
  icases BigSepL.bigSepL_cons.1 $$ Hrr with ⟨Hr2, Hrr⟩
  icases BigSepL.bigSepL_cons.1 $$ Hrr with ⟨Hr3, Hrr⟩
  icases BigSepL.bigSepL_cons.1 $$ Hrr with ⟨Hr4, Hrr⟩
  icases BigSepL.bigSepL_cons.1 $$ Hrr with ⟨Hr5, Hrr⟩
  icases BigSepL.bigSepL_cons.1 $$ Hrr with ⟨Hr6, -⟩
  imodintro
  iexists fun i => if i = 0 then iprop(([∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (epR γ) a) ∗ mapCtx (Gg := G) (I := EIn) ∗ pendCtx (Gg := G) (epR γ) (epS0 (GF := remoteGF)) γp ∗ pendLib (Gg := G) (epS0 (GF := remoteGF)) γp (epS0 (GF := remoteGF)).M.init ∗ [∗list] a ∈ clientAddrs, budUnits (Gg := G) a 6)
      else if i = 1 then iprop(clientInvs (G := G) γ ∗ remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 0 []) ∗ mapCtx (Gg := G) (I := EIn))
      else if i = 2 then iprop(clientInvs (G := G) γ ∗ remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 1 []) ∗ mapCtx (Gg := G) (I := EIn))
      else if i = 3 then iprop(clientInvs (G := G) γ ∗ remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 2 []) ∗ mapCtx (Gg := G) (I := EIn))
      else if i = 4 then iprop(clientInvs (G := G) γ ∗ remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 3 []) ∗ mapCtx (Gg := G) (I := EIn))
      else if i = 5 then iprop(clientInvs (G := G) γ ∗ remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 4 []) ∗ mapCtx (Gg := G) (I := EIn))
      else if i = 6 then iprop(clientInvs (G := G) γ ∗ remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 5 []) ∗ mapCtx (Gg := G) (I := EIn))
      else if i = 7 then iprop(clientInvs (G := G) γ ∗ remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 6 []) ∗ mapCtx (Gg := G) (I := EIn))
      else if i = 8 then iprop(clientInvs (G := G) γ ∗ remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 7 []) ∗ mapCtx (Gg := G) (I := EIn))
      else if i = 9 then iprop(clientInvs (G := G) γ ∗ remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 8 []) ∗ mapCtx (Gg := G) (I := EIn))
      else if i = 10 then iprop(clientInvs (G := G) γ ∗ remoteAddr (Gg := G) (epR γ) (clientAddrs.getD 9 []) ∗ mapCtx (Gg := G) (I := EIn))
      else if i = 11 then iprop(⌜W.SS = rpcSS γ⌝ ∗ masterRes (G := G) γ W)
      else if i = 12 then iprop(⌜W.SS = rpcSS γ⌝ ∗ replicaRes (G := G) γ W 2)
      else if i = 13 then iprop(⌜W.SS = rpcSS γ⌝ ∗ replicaRes (G := G) γ W 3)
      else if i = 14 then iprop(⌜W.SS = rpcSS γ⌝ ∗ replicaRes (G := G) γ W 4)
      else if i = 15 then iprop(⌜W.SS = rpcSS γ⌝ ∗ replicaRes (G := G) γ W 5)
      else if i = 16 then iprop(⌜W.SS = rpcSS γ⌝ ∗ replicaRes (G := G) γ W 6)
      else iprop(True)
  isplitr
  · ipureintro
    intro i m hm hG hGG hctx hT
    obtain ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    dsimp only at hGG hctx hT
    subst hGG hctx
    letI hG : HeapGS .hasLC remoteGF := ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    letI : net.rpc.InitHyp remoteGF := hri G' hG.goose_localGS
    letI : net.http.InitHyp remoteGF := hhi G' hG.goose_localGS
    letI : StateTreemap remoteGF :=
      StateTreemap.ofGods github_com.emirpasic.gods.maps.treemap.hyps_true
        github_com.imdea_software.swiftpaxos_epaxos.state.keyComparator_cmpOk
    letI : RpcHttpHyp remoteGF := rh G' hG.goose_localGS π
    have hrb' : receiptBound remoteGF ≤ 2 ^ 63 := by omega
    have hb' : threadBound remoteGF ≤ 2 ^ 31 ∧ receiptBound remoteGF ≤ 2 ^ 64 := by
      constructor <;> omega
    match i, hm with
    | 0, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.orch.initialize' cmd.orch.main _ cmd.orch.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.orch.wp_initialize' _ cmd.orch.getIsPkgInit_wf)) (P := iprop(([∗list] a ∈ clientAddrs, remoteAddr (Gg := G') (epR γ) a) ∗ mapCtx (Gg := G') (I := EIn) ∗ pendCtx (Gg := G') (epR γ) (epS0 (GF := remoteGF)) γp ∗ pendLib (Gg := G') (epS0 (GF := remoteGF)) γp (epS0 (GF := remoteGF)).M.init ∗ [∗list] a ∈ clientAddrs, budUnits (Gg := G') a 6))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Has, #Hm, #Hp, Hlib, Hbud⟩, -⟩ HΦ
            iapply (cmd.orch.wp_main EtcdGrove.dsvepaxos.wp_Orch γ γp hrb') $$ [Hlib Hbud] HΦ
            iframe #
            iframe Hlib Hbud) $$ HP Hgs
    | 1, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client0.initialize' cmd.client0.main _ cmd.client0.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client0.wp_initialize' _ cmd.client0.getIsPkgInit_wf)) (P := iprop(clientInvs (G := G') γ ∗ remoteAddr (Gg := G') (epR γ) (clientAddrs.getD 0 []) ∗ mapCtx (Gg := G') (I := EIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hr, #Hm⟩, -⟩ HΦ
            iapply (cmd.client0.wp_main EtcdGrove.dsvepaxos.wp_Client γ) $$ [] HΦ
            iframe #) $$ HP Hgs
    | 2, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client1.initialize' cmd.client1.main _ cmd.client1.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client1.wp_initialize' _ cmd.client1.getIsPkgInit_wf)) (P := iprop(clientInvs (G := G') γ ∗ remoteAddr (Gg := G') (epR γ) (clientAddrs.getD 1 []) ∗ mapCtx (Gg := G') (I := EIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hr, #Hm⟩, -⟩ HΦ
            iapply (cmd.client1.wp_main EtcdGrove.dsvepaxos.wp_Client γ) $$ [] HΦ
            iframe #) $$ HP Hgs
    | 3, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client2.initialize' cmd.client2.main _ cmd.client2.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client2.wp_initialize' _ cmd.client2.getIsPkgInit_wf)) (P := iprop(clientInvs (G := G') γ ∗ remoteAddr (Gg := G') (epR γ) (clientAddrs.getD 2 []) ∗ mapCtx (Gg := G') (I := EIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hr, #Hm⟩, -⟩ HΦ
            iapply (cmd.client2.wp_main EtcdGrove.dsvepaxos.wp_Client γ) $$ [] HΦ
            iframe #) $$ HP Hgs
    | 4, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client3.initialize' cmd.client3.main _ cmd.client3.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client3.wp_initialize' _ cmd.client3.getIsPkgInit_wf)) (P := iprop(clientInvs (G := G') γ ∗ remoteAddr (Gg := G') (epR γ) (clientAddrs.getD 3 []) ∗ mapCtx (Gg := G') (I := EIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hr, #Hm⟩, -⟩ HΦ
            iapply (cmd.client3.wp_main EtcdGrove.dsvepaxos.wp_Client γ) $$ [] HΦ
            iframe #) $$ HP Hgs
    | 5, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client4.initialize' cmd.client4.main _ cmd.client4.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client4.wp_initialize' _ cmd.client4.getIsPkgInit_wf)) (P := iprop(clientInvs (G := G') γ ∗ remoteAddr (Gg := G') (epR γ) (clientAddrs.getD 4 []) ∗ mapCtx (Gg := G') (I := EIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hr, #Hm⟩, -⟩ HΦ
            iapply (cmd.client4.wp_main EtcdGrove.dsvepaxos.wp_Client γ) $$ [] HΦ
            iframe #) $$ HP Hgs
    | 6, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client5.initialize' cmd.client5.main _ cmd.client5.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client5.wp_initialize' _ cmd.client5.getIsPkgInit_wf)) (P := iprop(clientInvs (G := G') γ ∗ remoteAddr (Gg := G') (epR γ) (clientAddrs.getD 5 []) ∗ mapCtx (Gg := G') (I := EIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hr, #Hm⟩, -⟩ HΦ
            iapply (cmd.client5.wp_main EtcdGrove.dsvepaxos.wp_Client γ) $$ [] HΦ
            iframe #) $$ HP Hgs
    | 7, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client6.initialize' cmd.client6.main _ cmd.client6.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client6.wp_initialize' _ cmd.client6.getIsPkgInit_wf)) (P := iprop(clientInvs (G := G') γ ∗ remoteAddr (Gg := G') (epR γ) (clientAddrs.getD 6 []) ∗ mapCtx (Gg := G') (I := EIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hr, #Hm⟩, -⟩ HΦ
            iapply (cmd.client6.wp_main EtcdGrove.dsvepaxos.wp_Client γ) $$ [] HΦ
            iframe #) $$ HP Hgs
    | 8, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client7.initialize' cmd.client7.main _ cmd.client7.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client7.wp_initialize' _ cmd.client7.getIsPkgInit_wf)) (P := iprop(clientInvs (G := G') γ ∗ remoteAddr (Gg := G') (epR γ) (clientAddrs.getD 7 []) ∗ mapCtx (Gg := G') (I := EIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hr, #Hm⟩, -⟩ HΦ
            iapply (cmd.client7.wp_main EtcdGrove.dsvepaxos.wp_Client γ) $$ [] HΦ
            iframe #) $$ HP Hgs
    | 9, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client8.initialize' cmd.client8.main _ cmd.client8.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client8.wp_initialize' _ cmd.client8.getIsPkgInit_wf)) (P := iprop(clientInvs (G := G') γ ∗ remoteAddr (Gg := G') (epR γ) (clientAddrs.getD 8 []) ∗ mapCtx (Gg := G') (I := EIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hr, #Hm⟩, -⟩ HΦ
            iapply (cmd.client8.wp_main EtcdGrove.dsvepaxos.wp_Client γ) $$ [] HΦ
            iframe #) $$ HP Hgs
    | 10, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client9.initialize' cmd.client9.main _ cmd.client9.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client9.wp_initialize' _ cmd.client9.getIsPkgInit_wf)) (P := iprop(clientInvs (G := G') γ ∗ remoteAddr (Gg := G') (epR γ) (clientAddrs.getD 9 []) ∗ mapCtx (Gg := G') (I := EIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Hc, #Hr, #Hm⟩, -⟩ HΦ
            iapply (cmd.client9.wp_main EtcdGrove.dsvepaxos.wp_Client γ) $$ [] HΦ
            iframe #) $$ HP Hgs
    | 11, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server1.initialize' cmd.server1.main _ cmd.server1.getIsPkgInit rpcBootRes
          (hb1 G' hG.goose_localGS π _ cmd.server1.getIsPkgInit_wf) (P := iprop(⌜W.SS = rpcSS γ⌝ ∗ masterRes (G := G') γ W))
          (by
            iintro %Φ ⟨#Hpkg, ⟨%HSS, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Henv, Hmux, #Hds, #Hde⟩
            iapply (cmd.server1.wp_main EtcdGrove.dsvepaxos.wp_Server γ W) $$ [Hr Hcf Hmux] HΦ
            unfold serverRes
            iframe Hpkg Hcf Hmux Hds Henv Hde
            isplitr
            · ipureintro; exact hb'
            isplitr
            · ipureintro; exact HSS
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ HP Hgs
    | 12, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server2.initialize' cmd.server2.main _ cmd.server2.getIsPkgInit rpcBootRes
          (hb2 G' hG.goose_localGS π _ cmd.server2.getIsPkgInit_wf) (P := iprop(⌜W.SS = rpcSS γ⌝ ∗ replicaRes (G := G') γ W 2))
          (by
            iintro %Φ ⟨#Hpkg, ⟨%HSS, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Henv, Hmux, #Hds, #Hde⟩
            iapply (cmd.server2.wp_main EtcdGrove.dsvepaxos.wp_Server γ W) $$ [Hr Hcf Hmux] HΦ
            unfold serverRes
            iframe Hpkg Hcf Hmux Hds Henv Hde
            isplitr
            · ipureintro; exact hb'
            isplitr
            · ipureintro; exact HSS
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ HP Hgs
    | 13, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server3.initialize' cmd.server3.main _ cmd.server3.getIsPkgInit rpcBootRes
          (hb3 G' hG.goose_localGS π _ cmd.server3.getIsPkgInit_wf) (P := iprop(⌜W.SS = rpcSS γ⌝ ∗ replicaRes (G := G') γ W 3))
          (by
            iintro %Φ ⟨#Hpkg, ⟨%HSS, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Henv, Hmux, #Hds, #Hde⟩
            iapply (cmd.server3.wp_main EtcdGrove.dsvepaxos.wp_Server γ W) $$ [Hr Hcf Hmux] HΦ
            unfold serverRes
            iframe Hpkg Hcf Hmux Hds Henv Hde
            isplitr
            · ipureintro; exact hb'
            isplitr
            · ipureintro; exact HSS
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ HP Hgs
    | 14, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server4.initialize' cmd.server4.main _ cmd.server4.getIsPkgInit rpcBootRes
          (hb4 G' hG.goose_localGS π _ cmd.server4.getIsPkgInit_wf) (P := iprop(⌜W.SS = rpcSS γ⌝ ∗ replicaRes (G := G') γ W 4))
          (by
            iintro %Φ ⟨#Hpkg, ⟨%HSS, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Henv, Hmux, #Hds, #Hde⟩
            iapply (cmd.server4.wp_main EtcdGrove.dsvepaxos.wp_Server γ W) $$ [Hr Hcf Hmux] HΦ
            unfold serverRes
            iframe Hpkg Hcf Hmux Hds Henv Hde
            isplitr
            · ipureintro; exact hb'
            isplitr
            · ipureintro; exact HSS
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ HP Hgs
    | 15, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server5.initialize' cmd.server5.main _ cmd.server5.getIsPkgInit rpcBootRes
          (hb5 G' hG.goose_localGS π _ cmd.server5.getIsPkgInit_wf) (P := iprop(⌜W.SS = rpcSS γ⌝ ∗ replicaRes (G := G') γ W 5))
          (by
            iintro %Φ ⟨#Hpkg, ⟨%HSS, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Henv, Hmux, #Hds, #Hde⟩
            iapply (cmd.server5.wp_main EtcdGrove.dsvepaxos.wp_Server γ W) $$ [Hr Hcf Hmux] HΦ
            unfold serverRes
            iframe Hpkg Hcf Hmux Hds Henv Hde
            isplitr
            · ipureintro; exact hb'
            isplitr
            · ipureintro; exact HSS
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ HP Hgs
    | 16, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server6.initialize' cmd.server6.main _ cmd.server6.getIsPkgInit rpcBootRes
          (hb6 G' hG.goose_localGS π _ cmd.server6.getIsPkgInit_wf) (P := iprop(⌜W.SS = rpcSS γ⌝ ∗ replicaRes (G := G') γ W 6))
          (by
            iintro %Φ ⟨#Hpkg, ⟨%HSS, Hr⟩, HR⟩ HΦ
            iunfold rpcBootRes at HR
            icases HR with ⟨Hcf, #Henv, Hmux, #Hds, #Hde⟩
            iapply (cmd.server6.wp_main EtcdGrove.dsvepaxos.wp_Server γ W) $$ [Hr Hcf Hmux] HΦ
            unfold serverRes
            iframe Hpkg Hcf Hmux Hds Henv Hde
            isplitr
            · ipureintro; exact hb'
            isplitr
            · ipureintro; exact HSS
            first | rw [if_pos rfl] | rw [if_neg (by decide)]
            iexact Hr) $$ HP Hgs
  · simp only [system]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hlib Hbud]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hlib Hbud
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
    isplitl [Hmr]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      isplitr
      · ipureintro; exact HW
      iexact Hmr
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr2]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      isplitr
      · ipureintro; exact HW
      iexact Hr2
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr3]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      isplitr
      · ipureintro; exact HW
      iexact Hr3
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr4]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      isplitr
      · ipureintro; exact HW
      iexact Hr4
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr5]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      isplitr
      · ipureintro; exact HW
      iexact Hr5
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr6]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      isplitr
      · ipureintro; exact HW
      iexact Hr6
    iapply BigSepL.bigSepL_nil.2
    iempintro

#print axioms epaxos_remote_robust

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial

