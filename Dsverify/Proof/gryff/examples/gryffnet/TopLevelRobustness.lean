/-
The gryff kit's top-level result (`Dsverify/Spec/gryff/examples/gryffnet/TopLevelRobustness.lean`),
proved (dsv-epaxos's pattern): from the deployment's start (the registry, the client machines'
addresses unset, the servers' seven wildcard listeners unset: dsv-epaxos's `robust_of_distProtoLisRBT`, with
each machine's thread bound), the kit's start (`gryff_start`: the names, the rpc world, Gryff's
ghost state and invariants, the listeners' protocols, the machines' shares, the register's half),
remote's map of operations, the client addresses' remote protocols, remote's pending library over
the store `casR γ.proto`, and each machine's boot from its share: the orchestrator's and the
client machines' by their generated initializer specs, the server machines' by their owned boots
(`cmd/server*/Boot.lean`: `gryffGlobals`, `bootProph`, `serverBoot` from `RpcBootHyp`).
-/
module

public import Dsverify.Spec.gryff.examples.gryffnet.TopLevelRobustness
public import Dsverify.Proof.gryff.examples.gryffnet.Link
public import Dsverify.Proof.gryff.examples.gryffnet.Mains
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Bridge
public import Dsverify.Proof.gryff.Start
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.orch.PkgTable
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.orch.Init
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client0.PkgTable
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client0.Init
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client1.PkgTable
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client1.Init
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client2.PkgTable
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client2.Init
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client3.PkgTable
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client3.Init
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client4.PkgTable
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client4.Init
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client5.PkgTable
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client5.Init
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server1.PkgTable
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server1.Init
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server2.PkgTable
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server2.Init
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server3.PkgTable
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server3.Init
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server4.PkgTable
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server4.Init
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server1.Boot
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server2.Boot
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server3.Boot
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server4.Boot

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness

namespace gryff.examples.gryffnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote Perennial.gryff
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

/-- **The gryff kit, closed** (see the statement's file). -/
theorem gryff_remote_robust : gryff_remote_robust.spec := by
  intro gctx lctx sem s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 fsem bvi rsem hri hhi hmr hbv hsi hss hmp hrs RA H hboot hdial σ g threads
  refine github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.robust_of_distProtoLisRBT (GF := remoteGF) gryffKitAddrs gryffLas (system σ) g threads
    (2 ^ 31 - 1) gryffLas_pairwise gryffLas_disj ?_
  intro G π hrb
  letI := RA G π
  iintro #Hreg Hs Hl
  unfold gryffKitAddrs
  imod gryff_start (G := G) $$ Hreg Hl with ⟨%γ, Hown, Hcl, Hsv⟩
  imod mapCtx_alloc (Gg := G) (I := In) ⊤ with ⟨%ρ, #Hmap⟩
  imod addrs_set_proto (Gg := G) ⊤ (fun _ => reqP (Gg := G) (RBase.svc (casR γ.proto)))
    (fun _ => repP (Gg := G) (RBase.svc (casR γ.proto))) clientAddrs $$ Hreg Hs with #Hpc
  have hv : regHalf (GF := remoteGF) γ.proto (W64 0) ⊢
      (casR (GF := remoteGF) γ.proto).sysState (casR (GF := remoteGF) γ.proto).B.init := .rfl
  ihave Hown := hv $$ Hown
  imod pend_alloc (Gg := G) (casR γ.proto) ⊤ (casS0 (GF := remoteGF)) rfl $$ Hown
    with ⟨%γp, #Hpend, Hlib⟩
  ihave #Hra : [∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (casR γ.proto) a $$ [Hpc]
  · unfold remoteAddr svcAddr; iexact Hpc
  ihave #Hra0 : remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 0 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 0) rfl $$ Hra
  ihave #Hra1 : remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 1 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 1) rfl $$ Hra
  ihave #Hra2 : remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 2 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 2) rfl $$ Hra
  ihave #Hra3 : remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 3 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 3) rfl $$ Hra
  ihave #Hra4 : remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 4 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 4) rfl $$ Hra
  ihave #Hra5 : remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 5 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 5) rfl $$ Hra
  icases Hcl with ⟨Hc0, Hc1, Hc2, Hc3, Hc4, Hc5, -⟩
  icases Hsv with ⟨Hv0, Hv1, Hv2, Hv3, -⟩
  imodintro
  iexists fun i => if i = 0 then iprop(([∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (casR γ.proto) a) ∗ mapCtx (Gg := G) (I := In) ∗ pendCtx (Gg := G) (casR γ.proto) (casS0 (GF := remoteGF)) γp ∗ pendLib (Gg := G) (casS0 (GF := remoteGF)) γp (casS0 (GF := remoteGF)).M.init)
      else if i = 1 then iprop(clientNodeShare (G := G) γ 0 ∗ remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 0 []) ∗ mapCtx (Gg := G) (I := In))
      else if i = 2 then iprop(clientNodeShare (G := G) γ 1 ∗ remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 1 []) ∗ mapCtx (Gg := G) (I := In))
      else if i = 3 then iprop(clientNodeShare (G := G) γ 2 ∗ remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 2 []) ∗ mapCtx (Gg := G) (I := In))
      else if i = 4 then iprop(clientNodeShare (G := G) γ 3 ∗ remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 3 []) ∗ mapCtx (Gg := G) (I := In))
      else if i = 5 then iprop(clientNodeShare (G := G) γ 4 ∗ remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 4 []) ∗ mapCtx (Gg := G) (I := In))
      else if i = 6 then iprop(clientNodeShare (G := G) γ 5 ∗ remoteAddr (Gg := G) (casR γ.proto) (clientAddrs.getD 5 []) ∗ mapCtx (Gg := G) (I := In))
      else if i = 7 then iprop(serverShare (G := G) γ 0)
      else if i = 8 then iprop(serverShare (G := G) γ 1)
      else if i = 9 then iprop(serverShare (G := G) γ 2)
      else if i = 10 then iprop(serverShare (G := G) γ 3)
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
    letI : math.rand.InitHyp remoteGF := hmr G' hG.goose_localGS
    letI : wire.BinaryVarintHyps remoteGF := hbv G' hG.goose_localGS
    letI : netN.StringsIndexHyp remoteGF := hsi G' hG.goose_localGS
    letI : replica2.SortSliceHyp remoteGF := hss G' hG.goose_localGS
    letI : lib.MathPowHyp remoteGF := hmp G' hG.goose_localGS
    letI : lib.RandSeedHyp remoteGF := hrs G' hG.goose_localGS
    letI : RpcHttpHyp remoteGF := H G' hG.goose_localGS π
    letI : RpcBootHyp remoteGF := hboot G' hG.goose_localGS π
    have wdial : net.rpc.DialHTTP.spec (GF := remoteGF) (hG := hG) := hdial G' hG.goose_localGS π
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
          (init_of_gen _ _ _ (cmd.orch.wp_initialize' _ cmd.orch.getIsPkgInit_wf)) (P := iprop(([∗list] a ∈ clientAddrs, remoteAddr (Gg := G') (casR γ.proto) a) ∗ mapCtx (Gg := G') (I := In) ∗ pendCtx (Gg := G') (casR γ.proto) (casS0 (GF := remoteGF)) γp ∗ pendLib (Gg := G') (casS0 (GF := remoteGF)) γp (casS0 (GF := remoteGF)).M.init))
          (by
            iintro %Φ ⟨#Hpkg, ⟨#Has, #Hm, #Hp, Hlib⟩, -⟩ HΦ
            iapply (cmd.orch.wp_main EtcdGrove.dsvgryff.wp_Orch γ.proto γp hrb') $$ [Hlib] HΦ
            iframe #
            iframe Hlib) $$ HP Hgs
    | 1, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client0.initialize' cmd.client0.main _ cmd.client0.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client0.wp_initialize' _ cmd.client0.getIsPkgInit_wf)) (P := iprop(clientNodeShare (G := G') γ 0 ∗ remoteAddr (Gg := G') (casR γ.proto) (clientAddrs.getD 0 []) ∗ mapCtx (Gg := G') (I := In)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hr, #Hm⟩, -⟩ HΦ
            unfold clientNodeShare netShare
            icases Hsh with ⟨⟨#Hrl, -⟩, #Hsi, Hst⟩
            ihave #Hpi := sharedInvs_proto γ $$ Hsi
            iapply (cmd.client0.wp_main EtcdGrove.dsvgryff.wp_Client γ) $$ [Hst] HΦ
            unfold replicaLises
            iframe #
            iframe Hst) $$ HP Hgs
    | 2, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client1.initialize' cmd.client1.main _ cmd.client1.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client1.wp_initialize' _ cmd.client1.getIsPkgInit_wf)) (P := iprop(clientNodeShare (G := G') γ 1 ∗ remoteAddr (Gg := G') (casR γ.proto) (clientAddrs.getD 1 []) ∗ mapCtx (Gg := G') (I := In)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hr, #Hm⟩, -⟩ HΦ
            unfold clientNodeShare netShare
            icases Hsh with ⟨⟨#Hrl, -⟩, #Hsi, Hst⟩
            ihave #Hpi := sharedInvs_proto γ $$ Hsi
            iapply (cmd.client1.wp_main EtcdGrove.dsvgryff.wp_Client γ) $$ [Hst] HΦ
            unfold replicaLises
            iframe #
            iframe Hst) $$ HP Hgs
    | 3, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client2.initialize' cmd.client2.main _ cmd.client2.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client2.wp_initialize' _ cmd.client2.getIsPkgInit_wf)) (P := iprop(clientNodeShare (G := G') γ 2 ∗ remoteAddr (Gg := G') (casR γ.proto) (clientAddrs.getD 2 []) ∗ mapCtx (Gg := G') (I := In)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hr, #Hm⟩, -⟩ HΦ
            unfold clientNodeShare netShare
            icases Hsh with ⟨⟨#Hrl, -⟩, #Hsi, Hst⟩
            ihave #Hpi := sharedInvs_proto γ $$ Hsi
            iapply (cmd.client2.wp_main EtcdGrove.dsvgryff.wp_Client γ) $$ [Hst] HΦ
            unfold replicaLises
            iframe #
            iframe Hst) $$ HP Hgs
    | 4, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client3.initialize' cmd.client3.main _ cmd.client3.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client3.wp_initialize' _ cmd.client3.getIsPkgInit_wf)) (P := iprop(clientNodeShare (G := G') γ 3 ∗ remoteAddr (Gg := G') (casR γ.proto) (clientAddrs.getD 3 []) ∗ mapCtx (Gg := G') (I := In)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hr, #Hm⟩, -⟩ HΦ
            unfold clientNodeShare netShare
            icases Hsh with ⟨⟨#Hrl, -⟩, #Hsi, Hst⟩
            ihave #Hpi := sharedInvs_proto γ $$ Hsi
            iapply (cmd.client3.wp_main EtcdGrove.dsvgryff.wp_Client γ) $$ [Hst] HΦ
            unfold replicaLises
            iframe #
            iframe Hst) $$ HP Hgs
    | 5, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client4.initialize' cmd.client4.main _ cmd.client4.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client4.wp_initialize' _ cmd.client4.getIsPkgInit_wf)) (P := iprop(clientNodeShare (G := G') γ 4 ∗ remoteAddr (Gg := G') (casR γ.proto) (clientAddrs.getD 4 []) ∗ mapCtx (Gg := G') (I := In)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hr, #Hm⟩, -⟩ HΦ
            unfold clientNodeShare netShare
            icases Hsh with ⟨⟨#Hrl, -⟩, #Hsi, Hst⟩
            ihave #Hpi := sharedInvs_proto γ $$ Hsi
            iapply (cmd.client4.wp_main EtcdGrove.dsvgryff.wp_Client γ) $$ [Hst] HΦ
            unfold replicaLises
            iframe #
            iframe Hst) $$ HP Hgs
    | 6, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client5.initialize' cmd.client5.main _ cmd.client5.getIsPkgInit iprop(True)
          (init_of_gen _ _ _ (cmd.client5.wp_initialize' _ cmd.client5.getIsPkgInit_wf)) (P := iprop(clientNodeShare (G := G') γ 5 ∗ remoteAddr (Gg := G') (casR γ.proto) (clientAddrs.getD 5 []) ∗ mapCtx (Gg := G') (I := In)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hr, #Hm⟩, -⟩ HΦ
            unfold clientNodeShare netShare
            icases Hsh with ⟨⟨#Hrl, -⟩, #Hsi, Hst⟩
            ihave #Hpi := sharedInvs_proto γ $$ Hsi
            iapply (cmd.client5.wp_main EtcdGrove.dsvgryff.wp_Client γ) $$ [Hst] HΦ
            unfold replicaLises
            iframe #
            iframe Hst) $$ HP Hgs
    | 7, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server1.initialize' cmd.server1.main _ cmd.server1.getIsPkgInit
          iprop(gryff.boot.gryffGlobals ∗ gryff.boot.bootProph ∗ serverBoot (GF := remoteGF))
          cmd.server1.wp_initialize'_own (P := iprop(serverShare (G := G') γ 0))
          (by
            iintro %Φ ⟨#Hpkg, Hsh, Hglob, Hbp, Hboot⟩ HΦ
            iapply (cmd.server1.wp_main (EtcdGrove.dsvgryff.wp_Server wdial) γ) $$ [Hsh Hglob Hbp Hboot] HΦ
            iframe Hpkg Hboot Hsh
            isplitr
            · ipureintro; exact hb'
            rw [if_pos rfl]; itrivial) $$ HP Hgs
    | 8, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server2.initialize' cmd.server2.main _ cmd.server2.getIsPkgInit
          iprop(gryff.boot.gryffGlobals ∗ gryff.boot.bootProph ∗ serverBoot (GF := remoteGF))
          cmd.server2.wp_initialize'_own (P := iprop(serverShare (G := G') γ 1))
          (by
            iintro %Φ ⟨#Hpkg, Hsh, Hglob, Hbp, Hboot⟩ HΦ
            iapply (cmd.server2.wp_main (EtcdGrove.dsvgryff.wp_Server wdial) γ) $$ [Hsh Hglob Hbp Hboot] HΦ
            iframe Hpkg Hboot Hsh
            isplitr
            · ipureintro; exact hb'
            rw [if_neg (by decide)]; iframe Hglob Hbp) $$ HP Hgs
    | 9, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server3.initialize' cmd.server3.main _ cmd.server3.getIsPkgInit
          iprop(gryff.boot.gryffGlobals ∗ gryff.boot.bootProph ∗ serverBoot (GF := remoteGF))
          cmd.server3.wp_initialize'_own (P := iprop(serverShare (G := G') γ 2))
          (by
            iintro %Φ ⟨#Hpkg, Hsh, Hglob, Hbp, Hboot⟩ HΦ
            iapply (cmd.server3.wp_main (EtcdGrove.dsvgryff.wp_Server wdial) γ) $$ [Hsh Hglob Hbp Hboot] HΦ
            iframe Hpkg Hboot Hsh
            isplitr
            · ipureintro; exact hb'
            rw [if_neg (by decide)]; iframe Hglob Hbp) $$ HP Hgs
    | 10, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server4.initialize' cmd.server4.main _ cmd.server4.getIsPkgInit
          iprop(gryff.boot.gryffGlobals ∗ gryff.boot.bootProph ∗ serverBoot (GF := remoteGF))
          cmd.server4.wp_initialize'_own (P := iprop(serverShare (G := G') γ 3))
          (by
            iintro %Φ ⟨#Hpkg, Hsh, Hglob, Hbp, Hboot⟩ HΦ
            iapply (cmd.server4.wp_main (EtcdGrove.dsvgryff.wp_Server wdial) γ) $$ [Hsh Hglob Hbp Hboot] HΦ
            iframe Hpkg Hboot Hsh
            isplitr
            · ipureintro; exact hb'
            rw [if_neg (by decide)]; iframe Hglob Hbp) $$ HP Hgs
  -- the shares, node by node
  unfold system
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hlib]
  · simp only [↓reduceIte]
    iframe #
    iframe Hlib
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc0]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc0; iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc1]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc1; iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc2]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc2; iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc3]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc3; iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc4]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc4; iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc5]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc5; iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hv0]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hv0
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hv1]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hv1
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hv2]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hv2
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hv3]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hv3
  iapply BigSepL.bigSepL_nil.2
  iempintro

#print axioms gryff_remote_robust

end gryff.examples.gryffnet
end Perennial
