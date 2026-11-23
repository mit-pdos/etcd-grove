/-
The SwiftPaxos kit's top-level result (`Spec/github_com/imdea_software/swiftpaxos/examples/swiftnet/TopLevelRobustness.lean`),
proved as dsv-epaxos's: from the deployment's start (the registry, the addresses unset, the
listeners unset: `robust_of_distProtoLisRBT_sha`, over the kit's two extensions), the kit's start
(`sw_start`: the names, the rpc world, remote's store's ghost variable, the machines' shares),
remote's map of operations, the client addresses' remote protocols, remote's pending library over
the store `swRK γk`, and each machine's boot: its command's first initialization
(`BootCmds.lean`, `wp_boot`: `bootRes`) and its `main` (`Mains.lean`) over the linked machine
specs (`Link.lean`).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.TopLevelRobustness
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Mains
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Bridge
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.BootCmds
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Start

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness Dsv

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.imdea_software.swiftpaxos
  github_com.imdea_software.swiftpaxos.cnode

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has
  netShaExts_hasSha256 GooseGlobalGS.gooseInvGS

section boot
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A command's boot program, from its initializer's spec from the empty package state (its
result `R` handed to `main`) and a spec of its `main` with precondition `P ∗ R` (dsv-epaxos's). -/
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

end boot

section res
variable [GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [net.rpc.Assumptions] [net.FieldAssumptions]
variable [log.Assumptions] [net.http.Assumptions] [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

/-- A client machine's boot resources, from its boot. -/
theorem bootRes_client (hrb : receiptBound netDistGF ≤ 2 ^ 64) :
    bootRes ⊢ client.ghostFresh ∗ codecFresh ∗ cliBoot ∗
      globalAddr swift.useFastAckPool ↦ false := by
  unfold bootRes rpcBootRes
  iintro ⟨Hfr, Hmg, Hmu, Hcu, #Hse, -, -, #Hde⟩
  unfold swift.mutGlobalsInit
  icases Hmg with ⟨-, Hp, -⟩
  iframe Hfr Hp
  unfold codecFresh cliBoot
  iframe Hmu Hcu Hde
  iunfold net.rpc.srvEnv at Hse
  icases Hse with ⟨#Hce, -⟩
  iframe Hce
  ipureintro; exact hrb

/-- Server machine `i + 1`'s boot resources, from its boot. -/
theorem bootRes_server (i : Nat)
    (hb : threadBound netDistGF ≤ 2 ^ 31 ∧ receiptBound netDistGF ≤ 2 ^ 64) :
    bootRes ⊢ srvBoot i := by
  unfold bootRes rpcBootRes srvBoot
  iintro ⟨Hfr, Hmg, Hmu, Hcu, #Hse, Hmux, Hds, #Hde⟩
  iframe Hmux Hds Hse
  unfold codecFresh cliBoot
  iframe Hmu Hcu Hde
  iunfold net.rpc.srvEnv at Hse
  icases Hse with ⟨#Hce, -⟩
  iframe Hce
  isplitr
  · ipureintro; exact hb.2
  isplitr
  · ipureintro; exact hb.1
  split
  · itrivial
  · iframe Hfr
    iapply swift.mutGlobalsInit_mutGlobals $$ Hmg

end res

/-- `sw_start` at the libraries `libsAt l π`, its net resources at `π` itself. -/
theorem sw_start_at [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]
    (l : SwiftNetPkgState netDistGF) (π : NetProtoGS)
    (RA : @RpcHttpAddr netDistGF G (libsAt l π)) :
    letI := libsAt l π; ⊢ regCtx (π := π) -∗ ([∗list] a ∈ swStartAddrs, addrUnset a) -∗
      ([∗list] la ∈ swLas, lisUnset la) ={⊤}=∗
      ∃ (γ : SwiftNames netDistGF) (γk : GName),
        common γ ∗ conf.writer γ ∗ cnode.linkInv γ γk ∗
        cnode.sysK γk (examples.swiftnet.swB.init) ∗
        ([∗list] c ∈ List.range 6, clientNodeShare γ c) ∗
        ([∗list] i ∈ List.range 6, serverShare γ i) :=
  @sw_start _ G (libsAt l π) RA

/-- **The SwiftPaxos kit, closed** (see the statement's file). -/
theorem swiftpaxos_remote_robust : swiftpaxos_remote_robust.spec := by
  intro gctx lctx sem s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 fsem bvi l hrand hri hhi hji hgi hsi hui hsw hns hor ra rh hfi σ g threads
  refine robust_of_distProtoLisRBT_sha (GF := netDistGF) swAddrs swLas (system σ) g threads
    (2 ^ 31 - 1) swLas_pairwise swLas_disj ?_
  intro G π hrb
  letI := libsAt l π
  letI := ra G π
  iintro #Hreg Hs Hl
  unfold swAddrs
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hss, Hsc⟩
  imod sw_start_at l π (ra G π) $$ Hreg Hss Hl with ⟨%γ, %γk, #Hcom, Hw, #Hli, Hsys, Hcs, Hss⟩
  imod mapCtx_alloc (Gg := G) (I := KIn) ⊤ with ⟨%ρ, #Hmap⟩
  imod addrs_set_proto (Gg := G) ⊤ (fun _ => reqP (Gg := G) (RBase.svc (swRK (G := G) γk)))
    (fun _ => repP (Gg := G) (RBase.svc (swRK (G := G) γk))) clientAddrs $$ Hreg Hsc with #Hpc
  haveI : ∀ st, Timeless ((swRK (G := G) γk).sysState st) := fun st => by
    unfold swRK swR; dsimp only; infer_instance
  have hv : cnode.sysK (G := G) γk swB.init ⊢
      (swRK (G := G) γk).sysState (swRK (G := G) γk).B.init := .rfl
  ihave Hsys := hv $$ Hsys
  imod pend_alloc (Gg := G) (swRK (G := G) γk) ⊤ (swS0 (GF := netDistGF)) rfl $$ Hsys
    with ⟨%γp, #Hpend, Hlib⟩
  ihave #Hra : [∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (swRK (G := G) γk) a $$ [Hpc]
  · unfold remoteAddr svcAddr; iexact Hpc
  ihave #Hra0 : remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 0 go!"") $$ []
  · iapply BigSepL.bigSepL_lookup (i := 0) rfl $$ Hra
  ihave #Hra1 : remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 1 go!"") $$ []
  · iapply BigSepL.bigSepL_lookup (i := 1) rfl $$ Hra
  ihave #Hra2 : remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 2 go!"") $$ []
  · iapply BigSepL.bigSepL_lookup (i := 2) rfl $$ Hra
  ihave #Hra3 : remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 3 go!"") $$ []
  · iapply BigSepL.bigSepL_lookup (i := 3) rfl $$ Hra
  ihave #Hra4 : remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 4 go!"") $$ []
  · iapply BigSepL.bigSepL_lookup (i := 4) rfl $$ Hra
  ihave #Hra5 : remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 5 go!"") $$ []
  · iapply BigSepL.bigSepL_lookup (i := 5) rfl $$ Hra
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc0, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc1, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc2, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc3, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc4, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc5, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs0, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs1, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs2, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs3, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs4, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs5, Hss⟩
  imodintro
  iexists fun i =>
      if i = 0 then iprop(conf.writer γ ∗ common γ ∗ ([∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (swRK (G := G) γk) a) ∗ mapCtx (Gg := G) (I := KIn) ∗ pendCtx (Gg := G) (swRK (G := G) γk) (swS0 (GF := netDistGF)) γp ∗ pendLib (Gg := G) (swS0 (GF := netDistGF)) γp (swS0 (GF := netDistGF)).M.init)
      else if i = 1 then iprop(clientNodeShare γ 0 ∗ cnode.linkInv (G := G) γ γk ∗ remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 0 go!"") ∗ mapCtx (Gg := G) (I := KIn))
      else if i = 2 then iprop(clientNodeShare γ 1 ∗ cnode.linkInv (G := G) γ γk ∗ remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 1 go!"") ∗ mapCtx (Gg := G) (I := KIn))
      else if i = 3 then iprop(clientNodeShare γ 2 ∗ cnode.linkInv (G := G) γ γk ∗ remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 2 go!"") ∗ mapCtx (Gg := G) (I := KIn))
      else if i = 4 then iprop(clientNodeShare γ 3 ∗ cnode.linkInv (G := G) γ γk ∗ remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 3 go!"") ∗ mapCtx (Gg := G) (I := KIn))
      else if i = 5 then iprop(clientNodeShare γ 4 ∗ cnode.linkInv (G := G) γ γk ∗ remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 4 go!"") ∗ mapCtx (Gg := G) (I := KIn))
      else if i = 6 then iprop(clientNodeShare γ 5 ∗ cnode.linkInv (G := G) γ γk ∗ remoteAddr (Gg := G) (swRK (G := G) γk) (clientAddrs.getD 5 go!"") ∗ mapCtx (Gg := G) (I := KIn))
      else if i = 7 then iprop(serverShare γ 0)
      else if i = 8 then iprop(serverShare γ 1)
      else if i = 9 then iprop(serverShare γ 2)
      else if i = 10 then iprop(serverShare γ 3)
      else if i = 11 then iprop(serverShare γ 4)
      else if i = 12 then iprop(serverShare γ 5)
      else iprop(True)
  isplitr
  · ipureintro
    intro i m hm hG hGG hctx hT
    obtain ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    dsimp only at hGG hctx hT
    subst hGG hctx
    letI hG : HeapGS .hasLC netDistGF := ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    letI : math.rand.InitHyp netDistGF := hrand G' hG.goose_localGS
    letI : net.rpc.InitHyp netDistGF := hri G' hG.goose_localGS
    letI : net.http.InitHyp netDistGF := hhi G' hG.goose_localGS
    letI : encoding.json.InitHyp netDistGF := hji G' hG.goose_localGS
    letI : encoding.gob.InitHyp netDistGF := hgi G' hG.goose_localGS
    letI : os.signal.InitHyp netDistGF := hsi G' hG.goose_localGS
    letI : github_com.google.uuid.InitHyp netDistGF := hui G' hG.goose_localGS
    letI : SwiftHyps netDistGF := hsw G' hG.goose_localGS π
    letI : SwiftNoSignals netDistGF := hns G' hG.goose_localGS π
    letI : SwiftOsRandom netDistGF := hor G' hG.goose_localGS π
    letI : RpcHttpHyp netDistGF := rh G' hG.goose_localGS π
    letI : RpcFirstInit (GF := netDistGF) := hfi G' hG.goose_localGS π
    have hrb' : receiptBound netDistGF ≤ 2 ^ 63 := by omega
    have hb' : threadBound netDistGF ≤ 2 ^ 31 ∧ receiptBound netDistGF ≤ 2 ^ 64 := by
      constructor <;> omega
    match i, hm with
    | 0, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.orch.initialize' cmd.orch.main _ cmd.orch.getIsPkgInit bootRes
          cmd.orch.wp_boot (P := iprop(conf.writer γ ∗ common γ ∗ ([∗list] a ∈ clientAddrs, remoteAddr (Gg := G') (swRK (G := G') γk) a) ∗ mapCtx (Gg := G') (I := KIn) ∗ pendCtx (Gg := G') (swRK (G := G') γk) (swS0 (GF := netDistGF)) γp ∗ pendLib (Gg := G') (swS0 (GF := netDistGF)) γp (swS0 (GF := netDistGF)).M.init))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hw, #Hc, #Has, #Hm, #Hp, Hlib⟩, -⟩ HΦ
            iapply (cmd.orch.wp_main (ρ := ρ) EtcdGrove.dsvswiftpaxos.wp_Orch γ γk γp hrb') $$ [Hw Hlib] HΦ
            iframe Hw Hlib
            iframe #) $$ HP Hgs
    | 1, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client0.initialize' cmd.client0.main _ cmd.client0.getIsPkgInit bootRes
          cmd.client0.wp_boot (P := iprop(clientNodeShare γ 0 ∗ cnode.linkInv (G := G') γ γk ∗ remoteAddr (Gg := G') (swRK (G := G') γk) (clientAddrs.getD 0 go!"") ∗ mapCtx (Gg := G') (I := KIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hli, #Hra, #Hm⟩, HR⟩ HΦ
            ihave ⟨Hfr, Hcf, #Hcb, Hpool⟩ := bootRes_client hb'.2 $$ HR
            ipersist Hpool
            iapply (cmd.client0.wp_main (ρ := ρ) EtcdGrove.dsvswiftpaxos.wp_Client γ γk) $$ [Hsh Hfr Hcf] HΦ
            iframe #
            unfold cnode.clientRes
            iframe Hsh Hfr Hcf
            iframe #) $$ HP Hgs
    | 2, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client1.initialize' cmd.client1.main _ cmd.client1.getIsPkgInit bootRes
          cmd.client1.wp_boot (P := iprop(clientNodeShare γ 1 ∗ cnode.linkInv (G := G') γ γk ∗ remoteAddr (Gg := G') (swRK (G := G') γk) (clientAddrs.getD 1 go!"") ∗ mapCtx (Gg := G') (I := KIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hli, #Hra, #Hm⟩, HR⟩ HΦ
            ihave ⟨Hfr, Hcf, #Hcb, Hpool⟩ := bootRes_client hb'.2 $$ HR
            ipersist Hpool
            iapply (cmd.client1.wp_main (ρ := ρ) EtcdGrove.dsvswiftpaxos.wp_Client γ γk) $$ [Hsh Hfr Hcf] HΦ
            iframe #
            unfold cnode.clientRes
            iframe Hsh Hfr Hcf
            iframe #) $$ HP Hgs
    | 3, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client2.initialize' cmd.client2.main _ cmd.client2.getIsPkgInit bootRes
          cmd.client2.wp_boot (P := iprop(clientNodeShare γ 2 ∗ cnode.linkInv (G := G') γ γk ∗ remoteAddr (Gg := G') (swRK (G := G') γk) (clientAddrs.getD 2 go!"") ∗ mapCtx (Gg := G') (I := KIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hli, #Hra, #Hm⟩, HR⟩ HΦ
            ihave ⟨Hfr, Hcf, #Hcb, Hpool⟩ := bootRes_client hb'.2 $$ HR
            ipersist Hpool
            iapply (cmd.client2.wp_main (ρ := ρ) EtcdGrove.dsvswiftpaxos.wp_Client γ γk) $$ [Hsh Hfr Hcf] HΦ
            iframe #
            unfold cnode.clientRes
            iframe Hsh Hfr Hcf
            iframe #) $$ HP Hgs
    | 4, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client3.initialize' cmd.client3.main _ cmd.client3.getIsPkgInit bootRes
          cmd.client3.wp_boot (P := iprop(clientNodeShare γ 3 ∗ cnode.linkInv (G := G') γ γk ∗ remoteAddr (Gg := G') (swRK (G := G') γk) (clientAddrs.getD 3 go!"") ∗ mapCtx (Gg := G') (I := KIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hli, #Hra, #Hm⟩, HR⟩ HΦ
            ihave ⟨Hfr, Hcf, #Hcb, Hpool⟩ := bootRes_client hb'.2 $$ HR
            ipersist Hpool
            iapply (cmd.client3.wp_main (ρ := ρ) EtcdGrove.dsvswiftpaxos.wp_Client γ γk) $$ [Hsh Hfr Hcf] HΦ
            iframe #
            unfold cnode.clientRes
            iframe Hsh Hfr Hcf
            iframe #) $$ HP Hgs
    | 5, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client4.initialize' cmd.client4.main _ cmd.client4.getIsPkgInit bootRes
          cmd.client4.wp_boot (P := iprop(clientNodeShare γ 4 ∗ cnode.linkInv (G := G') γ γk ∗ remoteAddr (Gg := G') (swRK (G := G') γk) (clientAddrs.getD 4 go!"") ∗ mapCtx (Gg := G') (I := KIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hli, #Hra, #Hm⟩, HR⟩ HΦ
            ihave ⟨Hfr, Hcf, #Hcb, Hpool⟩ := bootRes_client hb'.2 $$ HR
            ipersist Hpool
            iapply (cmd.client4.wp_main (ρ := ρ) EtcdGrove.dsvswiftpaxos.wp_Client γ γk) $$ [Hsh Hfr Hcf] HΦ
            iframe #
            unfold cnode.clientRes
            iframe Hsh Hfr Hcf
            iframe #) $$ HP Hgs
    | 6, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client5.initialize' cmd.client5.main _ cmd.client5.getIsPkgInit bootRes
          cmd.client5.wp_boot (P := iprop(clientNodeShare γ 5 ∗ cnode.linkInv (G := G') γ γk ∗ remoteAddr (Gg := G') (swRK (G := G') γk) (clientAddrs.getD 5 go!"") ∗ mapCtx (Gg := G') (I := KIn)))
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, #Hli, #Hra, #Hm⟩, HR⟩ HΦ
            ihave ⟨Hfr, Hcf, #Hcb, Hpool⟩ := bootRes_client hb'.2 $$ HR
            ipersist Hpool
            iapply (cmd.client5.wp_main (ρ := ρ) EtcdGrove.dsvswiftpaxos.wp_Client γ γk) $$ [Hsh Hfr Hcf] HΦ
            iframe #
            unfold cnode.clientRes
            iframe Hsh Hfr Hcf
            iframe #) $$ HP Hgs
    | 7, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server1.initialize' cmd.server1.main _ cmd.server1.getIsPkgInit bootRes
          cmd.server1.wp_boot (P := iprop(serverShare γ 0))
          (by
            iintro %Φ ⟨#Hpkg, Hsh, HR⟩ HΦ
            ihave HB := bootRes_server 0 hb' $$ HR
            iapply (cmd.server1.wp_main EtcdGrove.dsvswiftpaxos.wp_Server γ) $$ [Hsh HB] HΦ
            iframe #
            unfold serverRes
            iframe Hsh HB) $$ HP Hgs
    | 8, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server2.initialize' cmd.server2.main _ cmd.server2.getIsPkgInit bootRes
          cmd.server2.wp_boot (P := iprop(serverShare γ 1))
          (by
            iintro %Φ ⟨#Hpkg, Hsh, HR⟩ HΦ
            ihave HB := bootRes_server 1 hb' $$ HR
            iapply (cmd.server2.wp_main EtcdGrove.dsvswiftpaxos.wp_Server γ) $$ [Hsh HB] HΦ
            iframe #
            unfold serverRes
            iframe Hsh HB) $$ HP Hgs
    | 9, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server3.initialize' cmd.server3.main _ cmd.server3.getIsPkgInit bootRes
          cmd.server3.wp_boot (P := iprop(serverShare γ 2))
          (by
            iintro %Φ ⟨#Hpkg, Hsh, HR⟩ HΦ
            ihave HB := bootRes_server 2 hb' $$ HR
            iapply (cmd.server3.wp_main EtcdGrove.dsvswiftpaxos.wp_Server γ) $$ [Hsh HB] HΦ
            iframe #
            unfold serverRes
            iframe Hsh HB) $$ HP Hgs
    | 10, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server4.initialize' cmd.server4.main _ cmd.server4.getIsPkgInit bootRes
          cmd.server4.wp_boot (P := iprop(serverShare γ 3))
          (by
            iintro %Φ ⟨#Hpkg, Hsh, HR⟩ HΦ
            ihave HB := bootRes_server 3 hb' $$ HR
            iapply (cmd.server4.wp_main EtcdGrove.dsvswiftpaxos.wp_Server γ) $$ [Hsh HB] HΦ
            iframe #
            unfold serverRes
            iframe Hsh HB) $$ HP Hgs
    | 11, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server5.initialize' cmd.server5.main _ cmd.server5.getIsPkgInit bootRes
          cmd.server5.wp_boot (P := iprop(serverShare γ 4))
          (by
            iintro %Φ ⟨#Hpkg, Hsh, HR⟩ HΦ
            ihave HB := bootRes_server 4 hb' $$ HR
            iapply (cmd.server5.wp_main EtcdGrove.dsvswiftpaxos.wp_Server γ) $$ [Hsh HB] HΦ
            iframe #
            unfold serverRes
            iframe Hsh HB) $$ HP Hgs
    | 12, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server6.initialize' cmd.server6.main _ cmd.server6.getIsPkgInit bootRes
          cmd.server6.wp_boot (P := iprop(serverShare γ 5))
          (by
            iintro %Φ ⟨#Hpkg, Hsh, HR⟩ HΦ
            ihave HB := bootRes_server 5 hb' $$ HR
            iapply (cmd.server6.wp_main EtcdGrove.dsvswiftpaxos.wp_Server γ) $$ [Hsh HB] HΦ
            iframe #
            unfold serverRes
            iframe Hsh HB) $$ HP Hgs
  unfold system
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hw Hlib]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hw Hlib
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc0]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc0
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc1]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc1
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc2]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc2
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc3]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc3
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc4]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc4
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hc5]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hc5
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hs0]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hs0
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hs1]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hs1
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hs2]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hs2
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hs3]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hs3
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hs4]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hs4
    try iframe #
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hs5]
  · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    iframe Hs5
    try iframe #
  iapply BigSepL.bigSepL_nil.2
  iempintro

#print axioms swiftpaxos_remote_robust

end github_com.imdea_software.swiftpaxos.examples.swiftnet
end Perennial
