/-
The vr kit's top-level result (`Spec/github_com/tangledbytes/go_vsr/examples/vsrnet/TopLevelRobustness.lean`),
proved as paxos's: from the deployment's start (the registry, the addresses unset:
`robust_of_distProtoRB`), the kit's start (`vr_start`: the ghost layer, the addresses' protocols,
remote's slot map with the client addresses' call budgets, its pending library over the abstract
state, every machine's share), and each machine's boot from its share: its generated initializer's
spec and its `main`'s (`Mains.lean`) over the links (`Link.lean`)
at the model's decoder (`decRepModel`, `jsonHypsModel`) of its heap; a client's or server's boot is its first
run (`BootCmdsLinked.lean`), which returns encoding/json's fresh registry (`codecFresh`) for its
`main` (`RegisterJSON()`).
-/
module

public import Dsverify.Spec.github_com.tangledbytes.go_vsr.examples.vsrnet.TopLevelRobustness
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Link
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Start
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.BootCmdsLinked
public import Net.Statement.DistBridge
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.orch.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.orch.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client0.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client0.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client1.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client1.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client2.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client2.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client3.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client3.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client4.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client4.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client5.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client5.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server1.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server1.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server2.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server2.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server3.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server3.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server4.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server4.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server5.PkgTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server5.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.tangledbytes.go_vsr
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section boot
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A command's boot program, from its initializer's spec (with the program's package table
`getIs`) and a spec of its `main` with precondition `P` (paxos's). -/
theorem wp_boot [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    (init : val) (main pkg : GoString) [IsPkgInit (IProp GF) pkg] (getIs : GoString → IProp GF)
    (Hinit : {{ ownInitializing getIs }}
        (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getIs ∗ isPkgInit (PROP := IProp GF) pkg }})
    (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF) pkg ∗ P }}
        (App (Val (@! main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP (boot init main) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold boot
  wp_apply Hinit $$ [Hgs] as ⟨-, #Hpkg⟩
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  wp_pures
  wp_apply Hf $$ [HP]
  · iframe
  ipureintro; rfl

/-- A command's boot program, from its first-run boot (`BootCmdsLinked.lean`: from the empty
package state, it returns the boot resource `R`) and a spec of its `main` with precondition
`P ∗ R` (dsv-epaxos's). -/
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

theorem range6 : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
theorem range5 : List.range 5 = [0, 1, 2, 3, 4] := rfl

/-- **The vr kit** (see the statement's file). -/
theorem vr_remote_robust : vr_remote_robust.spec := by
  intro gctx lctx sem s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 bvi σ g threads
  refine robust_of_distProtoRB (GF := remoteGF) vrKitAddrs (system σ) g threads (2 ^ 63) ?_
  intro G π hrb
  iintro #Hreg Hs
  imod vr_start (GF := remoteGF) (G := G) $$ Hreg Hs with ⟨%ρ, %γ, %γp, Ho, Hcs, Hss⟩
  isimp only [range6] at Hcs
  isimp only [range5] at Hss
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc0, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc1, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc2, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc3, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc4, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc5, -⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs1, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs2, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs3, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs4, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs5, -⟩
  imodintro
  iexists fun i => if i = 0 then iprop(orchShare (G := G) (ρ := ρ) γ γp)
      else if i = 1 then iprop(clientShare (G := G) (ρ := ρ) γ 0)
      else if i = 2 then iprop(clientShare (G := G) (ρ := ρ) γ 1)
      else if i = 3 then iprop(clientShare (G := G) (ρ := ρ) γ 2)
      else if i = 4 then iprop(clientShare (G := G) (ρ := ρ) γ 3)
      else if i = 5 then iprop(clientShare (G := G) (ρ := ρ) γ 4)
      else if i = 6 then iprop(clientShare (G := G) (ρ := ρ) γ 5)
      else if i = 7 then iprop(srvShare (G := G) γ 1)
      else if i = 8 then iprop(srvShare (G := G) γ 2)
      else if i = 9 then iprop(srvShare (G := G) γ 3)
      else if i = 10 then iprop(srvShare (G := G) γ 4)
      else if i = 11 then iprop(srvShare (G := G) γ 5)
      else iprop(True)
  isplitr
  · ipureintro
    intro i m hm hG hGG hctx
    obtain ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    dsimp only at hGG hctx
    subst hGG hctx
    letI hG : HeapGS .hasLC remoteGF := ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    letI := encoding.json.decRepModel (hG := hG)
    have hJ := EtcdGrove.dsvvr.jsonHypsModel (GF := remoteGF) (hG := hG)
    letI := encoding.json.encRepModel (hG := hG)
    match i, hm with
    | 0, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_boot cmd.orch.initialize' cmd.orch.main _ cmd.orch.getIsPkgInit
          (cmd.orch.wp_initialize' _ cmd.orch.getIsPkgInit_wf) (orchShare (G := G') (ρ := ρ) γ γp)
          (by
            iintro %Φ ⟨#Hpkg, HP⟩ HΦ
            iunfold orchShare at HP
            icases HP with ⟨#Hs, Hz, #Hc, #Ha, #Hm, #Hp, Hl, Hb⟩
            iapply (cmd.orch.wp_main (ρ := ρ) (EtcdGrove.dsvvr.wp_Orch) γ γp hrb) $$ [Hz Hl Hb] HΦ
            iframe #
            iframe) $$ HP Hgs
    | 1, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client0.initialize' cmd.client0.main _ cmd.client0.getIsPkgInit
          (encoding.json.codecFresh (GF := remoteGF)) cmd.client0.wp_boot
          (clientShare (G := G') (ρ := ρ) γ 0)
          (by
            iintro %Φ ⟨#Hpkg, HP, Hfr⟩ HΦ
            iunfold clientShare at HP
            icases HP with ⟨#Hc, #Hv, #Hs, #Hr, Hn, #Ha, #Hb⟩
            ihave #HnP : pkg.network.netProtos (GF := remoteGF) γ $$ [Hv]
            · unfold pkg.network.netProtos; iexact Hv
            iapply (cmd.client0.wp_main (ρ := ρ) (EtcdGrove.dsvvr.wp_Client hJ) γ) $$ [Hn Hfr] HΦ
            iframe #
            iframe) $$ HP Hgs
    | 2, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client1.initialize' cmd.client1.main _ cmd.client1.getIsPkgInit
          (encoding.json.codecFresh (GF := remoteGF)) cmd.client1.wp_boot
          (clientShare (G := G') (ρ := ρ) γ 1)
          (by
            iintro %Φ ⟨#Hpkg, HP, Hfr⟩ HΦ
            iunfold clientShare at HP
            icases HP with ⟨#Hc, #Hv, #Hs, #Hr, Hn, #Ha, #Hb⟩
            ihave #HnP : pkg.network.netProtos (GF := remoteGF) γ $$ [Hv]
            · unfold pkg.network.netProtos; iexact Hv
            iapply (cmd.client1.wp_main (ρ := ρ) (EtcdGrove.dsvvr.wp_Client hJ) γ) $$ [Hn Hfr] HΦ
            iframe #
            iframe) $$ HP Hgs
    | 3, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client2.initialize' cmd.client2.main _ cmd.client2.getIsPkgInit
          (encoding.json.codecFresh (GF := remoteGF)) cmd.client2.wp_boot
          (clientShare (G := G') (ρ := ρ) γ 2)
          (by
            iintro %Φ ⟨#Hpkg, HP, Hfr⟩ HΦ
            iunfold clientShare at HP
            icases HP with ⟨#Hc, #Hv, #Hs, #Hr, Hn, #Ha, #Hb⟩
            ihave #HnP : pkg.network.netProtos (GF := remoteGF) γ $$ [Hv]
            · unfold pkg.network.netProtos; iexact Hv
            iapply (cmd.client2.wp_main (ρ := ρ) (EtcdGrove.dsvvr.wp_Client hJ) γ) $$ [Hn Hfr] HΦ
            iframe #
            iframe) $$ HP Hgs
    | 4, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client3.initialize' cmd.client3.main _ cmd.client3.getIsPkgInit
          (encoding.json.codecFresh (GF := remoteGF)) cmd.client3.wp_boot
          (clientShare (G := G') (ρ := ρ) γ 3)
          (by
            iintro %Φ ⟨#Hpkg, HP, Hfr⟩ HΦ
            iunfold clientShare at HP
            icases HP with ⟨#Hc, #Hv, #Hs, #Hr, Hn, #Ha, #Hb⟩
            ihave #HnP : pkg.network.netProtos (GF := remoteGF) γ $$ [Hv]
            · unfold pkg.network.netProtos; iexact Hv
            iapply (cmd.client3.wp_main (ρ := ρ) (EtcdGrove.dsvvr.wp_Client hJ) γ) $$ [Hn Hfr] HΦ
            iframe #
            iframe) $$ HP Hgs
    | 5, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client4.initialize' cmd.client4.main _ cmd.client4.getIsPkgInit
          (encoding.json.codecFresh (GF := remoteGF)) cmd.client4.wp_boot
          (clientShare (G := G') (ρ := ρ) γ 4)
          (by
            iintro %Φ ⟨#Hpkg, HP, Hfr⟩ HΦ
            iunfold clientShare at HP
            icases HP with ⟨#Hc, #Hv, #Hs, #Hr, Hn, #Ha, #Hb⟩
            ihave #HnP : pkg.network.netProtos (GF := remoteGF) γ $$ [Hv]
            · unfold pkg.network.netProtos; iexact Hv
            iapply (cmd.client4.wp_main (ρ := ρ) (EtcdGrove.dsvvr.wp_Client hJ) γ) $$ [Hn Hfr] HΦ
            iframe #
            iframe) $$ HP Hgs
    | 6, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.client5.initialize' cmd.client5.main _ cmd.client5.getIsPkgInit
          (encoding.json.codecFresh (GF := remoteGF)) cmd.client5.wp_boot
          (clientShare (G := G') (ρ := ρ) γ 5)
          (by
            iintro %Φ ⟨#Hpkg, HP, Hfr⟩ HΦ
            iunfold clientShare at HP
            icases HP with ⟨#Hc, #Hv, #Hs, #Hr, Hn, #Ha, #Hb⟩
            ihave #HnP : pkg.network.netProtos (GF := remoteGF) γ $$ [Hv]
            · unfold pkg.network.netProtos; iexact Hv
            iapply (cmd.client5.wp_main (ρ := ρ) (EtcdGrove.dsvvr.wp_Client hJ) γ) $$ [Hn Hfr] HΦ
            iframe #
            iframe) $$ HP Hgs
    | 7, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server1.initialize' cmd.server1.main _ cmd.server1.getIsPkgInit
          (encoding.json.codecFresh (GF := remoteGF)) cmd.server1.wp_boot (srvShare (G := G') γ 1)
          (by
            iintro %Φ ⟨#Hpkg, HP, Hfr⟩ HΦ
            iapply (cmd.server1.wp_main (EtcdGrove.dsvvr.wp_Server hJ) γ) $$ [HP Hfr] HΦ
            iframe #
            iframe) $$ HP Hgs
    | 8, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server2.initialize' cmd.server2.main _ cmd.server2.getIsPkgInit
          (encoding.json.codecFresh (GF := remoteGF)) cmd.server2.wp_boot (srvShare (G := G') γ 2)
          (by
            iintro %Φ ⟨#Hpkg, HP, Hfr⟩ HΦ
            iapply (cmd.server2.wp_main (EtcdGrove.dsvvr.wp_Server hJ) γ) $$ [HP Hfr] HΦ
            iframe #
            iframe) $$ HP Hgs
    | 9, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server3.initialize' cmd.server3.main _ cmd.server3.getIsPkgInit
          (encoding.json.codecFresh (GF := remoteGF)) cmd.server3.wp_boot (srvShare (G := G') γ 3)
          (by
            iintro %Φ ⟨#Hpkg, HP, Hfr⟩ HΦ
            iapply (cmd.server3.wp_main (EtcdGrove.dsvvr.wp_Server hJ) γ) $$ [HP Hfr] HΦ
            iframe #
            iframe) $$ HP Hgs
    | 10, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server4.initialize' cmd.server4.main _ cmd.server4.getIsPkgInit
          (encoding.json.codecFresh (GF := remoteGF)) cmd.server4.wp_boot (srvShare (G := G') γ 4)
          (by
            iintro %Φ ⟨#Hpkg, HP, Hfr⟩ HΦ
            iapply (cmd.server4.wp_main (EtcdGrove.dsvvr.wp_Server hJ) γ) $$ [HP Hfr] HΦ
            iframe #
            iframe) $$ HP Hgs
    | 11, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs
      iapply wp_bootR cmd.server5.initialize' cmd.server5.main _ cmd.server5.getIsPkgInit
          (encoding.json.codecFresh (GF := remoteGF)) cmd.server5.wp_boot (srvShare (G := G') γ 5)
          (by
            iintro %Φ ⟨#Hpkg, HP, Hfr⟩ HΦ
            iapply (cmd.server5.wp_main (EtcdGrove.dsvvr.wp_Server hJ) γ) $$ [HP Hfr] HΦ
            iframe #
            iframe) $$ HP Hgs
  · simp only [system]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ho]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Ho
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc0]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hc0
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc1]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hc1
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc2]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hc2
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc3]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hc3
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc4]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hc4
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc5]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hc5
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hs1]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hs1
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hs2]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hs2
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hs3]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hs3
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hs4]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hs4
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hs5]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hs5
    iapply BigSepL.bigSepL_nil.2
    iempintro

#print axioms vr_remote_robust

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
