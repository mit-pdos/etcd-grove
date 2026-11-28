/-
The hraft kit's top-level result (`Spec/github_com/hashicorp/raft/examples/hraftnet/TopLevelRobustness.lean`),
proved (as craq's and vr's): from the deployment's start (the registry, the addresses unset:
dsv-epaxos's `robust_of_distProtoLisRBTT`, no wildcard listener; runs of fewer than `hraftStepBound`
steps, each machine's thread bound `hraftThreadBound`, its main thread's token), the kit's start
(`hraft_start`, run at the start's heap `atStart lctx G`: `StartAt.lean`), and each machine's boot
from its share (converted to its own heap, `orchShare_at`, `cliShare_at`, `srvShare_at`): its
first-run boot (`BootCmdsLinked.lean`, `wp_boot`: net/rpc's codec unregistered) and its `main`'s spec
(`Mains.lean`) over the kit's links (`Link.lean`: `wp_Orch`, `wp_Client`, `wp_Server`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.TopLevelRobustness
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Link
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.StartAt
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Mains
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.BootCmdsLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Bridge

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section boot
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A command's boot program, from its first-run boot (from the empty package state, it returns the
boot resource `R`) and a spec of its `main` with precondition `P ∗ R` (craq's). -/
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

theorem range5 : List.range 5 = [0, 1, 2, 3, 4] := rfl
theorem range'16 : List.range' 1 6 = [1, 2, 3, 4, 5, 6] := rfl

/-- **The hraft kit, closed** (see the statement's file). -/
theorem hraft_nocrash_robust : hraft_nocrash_robust.spec := by
  intro gctx lctx sem s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 bvi σ g
  refine github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.robust_of_distProtoLisRBTT
    (GF := remoteGF) hraftKitAddrs [] (system σ) g hraftThreadBound hraftStepBound List.Pairwise.nil
    (fun _ _ _ h => by simp at h) ?_
  intro G π hrb
  haveI hRB : ReceiptBoundLe remoteGF (2 ^ 62) := ⟨hrb⟩
  iintro #Hreg Hs -
  imod hraft_start (hG := atStart lctx G) $$ Hreg Hs with ⟨%ρ, %K, %γp, Ho, Hcs, Hss⟩
  isimp only [range5] at Hcs
  isimp only [range'16] at Hss
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc0, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc1, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc2, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc3, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc4, -⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs1, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs2, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs3, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs4, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs5, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs6, -⟩
  imodintro
  iexists fun i => if i = 0 then iprop(orchShare (hG := atStart lctx G) (ρ := ρ) K γp)
      else if i = 1 then iprop(cliShare (hG := atStart lctx G) (ρ := ρ) K 0)
      else if i = 2 then iprop(cliShare (hG := atStart lctx G) (ρ := ρ) K 1)
      else if i = 3 then iprop(cliShare (hG := atStart lctx G) (ρ := ρ) K 2)
      else if i = 4 then iprop(cliShare (hG := atStart lctx G) (ρ := ρ) K 3)
      else if i = 5 then iprop(cliShare (hG := atStart lctx G) (ρ := ρ) K 4)
      else if i = 6 then iprop(srvShare (hG := atStart lctx G) K 1)
      else if i = 7 then iprop(srvShare (hG := atStart lctx G) K 2)
      else if i = 8 then iprop(srvShare (hG := atStart lctx G) K 3)
      else if i = 9 then iprop(srvShare (hG := atStart lctx G) K 4)
      else if i = 10 then iprop(srvShare (hG := atStart lctx G) K 5)
      else if i = 11 then iprop(srvShare (hG := atStart lctx G) K 6)
      else iprop(True)
  isplitr
  · ipureintro
    intro i m hm hG hGG hctx hT
    obtain ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    dsimp only at hGG hctx hT
    subst hGG hctx
    letI hG : HeapGS .hasLC remoteGF := ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    haveI htb : ThreadBoundLe remoteGF (2 ^ 28) := ⟨hT⟩
    have hrb64 : receiptBound remoteGF ≤ 2 ^ 64 := by
      have := hRB.receiptBound_le; omega
    have hb : receiptBound remoteGF ≤ 2 ^ 64 ∧ threadBound remoteGF ≤ 2 ^ 31 := by
      have := htb.threadBound_le; constructor <;> omega
    match i, hm with
    | 0, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs -
      iapply wp_bootR cmd.orch.initialize' cmd.orch.main _ cmd.orch.getIsPkgInit net.rpc.codecUnset
          cmd.orch.wp_boot (orchShare (hG := hG) (ρ := ρ) K γp)
          (cmd.orch.wp_main EtcdGrove.hraftnet.wp_Orch K γp) $$ [HP] Hgs
      iapply orchShare_at G' Lexts Lheap Lgs Lthr Lcr K γp $$ HP
    | 1, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs -
      iapply wp_bootR cmd.client0.initialize' cmd.client0.main _ cmd.client0.getIsPkgInit
          net.rpc.codecUnset cmd.client0.wp_boot (cliShare (hG := hG) (ρ := ρ) K 0)
          (cmd.client0.wp_main EtcdGrove.hraftnet.wp_Client K hrb64) $$ [HP] Hgs
      iapply cliShare_at G' Lexts Lheap Lgs Lthr Lcr K 0 $$ HP
    | 2, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs -
      iapply wp_bootR cmd.client1.initialize' cmd.client1.main _ cmd.client1.getIsPkgInit
          net.rpc.codecUnset cmd.client1.wp_boot (cliShare (hG := hG) (ρ := ρ) K 1)
          (cmd.client1.wp_main EtcdGrove.hraftnet.wp_Client K hrb64) $$ [HP] Hgs
      iapply cliShare_at G' Lexts Lheap Lgs Lthr Lcr K 1 $$ HP
    | 3, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs -
      iapply wp_bootR cmd.client2.initialize' cmd.client2.main _ cmd.client2.getIsPkgInit
          net.rpc.codecUnset cmd.client2.wp_boot (cliShare (hG := hG) (ρ := ρ) K 2)
          (cmd.client2.wp_main EtcdGrove.hraftnet.wp_Client K hrb64) $$ [HP] Hgs
      iapply cliShare_at G' Lexts Lheap Lgs Lthr Lcr K 2 $$ HP
    | 4, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs -
      iapply wp_bootR cmd.client3.initialize' cmd.client3.main _ cmd.client3.getIsPkgInit
          net.rpc.codecUnset cmd.client3.wp_boot (cliShare (hG := hG) (ρ := ρ) K 3)
          (cmd.client3.wp_main EtcdGrove.hraftnet.wp_Client K hrb64) $$ [HP] Hgs
      iapply cliShare_at G' Lexts Lheap Lgs Lthr Lcr K 3 $$ HP
    | 5, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs -
      iapply wp_bootR cmd.client4.initialize' cmd.client4.main _ cmd.client4.getIsPkgInit
          net.rpc.codecUnset cmd.client4.wp_boot (cliShare (hG := hG) (ρ := ρ) K 4)
          (cmd.client4.wp_main EtcdGrove.hraftnet.wp_Client K hrb64) $$ [HP] Hgs
      iapply cliShare_at G' Lexts Lheap Lgs Lthr Lcr K 4 $$ HP
    | 6, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs Htok
      iapply wp_bootR cmd.server1.initialize' cmd.server1.main _ cmd.server1.getIsPkgInit
          net.rpc.codecUnset cmd.server1.wp_boot iprop(srvShare (hG := hG) K 1 ∗ threadTok)
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, Htok⟩, Hcu⟩ HΦ
            iapply (cmd.server1.wp_main EtcdGrove.hraftnet.wp_Server K hb) $$ [Hsh Hcu Htok] HΦ
            iframe Hpkg Hsh Hcu Htok) $$ [HP Htok] Hgs
      iframe Htok
      iapply srvShare_at G' Lexts Lheap Lgs Lthr Lcr K 1 $$ HP
    | 7, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs Htok
      iapply wp_bootR cmd.server2.initialize' cmd.server2.main _ cmd.server2.getIsPkgInit
          net.rpc.codecUnset cmd.server2.wp_boot iprop(srvShare (hG := hG) K 2 ∗ threadTok)
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, Htok⟩, Hcu⟩ HΦ
            iapply (cmd.server2.wp_main EtcdGrove.hraftnet.wp_Server K hb) $$ [Hsh Hcu Htok] HΦ
            iframe Hpkg Hsh Hcu Htok) $$ [HP Htok] Hgs
      iframe Htok
      iapply srvShare_at G' Lexts Lheap Lgs Lthr Lcr K 2 $$ HP
    | 8, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs Htok
      iapply wp_bootR cmd.server3.initialize' cmd.server3.main _ cmd.server3.getIsPkgInit
          net.rpc.codecUnset cmd.server3.wp_boot iprop(srvShare (hG := hG) K 3 ∗ threadTok)
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, Htok⟩, Hcu⟩ HΦ
            iapply (cmd.server3.wp_main EtcdGrove.hraftnet.wp_Server K hb) $$ [Hsh Hcu Htok] HΦ
            iframe Hpkg Hsh Hcu Htok) $$ [HP Htok] Hgs
      iframe Htok
      iapply srvShare_at G' Lexts Lheap Lgs Lthr Lcr K 3 $$ HP
    | 9, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs Htok
      iapply wp_bootR cmd.server4.initialize' cmd.server4.main _ cmd.server4.getIsPkgInit
          net.rpc.codecUnset cmd.server4.wp_boot iprop(srvShare (hG := hG) K 4 ∗ threadTok)
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, Htok⟩, Hcu⟩ HΦ
            iapply (cmd.server4.wp_main EtcdGrove.hraftnet.wp_Server K hb) $$ [Hsh Hcu Htok] HΦ
            iframe Hpkg Hsh Hcu Htok) $$ [HP Htok] Hgs
      iframe Htok
      iapply srvShare_at G' Lexts Lheap Lgs Lthr Lcr K 4 $$ HP
    | 10, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs Htok
      iapply wp_bootR cmd.server5.initialize' cmd.server5.main _ cmd.server5.getIsPkgInit
          net.rpc.codecUnset cmd.server5.wp_boot iprop(srvShare (hG := hG) K 5 ∗ threadTok)
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, Htok⟩, Hcu⟩ HΦ
            iapply (cmd.server5.wp_main EtcdGrove.hraftnet.wp_Server K hb) $$ [Hsh Hcu Htok] HΦ
            iframe Hpkg Hsh Hcu Htok) $$ [HP Htok] Hgs
      iframe Htok
      iapply srvShare_at G' Lexts Lheap Lgs Lthr Lcr K 5 $$ HP
    | 11, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro HP Hgs Htok
      iapply wp_bootR cmd.server6.initialize' cmd.server6.main _ cmd.server6.getIsPkgInit
          net.rpc.codecUnset cmd.server6.wp_boot iprop(srvShare (hG := hG) K 6 ∗ threadTok)
          (by
            iintro %Φ ⟨#Hpkg, ⟨Hsh, Htok⟩, Hcu⟩ HΦ
            iapply (cmd.server6.wp_main EtcdGrove.hraftnet.wp_Server K hb) $$ [Hsh Hcu Htok] HΦ
            iframe Hpkg Hsh Hcu Htok) $$ [HP Htok] Hgs
      iframe Htok
      iapply srvShare_at G' Lexts Lheap Lgs Lthr Lcr K 6 $$ HP
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
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hs6]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexact Hs6
    iapply BigSepL.bigSepL_nil.2
    iempintro

#print axioms hraft_nocrash_robust

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
