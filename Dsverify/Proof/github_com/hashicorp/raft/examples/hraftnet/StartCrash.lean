/-
**The crash deployment's start** (hraft_robust R7; notes/dsv-hraft.md, "hraft_robust"): the no-crash
deployment's start (`hraft_start`, `Start.lean`, its shares unchanged) over the net and file extensions
(`kvraftExts`), and the conversions of its shares to each machine's heap. As `StartAt.lean` for
`netExts`: the start runs at a heap of its own, `atStartFs lctx G` (`G` with some local ghost names,
`anyLocalFs`, over `[netExt, fsExt]`), and each machine takes its share at its own heap over the same
`G` (`*_atFs`, by unfolding). Also: the restartable servers' boot programs (`rserverBoots`, the
statement's `crashServers`' programs) and the addresses' facts (`hraftKitAddrs_nodup`,
`hraftKitAddrs_ok`), checked by evaluation in the kernel.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Start
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.TopLevelCrashDefs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net NetFs

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] kvraftExts kvraftExtsSemantics kvraftExtsInterp kvraftExts_hasNet
  kvraftExts_hasFs GooseGlobalGS.gooseInvGS

section programs
variable [GoGlobalContext]

/-- The restartable servers' boot programs, server 1 first (`crashServers`' programs). -/
def rserverBoots : List Expr :=
  [bootFs cmd.rserver1.initialize' cmd.rserver1.main, bootFs cmd.rserver2.initialize' cmd.rserver2.main,
   bootFs cmd.rserver3.initialize' cmd.rserver3.main, bootFs cmd.rserver4.initialize' cmd.rserver4.main,
   bootFs cmd.rserver5.initialize' cmd.rserver5.main, bootFs cmd.rserver6.initialize' cmd.rserver6.main]

theorem crashServers_fst (σ : Nat → state) : (crashServers σ).map Prod.fst = rserverBoots := rfl

theorem crashServers_boot (σ : Nat → state) (i : Nat) (m : Expr × state)
    (hm : (crashServers σ)[i]? = some m) : rserverBoots[i]? = some m.1 := by
  rw [← crashServers_fst σ, List.getElem?_map, hm]; rfl

end programs

theorem hraftKitAddrs_nodup : hraftKitAddrs.Nodup := by
  unfold hraftKitAddrs; decide +kernel

theorem hraftKitAddrs_ok [GooseExts] : ∀ a ∈ hraftKitAddrs, addrOk a = true := by
  unfold hraftKitAddrs; decide +kernel

section startAt
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- Some local ghost state over `G` for `[netExt, fsExt]` (its names arbitrary; its Go context
`lctx`): the start's heap's. -/
@[reducible] def anyLocalFs (lctx : GoLocalContext) (G : GooseGlobalGS .hasLC GF) : GooseLocalGS GF :=
  ⟨((⟨G.gooseAllG, default, default⟩ : NetLocalGS GF),
      ((⟨G.gooseAllG, default, default, default, default, default, default, default, default, default,
        default, default, default, default, default, default, default⟩ : Fs.OsGS GF), ⟨⟩)), lctx,
    ⟨hPre.goose_preG_heap.na_heap_preG_inG, default⟩,
    goStateGSUpdatePre GF hPre.goose_preG_go_state G.gooseAllG default default,
    ⟨default, 2, by decide⟩, ⟨default⟩⟩

/-- The start's heap: `G` and `anyLocalFs lctx G`. -/
@[reducible] def atStartFs (lctx : GoLocalContext) (G : GooseGlobalGS .hasLC GF) :
    HeapGS .hasLC GF :=
  ⟨G, anyLocalFs lctx G⟩

variable [lctx : GoLocalContext] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable (G : GooseGlobalGS .hasLC GF) (Lexts : Exts.LocalGS _ GooseInterp.interps GF)
  (Lheap : NaHeapGS Loc val GF) (Lgs : GoStateGS GF) (Lthr : ThreadGS GF) (Lcr : CrashGS GF)

theorem srvShare_atFs (K : HK GF) (j : Nat) :
    srvShare (hG := atStartFs lctx G) K j ⊢
      srvShare (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K j := by
  with_unfolding_all exact .rfl

theorem cliShare_atFs [ρ : RemoteGS] (K : HK GF) (c : Nat) :
    cliShare (hG := atStartFs lctx G) K c ⊢
      cliShare (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K c := by
  with_unfolding_all exact .rfl

theorem drawInv_atFs (K : HK GF) :
    drawInv (hG := atStartFs lctx G) K ⊢ drawInv (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K := by
  with_unfolding_all exact .rfl

theorem drawPre_atFs (K : HK GF) :
    drawPre (hG := atStartFs lctx G) K ⊢ drawPre (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K := by
  with_unfolding_all exact .rfl

theorem kitSS_atFs (K : HK GF) :
    kitSS (hG := atStartFs lctx G) K → kitSS (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K := by
  with_unfolding_all exact id

theorem drawTok_atFs (K : HK GF) : drawTok (hG := atStartFs lctx G) K ⊢ drawTok (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K := by
  with_unfolding_all exact .rfl

/-- Remote's pending library reads its model spec `S` only through its model `S.M` (`regS`'s
representation predicate, a heap's, differs between the heaps; its model does not). -/
theorem regS_M_atFs : (regS (hG := atStartFs lctx G)).M = (regS (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩)).M := rfl

theorem pendCtx_atFs (st : GName) (γp : PendNames) :
    pendCtx (Gg := G) (regR (Gg := G) st) (regS (hG := atStartFs lctx G)) γp ⊢
      pendCtx (Gg := G) (regR (Gg := G) st) (regS (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩)) γp := by
  unfold pendCtx pendBody
  rw [regS_M_atFs G Lexts Lheap Lgs Lthr Lcr]

theorem pendLib_atFs (γp : PendNames) :
    pendLib (Gg := G) (regS (hG := atStartFs lctx G)) γp (regS (hG := atStartFs lctx G)).M.init ⊢
      pendLib (Gg := G) (regS (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩)) γp (regS (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩)).M.init := by
  unfold pendLib
  rw [regS_M_atFs G Lexts Lheap Lgs Lthr Lcr]

theorem orchShare_atFs [ρ : RemoteGS] (K : HK GF) (γp : PendNames) :
    orchShare (hG := atStartFs lctx G) K γp ⊢
      orchShare (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K γp := by
  iintro H
  unfold orchShare
  icases H with ⟨#Hcp, #Hra, %Hss, #Hdi, Htok, Hpre, #Hrem, #Hmap, #Hpend, Hlib, Hbud⟩
  ihave #Hdi' := drawInv_atFs G Lexts Lheap Lgs Lthr Lcr K $$ Hdi
  ihave Hpre' := drawPre_atFs G Lexts Lheap Lgs Lthr Lcr K $$ Hpre
  ihave Htok' := drawTok_atFs G Lexts Lheap Lgs Lthr Lcr K $$ Htok
  ihave #Hpend' := pendCtx_atFs G Lexts Lheap Lgs Lthr Lcr K.g.st γp $$ Hpend
  ihave Hlib' := pendLib_atFs G Lexts Lheap Lgs Lthr Lcr γp $$ Hlib
  isplitr; · iexact Hcp
  isplitr; · iexact Hra
  isplitr; · ipureintro; exact ⟨kitSS_atFs G Lexts Lheap Lgs Lthr Lcr K Hss.1, Hss.2⟩
  isplitr; · iexact Hdi'
  isplitl [Htok']; · iexact Htok'
  isplitl [Hpre']; · iexact Hpre'
  isplitr; · iexact Hrem
  isplitr; · iexact Hmap
  isplitr; · iexact Hpend'
  isplitl [Hlib']; · iexact Hlib'
  iexact Hbud

end startAt

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
