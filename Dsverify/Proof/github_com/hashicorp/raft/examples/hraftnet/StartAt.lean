/-
**The start's shares at every machine** (notes/dsv-hraft.md, "The top level"). The shares of the start
(`orchShare`, `cliShare`, `srvShare`, `Start.lean`) are stated, as the kit's specs are, at a `HeapGS`,
which a machine has and the deployment's start does not: the start has the global ghost state `G`
only. They mention only `G` (the protocol's ghost state is global), so the start runs at a heap of
its own, `atStart G` (`G` with some local ghost names, `anyLocal`: never a machine's, and nothing of
it is used), and each machine takes its share at its own heap over the same `G` by the lemmas below,
which hold by unfolding (`with_unfolding_all rfl`: `Inv`, `srvOwn`, ... of `gprot` are irreducible).
The orchestrator's share is converted conjunct by conjunct: unfolding all of it would unfold
`budUnits a orchBud`, a recursion `3 * 2 ^ 20` deep.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Start
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section startAt
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- Some local ghost state over `G` (its names arbitrary; its Go context `lctx`): the start's heap's. -/
@[reducible] def anyLocal (lctx : GoLocalContext) (G : GooseGlobalGS .hasLC GF) : GooseLocalGS GF :=
  ⟨((⟨G.gooseAllG, default, default⟩ : NetLocalGS GF), ⟨⟩), lctx,
    ⟨hPre.goose_preG_heap.na_heap_preG_inG, default⟩,
    goStateGSUpdatePre GF hPre.goose_preG_go_state G.gooseAllG default default,
    ⟨default, 2, by decide⟩, ⟨default⟩⟩

/-- The start's heap: `G` and `anyLocal lctx G`. -/
@[reducible] def atStart (lctx : GoLocalContext) (G : GooseGlobalGS .hasLC GF) : HeapGS .hasLC GF :=
  ⟨G, anyLocal lctx G⟩

variable [lctx : GoLocalContext] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable (G : GooseGlobalGS .hasLC GF) (Lexts : Exts.LocalGS _ GooseInterp.interps GF)
  (Lheap : NaHeapGS Loc val GF) (Lgs : GoStateGS GF) (Lthr : ThreadGS GF) (Lcr : CrashGS GF)

theorem srvShare_at (K : HK GF) (j : Nat) :
    srvShare (hG := atStart lctx G) K j ⊢
      srvShare (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K j := by
  with_unfolding_all exact .rfl

theorem cliShare_at [ρ : RemoteGS] (K : HK GF) (c : Nat) :
    cliShare (hG := atStart lctx G) K c ⊢
      cliShare (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K c := by
  with_unfolding_all exact .rfl

theorem drawInv_at (K : HK GF) :
    drawInv (hG := atStart lctx G) K ⊢ drawInv (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K := by
  with_unfolding_all exact .rfl

theorem drawPre_at (K : HK GF) :
    drawPre (hG := atStart lctx G) K ⊢ drawPre (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K := by
  with_unfolding_all exact .rfl

theorem kitSS_at (K : HK GF) :
    kitSS (hG := atStart lctx G) K → kitSS (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K := by
  with_unfolding_all exact id

theorem drawTok_at (K : HK GF) : drawTok (hG := atStart lctx G) K ⊢ drawTok (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K := by
  with_unfolding_all exact .rfl

/-- Remote's pending library reads its model spec `S` only through its model `S.M` (`regS`'s
representation predicate, a heap's, differs between the heaps; its model does not). -/
theorem regS_M_at : (regS (hG := atStart lctx G)).M = (regS (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩)).M := rfl

theorem pendCtx_at (st : GName) (γp : PendNames) :
    pendCtx (Gg := G) (regR (Gg := G) st) (regS (hG := atStart lctx G)) γp ⊢
      pendCtx (Gg := G) (regR (Gg := G) st) (regS (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩)) γp := by
  unfold pendCtx pendBody
  rw [regS_M_at G Lexts Lheap Lgs Lthr Lcr]

theorem pendLib_at (γp : PendNames) :
    pendLib (Gg := G) (regS (hG := atStart lctx G)) γp (regS (hG := atStart lctx G)).M.init ⊢
      pendLib (Gg := G) (regS (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩)) γp (regS (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩)).M.init := by
  unfold pendLib
  rw [regS_M_at G Lexts Lheap Lgs Lthr Lcr]

theorem orchShare_at [ρ : RemoteGS] (K : HK GF) (γp : PendNames) :
    orchShare (hG := atStart lctx G) K γp ⊢
      orchShare (hG := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩) K γp := by
  iintro H
  unfold orchShare
  icases H with ⟨#Hcp, #Hra, %Hss, #Hdi, Htok, Hpre, #Hrem, #Hmap, #Hpend, Hlib, Hbud⟩
  ihave #Hdi' := drawInv_at G Lexts Lheap Lgs Lthr Lcr K $$ Hdi
  ihave Hpre' := drawPre_at G Lexts Lheap Lgs Lthr Lcr K $$ Hpre
  ihave Htok' := drawTok_at G Lexts Lheap Lgs Lthr Lcr K $$ Htok
  ihave #Hpend' := pendCtx_at G Lexts Lheap Lgs Lthr Lcr K.g.st γp $$ Hpend
  ihave Hlib' := pendLib_at G Lexts Lheap Lgs Lthr Lcr γp $$ Hlib
  isplitr; · iexact Hcp
  isplitr; · iexact Hra
  isplitr; · ipureintro; exact ⟨kitSS_at G Lexts Lheap Lgs Lthr Lcr K Hss.1, Hss.2⟩
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
