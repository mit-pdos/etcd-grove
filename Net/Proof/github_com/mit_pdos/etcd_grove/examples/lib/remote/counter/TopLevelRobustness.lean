/-
The proof of `counter_remote_robust.spec` (`Net/Spec/.../lib/remote/counter/TopLevelRobustness.lean`):
`remote_robustRB` at the ghost bundle `remoteGF` (porcupine's non-atomic invariants), whose
obligation gets the registry, the slot map, the addresses' protocols for a store of its choice, and
the receipt bound. The start: a ghost variable `γs` at the counter's initial value (half to node 0's
invariant as the store's state, half to the server), the three addresses' protocols for `cR γs`,
node 0's invariant (`pend_alloc`) and lintest's state at the model's start. The shares: the
orchestrator gets the client addresses, the slot map, the invariant and lintest's state; each client
node its address, the server's, the slot map and the read's update with no result (`readNoop`); the
server its address and its half of `γs`. Each machine's boot program is its command's initializer
then its `main` (`wp_boot`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.TopLevelRobustness
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Linked
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Robust
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.orch.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client0.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client1.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.orch.Init
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client0.Init
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client1.Init
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open github_com.mit_pdos.etcd_grove.examples.lib.remote EtcdGrove

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section boot
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A command's boot program, from its initializer's spec (with the program's package table
`getIs`) and a spec of its `main` with precondition `P` (echo's `wp_boot`). -/
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

end boot

/-- **remote's counter instance, closed** (see the statement's file). -/
theorem counter_remote_robust : counter_remote_robust.spec := by
  intro gctx lctx sem osem c0sem c1sem ssem fsem bvi σo σ0 σ1 σs g threads
  refine remote_robustRB (GF := remoteGF) (St := w64) (I := Bool) (O := w64) counterAddrs
    (system σo σ0 σ1 σs) g threads (2 ^ 63) ?_
  intro G π ρ hrb
  iintro #Hreg #Hmap Hset
  imod ghostVar_alloc (GF := remoteGF) (W64 0) with ⟨%γs, Hv⟩
  icases (ghostVar_split_half γs 1 (W64 0)).mp $$ Hv with ⟨Hv1, Hv2⟩
  imod Hset $$ %(cR (GF := remoteGF) γs) with Has
  unfold counterAddrs
  icases BigSepL.bigSepL_cons.1 $$ Has with ⟨#Ha0, Has⟩
  icases BigSepL.bigSepL_cons.1 $$ Has with ⟨#Ha1, Has⟩
  icases BigSepL.bigSepL_cons.1 $$ Has with ⟨#Hsa, -⟩
  have hinit : (cS (GF := remoteGF)).M.init = linkv.pInit (cR (GF := remoteGF) γs).B := rfl
  have hv : ghostVar γs (1 : Qp).half (W64 0) ⊢
      (cR (GF := remoteGF) γs).sysState (cR (GF := remoteGF) γs).B.init := by
    simp only [cR, cB]; exact .rfl
  ihave Hv1 := hv $$ Hv1
  imod pend_alloc (Gg := G) (cR (GF := remoteGF) γs) ⊤ cS hinit $$ Hv1 with ⟨%γp, #Hpend, Hlib⟩
  ihave #Hrd : □ (∀ i : Bool, ⌜cB.isWrite i = false⌝ -∗
      lin (Gg := G) (cR (GF := remoteGF) γs) i (fun _ => iprop(True))) $$ []
  · iintro !> %i %hw
    iapply readNoop (Gg := G) (cR (GF := remoteGF) γs) pendN_syncN cS γp i hw $$ Hpend
  ihave #HC : iprop(
      remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7302" ∗
      remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7303" ∗
      remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7301" ∗
      mapCtx (Gg := G) (I := Bool) ∗
      pendCtx (Gg := G) (cR (GF := remoteGF) γs) (cS (GF := remoteGF)) γp ∗
      □ (∀ i : Bool, ⌜cB.isWrite i = false⌝ -∗
        lin (Gg := G) (cR (GF := remoteGF) γs) i (fun _ => iprop(True)))) $$ []
  · iframe #
  imodintro
  iexists fun i => if i = 0 then iprop((remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7302" ∗
      remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7303" ∗
      remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7301" ∗
      mapCtx (Gg := G) (I := Bool) ∗
      pendCtx (Gg := G) (cR (GF := remoteGF) γs) (cS (GF := remoteGF)) γp ∗
      □ (∀ i : Bool, ⌜cB.isWrite i = false⌝ -∗
        lin (Gg := G) (cR (GF := remoteGF) γs) i (fun _ => iprop(True)))) ∗
      pendLib (Gg := G) (cS (GF := remoteGF)) γp (cS (GF := remoteGF)).M.init)
    else if i = 3 then iprop((remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7302" ∗
      remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7303" ∗
      remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7301" ∗
      mapCtx (Gg := G) (I := Bool) ∗
      pendCtx (Gg := G) (cR (GF := remoteGF) γs) (cS (GF := remoteGF)) γp ∗
      □ (∀ i : Bool, ⌜cB.isWrite i = false⌝ -∗
        lin (Gg := G) (cR (GF := remoteGF) γs) i (fun _ => iprop(True)))) ∗
      ghostVar γs (1 : Qp).half (W64 0))
    else iprop(remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7302" ∗
      remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7303" ∗
      remoteAddr (Gg := G) (cR (GF := remoteGF) γs) go!"127.0.0.1:7301" ∗
      mapCtx (Gg := G) (I := Bool) ∗
      pendCtx (Gg := G) (cR (GF := remoteGF) γs) (cS (GF := remoteGF)) γp ∗
      □ (∀ i : Bool, ⌜cB.isWrite i = false⌝ -∗
        lin (Gg := G) (cR (GF := remoteGF) γs) i (fun _ => iprop(True))))
  isplitr
  · ipureintro
    intro i m hm hG hGG hctx
    obtain ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    dsimp only at hGG hctx
    subst hGG hctx
    letI hG : HeapGS .hasLC remoteGF := ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    match i, hm with
    | 0, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨⟨#H0, #H1, #Hs, #Hm, #Hp, #Hr⟩, Hl⟩ Hgs
      iapply wp_boot cmd.orch.initialize' cmd.orch.main _ cmd.orch.getIsPkgInit
          (cmd.orch.wp_initialize' _ cmd.orch.getIsPkgInit_wf) _
          (cmd.orch.wp_main wp_Orch γs γp hrb) $$ [Hl] Hgs
      iframe #
      iframe Hl
    | 1, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#H0, #H1, #Hs, #Hm, #Hp, #Hr⟩ Hgs
      iapply wp_boot cmd.client0.initialize' cmd.client0.main _ cmd.client0.getIsPkgInit
          (cmd.client0.wp_initialize' _ cmd.client0.getIsPkgInit_wf) _
          (cmd.client0.wp_main wp_Client γs) $$ [] Hgs
      iframe #
    | 2, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨#H0, #H1, #Hs, #Hm, #Hp, #Hr⟩ Hgs
      iapply wp_boot cmd.client1.initialize' cmd.client1.main _ cmd.client1.getIsPkgInit
          (cmd.client1.wp_initialize' _ cmd.client1.getIsPkgInit_wf) _
          (cmd.client1.wp_main wp_Client γs) $$ [] Hgs
      iframe #
    | 3, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨⟨#H0, #H1, #Hs, #Hm, #Hp, #Hr⟩, Hv⟩ Hgs
      iapply wp_boot cmd.server.initialize' cmd.server.main _ cmd.server.getIsPkgInit
          (cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf) _
          (cmd.server.wp_main wp_Server γs) $$ [Hv] Hgs
      iframe #
      iframe Hv
  · simp only [system]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hlib]
    · simp only [↓reduceIte]
      iframe #
      iframe Hlib
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · simp only [Nat.zero_add, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hv2]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hv2
    iapply BigSepL.bigSepL_nil.2
    iempintro

#print axioms counter_remote_robust

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
