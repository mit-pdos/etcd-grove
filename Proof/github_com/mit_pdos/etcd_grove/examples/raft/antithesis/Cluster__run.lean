/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__run.lean`, over its callees'
specs: `n.start()` (the node drained by `boot`, so its cause cell `nil`: idle), the ticker made (the
configuration's tick positive), then a loop whose invariant is node `j` between inputs
(`nodeOwn … .idle`, whose `dead` field is `false`: the loop's condition holds), over a `select` of
three cases:
- the stop channel closed (a broadcast): the ticker stopped, `nodesWg.Done()` with the node's right
  to report and its network adders' share (`nodeExit`), return;
- a tick: `n.tick()` (drained by `tick`: idle again);
- an input from `n.in`'s bag (`inputOk`): `c.handle(n, inp)`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__handle
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__start
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__tick
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Perennial.Spec.time.NewTicker
public import Perennial.Spec.time.Ticker__Stop
public import Perennial.Spec.sync.WaitGroup__Done

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- A node goroutine's `dead` field, `false` at every phase (no kill in B1's mask), taken out and
put back. -/
theorem nodeOwn_dead (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (ph : Phase) :
    nodeOwn (GF := GF) c γ j n v ph ⊢
      n.[H.node, go!"dead"] ↦ false ∗ (n.[H.node, go!"dead"] ↦ false -∗ nodeOwn c γ j n v ph) := by
  unfold nodeOwn nodeMemB1 emitOk
  iintro ⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, #Hd,
    ⟨%mhs, %rhs, Hit, Hmhs, Hrhs, Hwr, Hinf, Happs, Happl, Hres, Hwip, Haip, Hcfs, Hcb, Hdead, Hfuse⟩,
    Hrest⟩
  iframe Hdead
  iintro Hdead
  iexists d, rn, ms, hsl, cl, csl, role, applied
  iframe Hd Hrest
  iexists mhs, rhs
  iframe

/-- A node goroutine's right to report, out of its state (at the stop: `nodeExit`). -/
theorem nodeOwn_live (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (ph : Phase) :
    nodeOwn (GF := GF) c γ j n v ph ⊢ nodeLive γ j := by
  unfold nodeOwn
  iintro ⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, -, -, -, -, -, -, -, -, -, -, Hl, -⟩
  iexact Hl

theorem Cluster.run.wp_proof
    (wp_NewTicker : time.NewTicker.spec (GF := GF) (hG := hG))
    (wp_TStop : time.Ticker.Stop.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (wp_start : node.start.spec (GF := GF) (hG := hG))
    (wp_tick : node.tick.spec (GF := GF) (hG := hG))
    (wp_handle : Cluster.handle.spec (GF := GF) (hG := hG)) :
    Cluster.run.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v q
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok, Hdone, %Hb1⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  ihave #Hn' := Hn
  iunfold nodeRO at Hn'
  icases Hn' with ⟨%ch, %d, #Hnc, #Hid, #Hname, #Hin, #Hbag, #Hd, #Hlog⟩
  ihave #Hsch := ownBroadcastChan_is_chan _ _ _ _ $$ Hbc
  ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hcf := Hcfg
  iStructNamed Hcf
  wp_auto
  wp_apply wp_start c γ n j v q $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as %v0 ⟨Hown, Had, Htok, %Hby⟩
  · ipureintro; exact Hb1
  ihave Hown := nodeOwn_drained_idle c γ j n v0 (by rw [Hby]; decide) $$ Hown
  (try wp_auto)
  wp_apply wp_NewTicker as %t %tch %γt #Ht
  · ipureintro; exact Hcok
  ihave #Ht' := Ht
  iunfold time.isTicker at Ht'
  icases Ht' with ⟨#HtC, #HtI, #HtR, #Htbag⟩
  (try wp_auto)
  ihave IH : iprop(∃ v : AntSim.NodeView, nodeOwn c γ j n v .idle ∗ netAdder c γ q ∗ threadTok ∗
      sync.join.ownDone (c.[H.Cluster, go!"nodesWg"]) (nodeExit c γ j q)) $$ [Hown Had Htok Hdone]
  · iexists v0; iframe Hown Had Htok Hdone
  wp_for_core
  icases IH with ⟨%v, Hown, Had, Htok, Hdone⟩
  icases nodeOwn_dead c γ j n v .idle $$ Hown with ⟨Hdead, Hown⟩
  wp_auto_lc 1
  irename Hlc1 => Hlc0
  cleanup_bool_decide
  wp_auto_lc 1
  irename Hlc0 => Hlc2
  ihave Hown := Hown $$ Hdead
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the run stops
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stop, γ.stopCh
    isplit
    · ipureintro; rfl
    isplit
    · iexact Hsch
    iapply broadcast_chan_receive $$ Hbc
    iintro -
    (try wp_auto)
    wp_apply wp_TStop t $$ []
    · iexists tch, γt; iexact Ht
    (try wp_auto)
    ihave Hl := nodeOwn_live c γ j n v .idle $$ Hown
    wp_apply (sync.join.WaitGroup.wp_Done_of wp_Done (nodeExit c γ j q) _) $$ [$Hsync $Hdone Hl Had]
    · iunfold nodeExit; iframe Hl Had
    (try wp_auto)
    wp_for_post
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a tick
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htbag
    inext
    iintro %tm0 -
    (try wp_auto)
    wp_apply wp_tick c γ n j v q $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as %v' ⟨Hown, Had, Htok, %Hby'⟩
    · ipureintro; exact Hb1
    ihave Hown := nodeOwn_drained_idle c γ j n v' (by rw [Hby']; decide) $$ Hown
    ihave IH : iprop(∃ v : AntSim.NodeView, nodeOwn c γ j n v .idle ∗ netAdder c γ q ∗ threadTok ∗
        sync.join.ownDone (c.[H.Cluster, go!"nodesWg"]) (nodeExit c γ j q)) $$ [Hown Had Htok Hdone]
    · iexists v'; iframe Hown Had Htok Hdone
    (try wp_auto)
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- an input
    simp only [chan.blockingClausePre]
    iexists H.input, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ.inCh j
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %inp Hinp
    (try wp_auto)
    wp_apply wp_handle c γ n j v inp q $$ [$Hpkg $Hc $Hn $Hown $Hinp $Had $Htok] as %v' ⟨Hown, Had, Htok⟩
    · ipureintro; exact Hb1
    ihave IH : iprop(∃ v : AntSim.NodeView, nodeOwn c γ j n v .idle ∗ netAdder c γ q ∗ threadTok ∗
        sync.join.ownDone (c.[H.Cluster, go!"nodesWg"]) (nodeExit c γ j q)) $$ [Hown Had Htok Hdone]
    · iexists v'; iframe Hown Had Htok Hdone
    (try wp_auto)
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end AntHarness
end EtcdGrove
end Perennial
