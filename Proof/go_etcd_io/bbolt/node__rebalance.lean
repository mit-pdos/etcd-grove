/-
`node.rebalance` (bbolt, internal to U8b, `notes/bbolt-proof-plan.md`): its spec and proof. Its
only caller is `Bucket.rebalance` (and itself, `n.parent.rebalance()`), so the spec is U8b's own:
over `rebalance`'s invariant `rblX` (`Rebalance/RblX.lean`) with at most one deficient node, the
one being rebalanced.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSteps
public import Spec.go_etcd_io.bbolt.node__size
public import Spec.go_etcd_io.bbolt.node__numChildren
public import Spec.go_etcd_io.bbolt.node__childIndex
public import Spec.go_etcd_io.bbolt.node__nextSibling
public import Spec.go_etcd_io.bbolt.node__prevSibling
public import Spec.go_etcd_io.bbolt.node__del
public import Spec.go_etcd_io.bbolt.node__removeChild
public import Spec.go_etcd_io.bbolt.node__free
public import Spec.go_etcd_io.bbolt.Bucket__node
public import Spec.go_etcd_io.bbolt.TxStats__IncRebalance
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Pgid
public import Proof.go_etcd_io.bbolt.Rebalance.NodeRblBase
public import Proof.go_etcd_io.bbolt.Inv.WtxBase
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSMat
public import Proof.go_etcd_io.bbolt.Rebalance.RblXMg
public import Proof.go_etcd_io.bbolt.Rebalance.BktRbl
public import Proof.go_etcd_io.bbolt.Inv.MatReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- What `n.rebalance()` did to the buckets: the other buckets' records unchanged; in `bl`, the
unbalanced nodes after are some of those before (the same page ids), not `n`. -/
def rblStepX (X X' : WX) (bl n : Loc) : Prop :=
  (∀ bl', bl' ≠ bl → X'.t.bs !! bl' = X.t.bs !! bl') ∧
  ∀ B B', X.t.bs !! bl = some B → X'.t.bs !! bl = some B' → rblStep B B' n

/-- **`n.rebalance()`** of a node `n` of bucket `bl`: from `rebalance`'s invariant with `n` the
deficient node (if any, then marked unbalanced), to the invariant with none; the steps' frees
(`Free` steps for the writer's txid, `rblRel`), `n` no longer unbalanced and no node newly so
(`rblStepX`). -/
def node.rebalance.spec' : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl : Loc) (B : BRec) (n : Loc)
    (rn : NRec) (dfc : Option Loc),
  rblX X w.fl bl dfc → X.t.bs !! bl = some B → B.ns !! n = some rn →
  (dfc = none ∨ (dfc = some n ∧ rn.nv.unbalanced' = true)) → (bl = X.rl ∨ (X.handles !! bl).isSome) →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"rebalance")) (Val #()))
  {{ RET #(); ∃ (X' : WX) (fl' : FLPg), wtxW K tx r m X' ∗ wdbW K tx X.v (w.withFl fl') ∗
      ⌜rblX X' fl' bl none ∧ rblRel X w.fl X' fl' X.t.mv.txid' ∧ rblStepX X X' bl n⌝ }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `node.rebalance.spec'`, as an Iris proposition (for the recursion, Löb). -/
def rebalW : IProp GF :=
  iprop(∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl : Loc) (B : BRec)
    (n : Loc) (rn : NRec) (dfc : Option Loc),
  ⌜rblX X w.fl bl dfc ∧ X.t.bs !! bl = some B ∧ B.ns !! n = some rn ∧
    (dfc = none ∨ (dfc = some n ∧ rn.nv.unbalanced' = true)) ∧ (bl = X.rl ∨ (X.handles !! bl).isSome)⌝ →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"rebalance")) (Val #()))
  {{ RET #(); ∃ (X' : WX) (fl' : FLPg), wtxW K tx r m X' ∗ wdbW K tx X.v (w.withFl fl') ∗
      ⌜rblX X' fl' bl none ∧ rblRel X w.fl X' fl' X.t.mv.txid' ∧ rblStepX X X' bl n⌝ }})

/-- `n.minKeys()`: `1` for a leaf, `2` for a branch (its body, inlined). -/
theorem node_minKeys_wp (n : Loc) (b : Bool) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n.[node, go!"isLeaf"] ↦{dq} b }}
      (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"minKeys")) (Val #()))
    {{ RET #(if b then W64 1 else W64 2); n.[node, go!"isLeaf"] ↦{dq} b }} := by
  wp_start as Hl
  wp_auto
  cases b <;> (try wp_auto) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iapply HΦ <;> iframe

set_option maxHeartbeats 3000000 in
theorem rebal_loeb
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hNum : node.numChildren.spec (GF := GF) (hG := hG))
    (hIdx : node.childIndex.spec (GF := GF) (hG := hG))
    (hNext : node.nextSibling.spec (GF := GF) (hG := hG))
    (hPrev : node.prevSibling.spec (GF := GF) (hG := hG))
    (hDel : node.del.spec (GF := GF) (hG := hG))
    (hRm : node.removeChild.spec (GF := GF) (hG := hG))
    (hFree : node.free.spec (GF := GF) (hG := hG))
    (hNode : Bucket.node.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncRebalance.spec (GF := GF) (hG := hG))
    (hAssert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hPg : internal.common.Inode.Pgid.spec (GF := GF) (hG := hG)) :
    ⊢ rebalW (GF := GF) := by
  iloeb as IH
  unfold rebalW
  iintro %K %tx %r %m %X %w %bl %B %n %rn %dfc %Hpre
  obtain ⟨hI, hb, hrn, hdfc, hfp⟩ := Hpre
  wp_start as ⟨Hw, Hdb⟩
  icases (wtxW_split K tx r m X).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
  unfold wtxCore
  icases Hc with ⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  have Ho := objs_node X.t bl B n rn Hok.2.1 hb hrn
  icases wtxHeap_node_ptr_acc tx (DFrac.own 1) X bl n rn Ho $$ Hh with ⟨Hn, Hback⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  have hnl : n ∈ X.live := (hI.2.1 bl B hb).2.2.2.2 n rn hrn
  have hbll : bl ∈ X.liveB := hI.2.2.2.2.1.2.2.1 bl B hb
  rcases Bool.eq_false_or_eq_true rn.nv.unbalanced' with hu | hu0
  rotate_left
  · -- balanced: nothing
    rw [hu0]
    wp_auto
    have hd : dfc = none := by
      rcases hdfc with h | ⟨-, h⟩
      · exact h
      · rw [hu0] at h; cases h
    subst hd
    ihave Hn : (n ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]; rw [hu0]
      iframe
    ihave Hh := Hback $$ Hn
    ihave Hw : wtxW K tx r m X $$ [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
    · iapply (wtxW_split K tx r m X).2; unfold wtxCore; iframe; iframe #; ipureintro; exact Hr
    iapply HΦ
    iexists X, w.fl
    rw [show w.withFl w.fl = w from rfl]
    iframe
    ipureintro
    refine ⟨hI, rblRel_refl X w.fl _, fun _ _ => rfl, fun B1 B2 h1 h2 => ?_⟩
    rw [hb] at h1 h2; cases h1; cases h2
    refine ⟨rfl, rfl, rfl, fun l r' hl hu' => ⟨?_, r', hl, hu', rfl⟩⟩
    rintro rfl; rw [hrn] at hl; cases hl; rw [hu0] at hu'; cases hu'
  rw [hu]
  ihave Hn : (n ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]; rw [hu]
    iframe
  ihave Hh := Hback $$ Hn
  have hnc := (hI.2.1 bl B hb).1.1.2.2.2.2.2.2.2.1 n rn hrn
  have hbtx : B.bv.tx' = tx := Hok.2.2.1 bl B hb
  icases wtxHeap_setNode_acc tx (DFrac.own 1) X bl B n rn hb hrn $$ Hh
    with ⟨Hno, Hbo, Htf, Hrf, Hback⟩
  rw [decide_eq_true hnl, decide_eq_true hbll]
  ihave Hfp : (∃ f : w64, bl.[Bucket, go!"FillPercent"] ↦ f ∗
      (bl.[Bucket, go!"FillPercent"] ↦ f -∗ rootFill tx (DFrac.own 1) ∗ fills X.handles (DFrac.own 1))
      : IProp GF) $$ [Hrf Hfills]
  · rcases hfp with hroot | hh
    · have hbr : bl = tx.[Tx, go!"root"] := hroot.trans Hok.1
      unfold rootFill
      icases Hrf with ⟨%f, %Hnan, Hf⟩
      iexists f
      rw [hbr]
      iframe Hf
      iintro Hf
      iframe Hfills
      iexists f; iframe Hf; ipureintro; exact Hnan
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hh
      unfold fills
      icases (BigSepM.bigSepM_lookup_acc hx).1 $$ Hfills with ⟨⟨%f, %Hnan, Hf⟩, Hfb⟩
      iexists f
      iframe Hf
      iintro Hf
      iframe Hrf
      iapply Hfb
      iexists f; iframe Hf; ipureintro; exact Hnan
  icases Hfp with ⟨%fp, Hfp, Hfpb⟩
  unfold objOwn
  icases Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
  icases Hbo with ⟨Hb1, Hbtx, Hb3, Hb4, Hb5, Hbnodes, Hib, Hnm, Hbm, Hpo⟩
  ihave Htxf : (∃ dqb : DFrac, bl.[Bucket, go!"tx"] ↦{dqb} tx ∗
      (bl.[Bucket, go!"tx"] ↦{dqb} tx -∗
        if bl = B.bv.tx'.[Tx, go!"root"] then bl.[Bucket, go!"tx"] ↦ B.bv.tx'
        else bl.[Bucket, go!"tx"] ↦□ B.bv.tx') : IProp GF) $$ [Hbtx]
  · rw [hbtx]
    by_cases hroot : bl = tx.[Tx, go!"root"]
    · rw [if_pos hroot]
      iexists DFrac.own 1
      iframe
      iintro H; iexact H
    · rw [if_neg hroot]
      icases Hbtx with #Hbtx
      iexists DFrac.discard
      isplitr
      · iexact Hbtx
      · iintro _; iexact Hbtx
  icases Htxf with ⟨%dqb, Htx, Htxb⟩
  ihave #Hps : (r.db.[DB, go!"pageSize"] ↦□ W64 4096 : IProp GF) $$ [Hcore]
  · rw [Hr.1]; iapply rbl_pageSize K; iexact Hcore
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn'⟩
  iStructNamed Hn
  rw [hnc.1]
  wp_auto
  rw [hbtx]
  wp_apply hInc K tx r m 1 (W64 1) $$ [Hst] as %_ Hst
  · iframe; iframe #
  try wp_auto
  wp_apply wp_ArbitraryInt as %thr _
  ihave Hn : (n ↦ ({ rn.nv with unbalanced' := false } : node) : IProp GF)
    $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn'
    simp only [TypedPointsto.typedPointstoDef]; rw [hnc.1]
    iframe
  wp_apply hSize n ({ rn.nv with unbalanced' := false } : node) rn.ins (DFrac.own 1) (DFrac.own 1)
    $$ [Hn Hins] as ⟨Hn, Hins⟩
  · iframe
  wp_join (v := #(decide (sint.Z (BitVec.sdiv thr (W64 2)) < sint.Z (W64 (insSize rn.ins : Int)) ∧
      sint.Z (if rn.nv.isLeaf' then W64 1 else W64 2) < sint.Z rn.nv.inodes'.len))) at
    (if: #(decide (sint.Z (BitVec.sdiv thr (W64 2)) < sint.Z (W64 (insSize rn.ins : Int)))) then _
      else #false) with [Hn Hins n]
  · wp_if_destruct
    · iStructNamed Hn
      wp_apply node_minKeys_wp n rn.nv.isLeaf' (DFrac.own 1) $$ [isLeaf] as isLeaf
      · iframe
      ihave Hn : (n ↦ ({ rn.nv with unbalanced' := false } : node) : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn'
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      try wp_auto
      iframe
      ipureintro
      simp only [Hif, true_and]
    · rw [decide_eq_false (fun h => Hif h.1)]
      wp_join_done
  -- the heap closed on `X1`: the node no longer unbalanced
  ihave %Hsl := ownSlice_len _ _ _ $$ Hins
  ihave Hbtx := Htxb $$ Htx
  icases Hfpb $$ Hfp with ⟨Hrf, Hfills⟩
  ihave Hh := Hback $$ %(rblClear rn) [] [Hn Hins Hcap Hws Hch Hchcap Hkey]
    [Hb1 Hbtx Hb3 Hb4 Hb5 Hbnodes Hib Hnm Hbm Hpo] [Htf] [Hrf]
  · ipureintro; exact Hok.2.2.2.1 bl B n rn hb hrn
  · simp only [rblClear]; iframe
  · iframe
  · iframe
  · iframe
  have hX1 : X.setNode bl n (rblClear rn) = X.setBkt bl (rblStart B n rn) := by
    unfold WX.setNode; rw [hb]; rfl
  rw [hX1]
  have hdfc' : dfc = none ∨ dfc = some n := by
    rcases hdfc with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨hI1, hR1⟩ := rblX_start X w.fl bl dfc B n rn hI hb hrn hdfc'
  ihave Hw : wtxW K tx r m (X.setBkt bl (rblStart B n rn)) $$
    [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
  · iapply (wtxW_split K tx r m _).2; unfold wtxCore
    simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc, WX.kill_v, WX.kill_handles, WX.kill_nloc, WX.setNode_v, WX.setNode_handles, WX.setNode_nloc]
    iframe; iframe #; ipureintro; exact Hr
  have hlen : rn.ws.length = sint.nat rn.nv.inodes'.len := by rw [← hnc.2.2.1, Hsl.1]
  have hb1 : (X.setBkt bl (rblStart B n rn)).t.bs !! bl = some (rblStart B n rn) :=
    GMap.lookup_insert _ _ _
  have hr1 : (rblStart B n rn).ns !! n = some (rblClear rn) := GMap.lookup_insert _ _ _
  -- the post of a step that only cleared the node (done)
  have hpost : (rn.nv.isLeaf' = false → 2 ≤ rn.ws.length) →
      (rn.nv.isLeaf' = true → rn.nv.parent' ≠ null → 0 < rn.ws.length) →
      rblX (X.setBkt bl (rblStart B n rn)) w.fl bl none ∧
      rblRel X w.fl (X.setBkt bl (rblStart B n rn)) w.fl X.t.mv.txid' ∧
      rblStepX X (X.setBkt bl (rblStart B n rn)) bl n := by
    intro h2 h1
    obtain ⟨hD1, hD2, hD3⟩ := rblX_done X w.fl bl dfc B n rn hI hb hrn hdfc' h2 h1
    refine ⟨hD1, hD2, fun bl' hne => ?_, fun B1 B2 h1' h2' => ?_⟩
    · show (X.t.bs.insert bl _) !! bl' = _; rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]
    · rw [hb] at h1'; cases h1'
      rw [hb1] at h2'; cases h2'; exact hD3
  wp_if_destruct
  · -- big enough: done
    have hmk := Hif.2
    have h2 : rn.nv.isLeaf' = false → 2 ≤ rn.ws.length := by
      intro hl; rw [hl] at hmk; simp only [Bool.false_eq_true, ↓reduceIte] at hmk; rw [hlen]; word
    have h1 : rn.nv.isLeaf' = true → rn.nv.parent' ≠ null → 0 < rn.ws.length := by
      intro hl _; rw [hl] at hmk; simp only [↓reduceIte] at hmk; rw [hlen]; word
    iapply HΦ
    iexists X.setBkt bl (rblStart B n rn), w.fl
    rw [show w.withFl w.fl = w from rfl]
    iframe
    ipureintro
    exact hpost h2 h1
  -- not done
  icases (wtxW_split K tx r m _).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
  unfold wtxCore
  icases Hc with ⟨-, -, -, -, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
  ihave %Hok1 := wtxHeap_heapOK tx (DFrac.own 1) _ $$ Hh
  have Ho1 := objs_node _ bl _ n _ Hok1.2.1 hb1 hr1
  icases wtxHeap_node_ptr_acc tx (DFrac.own 1) _ bl n (rblClear rn) Ho1 $$ Hh with ⟨Hn, Hback⟩
  iStructNamed Hn
  wp_auto
  wp_if_destruct
  · -- the root
    have hpn : rn.nv.parent' = null := Hif
    have hbrlen : rn.nv.isLeaf' = false → 0 < rn.ws.length := fun hl => (hnc.2.2.2.2.2.2.2.2.2.2.2.2.1 hl).1
    rcases Bool.eq_false_or_eq_true rn.nv.isLeaf' with hlf | hlf
    · -- a leaf root: done
      have hlf' : (rblClear rn).nv.isLeaf' = true := hlf
      (try rw [hlf]); (try rw [hlf'])
      wp_auto
      ihave Hn : (n ↦ (rblClear rn).nv : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn'
        simp only [TypedPointsto.typedPointstoDef]; (try rw [hlf]); (try rw [hlf'])
        iframe
      ihave Hh := Hback $$ Hn
      ihave Hw : wtxW K tx r m (X.setBkt bl (rblStart B n rn)) $$
        [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
      · iapply (wtxW_split K tx r m _).2; unfold wtxCore
        simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc, WX.kill_v, WX.kill_handles, WX.kill_nloc, WX.setNode_v, WX.setNode_handles, WX.setNode_nloc]
        iframe; iframe #; ipureintro; exact Hr
      iapply HΦ
      iexists X.setBkt bl (rblStart B n rn), w.fl
      rw [show w.withFl w.fl = w from rfl]
      iframe
      ipureintro
      exact hpost (fun h => by rw [hlf] at h; cases h) (fun _ h => absurd hpn h)
    have hlf' : (rblClear rn).nv.isLeaf' = false := hlf
    (try rw [hlf]); (try rw [hlf'])
    wp_auto
    wp_if_destruct
    · -- the root collapses into its only child
      have hl1 : rn.nv.inodes'.len = W64 1 := Hif
      have hws1 : rn.ws.length = 1 := by rw [hlen, hl1]; rfl
      obtain ⟨w0, hw0⟩ : ∃ w0, rn.ws = [w0] := by
        match h : rn.ws, hws1 with
        | [w0], _ => exact ⟨w0, rfl⟩
      have hw00 : rn.ws[0]? = some w0 := by rw [hw0]; rfl
      have hB1 := (hI1.2.1 bl _ hb1).1
      rw [if_pos rfl] at hB1
      obtain ⟨hc1, ⟨bnd1, hk1⟩, -, -⟩ := hB1
      -- entry 0's page id (`n.inodes[0].Pgid()`)
      ihave Hn : (n ↦ (rblClear rn).nv : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn'
        simp only [TypedPointsto.typedPointstoDef]; (try rw [hlf]); (try rw [hlf'])
        iframe
      ihave Hh := Hback $$ Hn
      icases wtxHeap_live_node_acc tx (DFrac.own 1) _ bl _ n (rblClear rn) hb1 hr1 hnl $$ Hh
        with ⟨Ho, Hback⟩
      icases (objOwn_live_node _ _ _ _ _).1 $$ Ho with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
      ihave %Hsl1 := ownSlice_len _ _ _ $$ Hins
      ihave %Hwl1 := BigSepL2.bigSepL2_length $$ Hws
      have hil : 0 < rn.ins.length := by
        have : rn.ins.length = rn.ws.length := Hwl1
        rw [this, hws1]; omega
      obtain ⟨it, hit⟩ : ∃ it, rn.ins[0]? = some it := ⟨_, List.getElem?_eq_getElem hil⟩
      have hit' : (rblClear rn).ins[0]? = some it := hit
      have hw00' : (rblClear rn).ws[0]? = some w0 := hw00
      icases BigSepL2.bigSepL2_lookup_acc hit' hw00' $$ Hws with ⟨Hw0, Hwsb⟩
      icases (Write.wOwn_live _ _ _).1 $$ Hw0 with ⟨%Hfp, Hw0r⟩
      ihave Hws := Hwsb $$ [Hw0r]
      · iapply (Write.wOwn_live _ _ _).2; iframe; ipureintro; exact Hfp
      icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn3⟩
      iStructNamed Hn
      -- `n.inodes[0].Pgid()`
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧
        sint.Z (W64 0) < sint.Z rn.nv.inodes'.len from ⟨by word, by rw [hl1]; word⟩))]
      isimp only [rblClear] at Hins
      icases ownSlice_elem_acc (sint.Z (W64 0)) it rn.nv.inodes' _ rn.ins (by word) (by simpa using hit)
        $$ Hins with ⟨Hit, Hsback⟩
      wp_apply hPg $$ [$Hit] as Hit
      try wp_auto
      ihave Hins := Hsback $$ Hit
      rw [list_set_lookup_self _ _ _ (by simpa using hit), Hfp.2]
      ihave Hn : (n ↦ (rblClear rn).nv : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn3
        simp only [TypedPointsto.typedPointstoDef]; (try rw [hlf]); (try rw [hlf'])
        iframe
      ihave Hh := Hback $$ [Hn Hins Hcap Hws Hch Hchcap Hkey]
      · iapply (objOwn_live_node _ _ _ _ _).2
        isimp only [true_and] at Hkey
        simp only [eq_self_iff_true, true_and]
        iframe Hn Hcap Hws Hch Hchcap Hkey; simp only [rblClear]; iexact Hins
      ihave Hw : wtxW K tx r m (X.setBkt bl (rblStart B n rn)) $$
        [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
      · iapply (wtxW_split K tx r m _).2; unfold wtxCore
        simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc]
        iframe; iframe #; ipureintro; exact Hr
      -- `n.bucket.node(pgid, n)`
      have hroot0 := rbl_root_ne _ _ _ _ bl _ n (rblClear rn) hI1 hb1 hr1 hlf'
      obtain ⟨-, -, hnk3, -, -⟩ := hk1.2.2 n (rblClear rn) hr1
      obtain ⟨-, -, kind0, hkd0⟩ := hnk3 hlf'
      ihave %Hready : ⌜(rblStart B n rn).nm !! w0.pgid = none →
          matReady (X.setBkt bl (rblStart B n rn)) (rblStart B n rn) w0.pgid⌝ $$ [Hw]
      · by_cases hnone0 : (rblStart B n rn).nm !! w0.pgid = none
        · obtain ⟨pg0, hpg0, -⟩ := (hkd0 0 w0 hw00').2 hnone0
          ihave %Hmr := wtxW_matReady K tx r m _ (rblStart B n rn) w0.pgid pg0 hroot0
            hI1.2.2.2.2.2.2.1 hpg0 (by show X.t.pm !! _ = none; rw [hI.1.2.1]; rfl) $$ Hw
          ipureintro; exact fun _ => Hmr
        · ipureintro; exact fun h => absurd h hnone0
      icases wtxW_nm_acc K tx r m _ bl _ hb1 _ _ rfl rfl $$ Hw with ⟨Hnm, Hw⟩
      ihave %Hnodes := ownMap_not_nil _ _ _ $$ Hnm
      ihave Hw := Hw $$ Hnm
      rw [hnc.1]
      wp_apply hNode K tx r m _ bl _ w0.pgid n hb1 hbll Hnodes (fun l h => (hc1.2.2.2.2.1 _ l h).1)
        (fun h => ⟨Hready h, Or.inr ⟨rblClear rn, hr1, hlf', hnl⟩⟩) $$ [Hw] as %lc ⟨%X2, Hw, %Hmat⟩
      · iexact Hw
      sorry
    · -- a branch root with two entries or more: done
      ihave Hn : (n ↦ (rblClear rn).nv : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn'
        simp only [TypedPointsto.typedPointstoDef]; (try rw [hlf]); (try rw [hlf'])
        iframe
      ihave Hh := Hback $$ Hn
      ihave Hw : wtxW K tx r m (X.setBkt bl (rblStart B n rn)) $$
        [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
      · iapply (wtxW_split K tx r m _).2; unfold wtxCore
        simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc, WX.kill_v, WX.kill_handles, WX.kill_nloc, WX.setNode_v, WX.setNode_handles, WX.setNode_nloc]
        iframe; iframe #; ipureintro; exact Hr
      iapply HΦ
      iexists X.setBkt bl (rblStart B n rn), w.fl
      rw [show w.withFl w.fl = w from rfl]
      iframe
      ipureintro
      refine hpost (fun _ => ?_) (fun _ h => absurd hpn h)
      have h0 := hbrlen hlf
      have h1 : rn.nv.inodes'.len ≠ W64 1 := Hif
      have : sint.nat rn.nv.inodes'.len ≠ 1 := by intro h; apply h1; word
      omega
  · -- not the root
    have hpn : rn.nv.parent' ≠ null := Hif
    ihave Hn : (n ↦ (rblClear rn).nv : IProp GF)
      $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn'
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    wp_apply hNum n (rblClear rn).nv (DFrac.own 1) $$ [Hn] as Hn
    · iframe
    ihave Hh := Hback $$ [Hn]
    · simp only [rblClear]; iexact Hn
    ihave Hw : wtxW K tx r m (X.setBkt bl (rblStart B n rn)) $$
      [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
    · iapply (wtxW_split K tx r m _).2; unfold wtxCore
      simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc, WX.kill_v, WX.kill_handles, WX.kill_nloc, WX.setNode_v, WX.setNode_handles, WX.setNode_nloc]
      iframe; iframe #; ipureintro; exact Hr
    wp_if_destruct
    · -- an empty node: removed
      have hlen0 : rn.nv.inodes'.len = W64 0 := Hif
      have hemp : rn.ws = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hlen0]; rfl)
      have hleaf : rn.nv.isLeaf' = true := by
        rcases Bool.eq_false_or_eq_true rn.nv.isLeaf' with h | h
        · exact h
        · have := (hnc.2.2.2.2.2.2.2.2.2.2.2.2.1 h).1; rw [hemp] at this; cases this
      have hB1 := (hI1.2.1 bl _ hb1).1
      rw [if_pos rfl] at hB1
      obtain ⟨hc1, ⟨bnd1, hk1⟩, -, -⟩ := hB1
      obtain ⟨hkey, rp, i, wi, hrp1, hwi, hwp, hwk, -⟩ := (hk1.2.2 n (rblClear rn) hr1).2.1 hpn
      have hn1 := hc1.2.2.2.2.2.2.2.1 n (rblClear rn) hr1
      have hncp := hc1.2.2.2.2.2.2.2.1 _ rp hrp1
      obtain ⟨rq, hrq, hrpbr, -⟩ := hn1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
      rw [hrp1] at hrq; cases hrq
      have hroot0 := rbl_root_ne _ _ _ _ bl _ _ rp hI1 hb1 hrp1 hrpbr
      obtain ⟨pg, hpg, hp0⟩ := rbl_node_page _ _ _ _ bl _ n (rblClear rn) hI1 hb1 hr1 hroot0
      have hpln : rn.nv.parent' ≠ n := Hok1.2.2.2.1 bl _ n (rblClear rn) hb1 hr1
      have hpp : rp.nv.parent' ≠ rn.nv.parent' := Hok1.2.2.2.1 bl _ _ rp hb1 hrp1
      have hplive : rn.nv.parent' ∈ X.live := (hI1.2.1 bl _ hb1).2.2.2.2 _ rp hrp1
      have hfound := wsDelAt_at rp.ws i wi hncp.2.2.2.1 hwi
      have hidx := wsIdx_at rp.ws i wi hncp.2.2.2.1 hwi
      rw [hwk] at hfound hidx
      simp only [rblClear] at hfound hidx
      have hks : rn.ksrc ≠ Src.stale := (hn1.2.2.2.2.2.2.2.2.2.2.1.resolve_left hkey).2
      ihave %Hbase := wtxW_base_pos K tx r m _ $$ Hw
      -- open the node, its parent and the bucket
      icases (wtxW_split K tx r m _).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
      unfold wtxCore
      icases Hc with ⟨-, -, -, -, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
      have hLs : [n, rn.nv.parent'].Nodup := by simp [Ne.symm hpln]
      icases wtxHeap_setBkt_acc tx (DFrac.own 1) _ bl _ [n, rn.nv.parent']
        (fun l => if l = n then rblClear rn else rp) hb1 hLs
        (by
          intro l hl
          simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hl
          rcases hl with rfl | rfl
          · simp only [ite_true]; exact hr1
          · simp only [if_neg hpln]; exact hrp1) $$ Hh
        with ⟨⟨Hno, Hpo, -⟩, Hbo, Htf, Hrf, Hback⟩
      isimp only [ite_true, if_neg hpln] at Hno Hpo
      have hnl1 : n ∈ (X.setBkt bl (rblStart B n rn)).live := hnl
      have hbl1 : bl ∈ (X.setBkt bl (rblStart B n rn)).liveB := hbll
      have hpl1 : rn.nv.parent' ∈ (X.setBkt bl (rblStart B n rn)).live := hplive
      rw [decide_eq_true hnl1, decide_eq_true hpl1, decide_eq_true hbl1]
      icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
      rw [if_pos (show true = true ∧ (rblClear rn).nv.key' ≠ slice.nil from ⟨rfl, hkey⟩)]
      icases Hkey with #Hkey
      icases (objOwn_bkt_unf _ _ _ _ _).1 $$ Hbo
        with ⟨Hb1, Hbtx, Hb3, Hb4, Hb5, Hbnodes, Hib, Hnm, Hbm, Hpgo⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn2⟩
      iStructNamed Hn
      wp_auto
      -- `n.parent.del(n.key)`
      wp_apply hDel (X.setBkt bl (rblStart B n rn)).v rn.nv.parent' bl rp wq rn.nv.key'
        rn.key rn.ksrc hncp.2.1 hncp.2.2.2.1 hncp.2.2.2.2.2.1 hks Hbase $$ [Hpo Hcells Hkey]
        as ⟨Hd, Hcells⟩
      · iframe; simp only [rblClear]; iframe #
      icases Hd with (⟨%Hnf, -⟩ | ⟨-, %sI, Hpo⟩)
      · exact absurd hfound.1 Hnf
      rw [hfound.2, hidx]
      icases (objOwn_live_node _ _ _ _ _).1 $$ Hpo
        with ⟨Hp, Hpins, Hpcap, Hpws, Hpch, Hpchcap, Hpkey⟩
      ihave %Hpwl := BigSepL2.bigSepL2_length $$ Hpws
      try wp_auto
      -- `n.parent.removeChild(n)`
      wp_apply hRm rn.nv.parent' (rp.withEntsU sI (rp.ins.eraseIdx i) (rp.ws.eraseIdx i) true).nv rp.cs n $$ [Hp Hpch Hpchcap] as ⟨%sC, Hp, Hpch, Hpchcap⟩
      · simp only [NRec.withEntsU]; iframe
      rw [hnc.1]
      try wp_auto
      -- `delete(n.bucket.nodes, n.pgid)`
      rw [show (rblStart B n rn).bv = B.bv from rfl]
      wp_apply (wp_mapDelete (K := w64) (V := Loc) B.bv.nodes' (rblStart B n rn).nm
        rn.nv.pgid' internal.common.Pgid.ty (go.GoType.PointerType node.ty)) $$ [Hnm]
        as Hnm
      · iexact Hnm
      try wp_auto
      -- the heap on `X2`: the parent without the entry and the child, the cache without `n`
      let B2 : BRec := { rblStart B n rn with
        nm := GMap.delete (rblClear rn).nv.pgid' (rblStart B n rn).nm,
        ns := (rblStart B n rn).ns.insert rn.nv.parent' (rmParent rp i n sI sC) }
      ihave Hn : (n ↦ (rblClear rn).nv : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn2
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Hh := Hback $$ %B2 %(fun l => if l = n then rblClear rn else (rmParent rp i n sI sC))
        [] [Hn Hins Hcap Hws Hch Hchcap Hp Hpins Hpcap Hpws Hpch Hpchcap Hpkey]
        [Hb1 Hbtx Hb3 Hb4 Hb5 Hbnodes Hib Hnm Hbm Hpgo] [Htf] [Hrf]
      · ipureintro
        refine ⟨?_, ?_, rfl, ?_⟩
        · intro l hl
          simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hl
          rcases hl with rfl | rfl
          · simp only [ite_true]
            show ((rblStart B l rn).ns.insert rn.nv.parent' (rmParent rp i l sI sC)) !! l = _
            rw [GMap.lookup_insert_ne _ _ hpln]; exact hr1
          · simp only [if_neg hpln]; exact GMap.lookup_insert _ _ _
        · intro l hl
          simp only [List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hl
          show ((rblStart B n rn).ns.insert rn.nv.parent' (rmParent rp i n sI sC)) !! l = _
          exact GMap.lookup_insert_ne _ _ (Ne.symm hl.2)
        · intro l hl
          simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hl
          rcases hl with rfl | rfl
          · simp only [ite_true]; exact Hok1.2.2.2.1 bl _ l _ hb1 hr1
          · simp only [if_neg hpln]; exact hpp
      · iapply BigSepL.bigSepL_cons.2
        isplitl [Hn Hins Hcap Hws Hch Hchcap]
        · simp only [↓reduceIte]
          rw [decide_eq_true hnl1]
          iapply (objOwn_live_node _ _ _ _ _).2
          first
            | rw [if_pos (show true = true ∧ (rblClear rn).nv.key' ≠ slice.nil from ⟨rfl, hkey⟩)]
            | rw [if_pos (show True ∧ (rblClear rn).nv.key' ≠ slice.nil from ⟨trivial, hkey⟩)]
          iframe; iframe #
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hp Hpins Hpcap Hpws Hpch Hpchcap Hpkey]
        · simp only [if_neg hpln]
          rw [decide_eq_true hpl1]
          iapply (objOwn_live_node _ _ _ _ _).2
          dsimp only [rmParent, NRec.withEntsU, WX.setBkt_v]
          simp only [hncp.2.1, ↓reduceIte]
          by_cases hpk : rp.nv.key' = slice.nil
          · simp only [hpk, ne_eq, not_true_eq_false, and_false, ↓reduceIte]
            rw [cs_erase]; iframe
          simp only [hpk, ne_eq, not_false_eq_true, _root_.and_self, ↓reduceIte]
          isplitl [Hp]
          · iexact Hp
          isplitl [Hpins]
          · iexact Hpins
          isplitl [Hpcap]
          · iexact Hpcap
          isplitl [Hpws]
          · iexact Hpws
          isplitl [Hpch]
          · rw [cs_erase]; iexact Hpch
          isplitl [Hpchcap]
          · iexact Hpchcap
          iexact Hpkey
        iapply BigSepL.bigSepL_nil.2; iempintro
      · iapply (objOwn_bkt_unf _ _ _ _ _).2
        iframe
        simp only [ite_true, eq_self_iff_true, if_true]
        rw [pageOwn_congr' _ (rblStart B n rn) B2 rfl rfl rfl rfl]
        iexact Hpgo
      · iframe
      · iframe
      have hb2 : ((X.setBkt bl (rblStart B n rn)).setBkt bl B2).t.bs !! bl = some B2 :=
        GMap.lookup_insert _ _ _
      ihave Hw : wtxW K tx r m ((X.setBkt bl (rblStart B n rn)).setBkt bl B2) $$
        [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
      · iapply (wtxW_split K tx r m _).2; unfold wtxCore
        simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc, WX.kill_v, WX.kill_handles, WX.kill_nloc, WX.setNode_v, WX.setNode_handles, WX.setNode_nloc]
        iframe; iframe #; ipureintro; exact Hr
      -- `n.free()`
      icases wdbW_view_rbl K tx X.v w $$ Hdb with ⟨%Hwv, Hdb⟩
      have htxid : (X.setBkt bl (rblStart B n rn)).t.mv.txid' = w.wtxid :=
        rblX_wtxid _ w.fl bl _ w hI1 Hwv
      obtain ⟨pgc, hpgc, hlenc, hidc, hflc, hcanc⟩ :=
        rblX_canFree _ w.fl bl _ _ n (rblClear rn) hI1 hb1 hr1 hp0
      have hpgeq : pgc = pg := by
        have := hpg.symm.trans hpgc; cases this; rfl
      subst hpgeq
      have hX2n : ((X.setBkt bl (rblStart B n rn)).setBkt bl B2).node bl n = some (rblClear rn) := by
        unfold WX.node; rw [hb2]
        show ((rblStart B n rn).ns.insert rn.nv.parent' (rmParent rp i n sI sC)) !! n = _
        rw [GMap.lookup_insert_ne _ _ hpln]; exact hr1
      wp_apply hFree K tx r m _ w bl n (rblClear rn) hX2n hnc.1
        (fun _ => ⟨by show X.t.pm !! _ = none; rw [hI.1.2.1]; rfl, htxid, pgc, hpgc, hlenc, hidc,
          hflc, by rw [← htxid]; exact hcanc⟩)
        $$ [Hw Hdb] as ⟨%X3, %w3, Hw, Hdb, %Hfr⟩
      · iframe
      let r1' : NRec := { rblClear rn with nv := { (rblClear rn).nv with pgid' := W64 0 } }
      obtain ⟨hX3, hw3⟩ : X3 = ((X.setBkt bl (rblStart B n rn)).setBkt bl B2).setNode bl n r1' ∧
          w3 = w.withFl (w.fl.freePages w.wtxid (rblClear rn).nv.pgid' (1 + pageOverflow pgc)) := by
        rcases Hfr with ⟨h0, -, -⟩ | ⟨pg', -, hpg', hX3, hw3⟩
        · exact absurd h0 hp0
        · have := hpgc.symm.trans hpg'; cases this; exact ⟨hX3, hw3⟩
      subst hX3 hw3
      let B3 : BRec := { B2 with ns := B2.ns.insert n r1' }
      have hb3 : (((X.setBkt bl (rblStart B n rn)).setBkt bl B2).setNode bl n r1').t.bs !! bl =
          some B3 := by
        unfold WX.setNode; rw [hb2]; exact GMap.lookup_insert _ _ _
      have hr3 : B3.ns !! n = some r1' := GMap.lookup_insert _ _ _
      -- `n.parent` read (the node's struct)
      icases (wtxW_split K tx r m _).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
      unfold wtxCore
      icases Hc with ⟨-, -, -, -, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
      ihave %Hok3 := wtxHeap_heapOK tx (DFrac.own 1) _ $$ Hh
      have Ho3 := objs_node _ bl _ n _ Hok3.2.1 hb3 hr3
      icases wtxHeap_node_ptr_acc tx (DFrac.own 1) _ bl n r1' Ho3 $$ Hh with ⟨Hn, Hback⟩
      iStructNamed Hn
      wp_auto
      ihave Hn : (n ↦ r1'.nv : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn2
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Hh := Hback $$ Hn
      -- `n` goes dead: the records after the removal
      let B4 : BRec := rmBkt (rblStart B n rn) n rn.nv.parent' (rblClear rn).nv.pgid' (rmParent rp i n sI sC)
      have hns4 : B4.ns = GMap.delete n B3.ns := by
        apply GMap.ext
        intro y
        show B4.ns !! y = (GMap.delete n B3.ns) !! y
        rw [rm_ns]
        by_cases hy1 : y = rn.nv.parent'
        · subst hy1
          rw [if_pos rfl, GMap.lookup_delete_ne _ (Ne.symm hpln)]
          show _ = (B2.ns.insert n r1') !! rn.nv.parent'
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hpln)]
          exact (GMap.lookup_insert _ _ _).symm
        · rw [if_neg hy1]
          by_cases hy2 : y = n
          · subst hy2; rw [if_pos rfl, GMap.lookup_delete]
          · rw [if_neg hy2, GMap.lookup_delete_ne _ (Ne.symm hy2)]
            show _ = (B2.ns.insert n r1') !! y
            rw [GMap.lookup_insert_ne _ _ (Ne.symm hy2)]
            show _ = ((rblStart B n rn).ns.insert rn.nv.parent' (rmParent rp i n sI sC)) !! y
            rw [GMap.lookup_insert_ne _ _ (Ne.symm hy1)]
      ihave Hh := wtxHeap_kill_node tx (DFrac.own 1) _ bl B3 B4 n r1' hb3 hr3 rfl rfl rfl rfl rfl rfl
        rfl hns4 $$ Hh
      have hK : (((X.setBkt bl (rblStart B n rn)).setBkt bl B2).setNode bl n r1').kill bl B4 n r1' =
          (X.setBkt bl (rblStart B n rn)).kill bl B4 n r1' := by
        unfold WX.setNode; rw [hb2]; simp only [WX.kill, WX.setBkt, GMap.insert_insert]
      rw [hK]
      obtain ⟨hI4, hR4, -, -⟩ := rblX_rm (X.setBkt bl (rblStart B n rn)) w.fl bl _ n (rblClear rn)
        rn.nv.parent' rp i wi sI sC pgc hI1 hb1 hr1 hleaf hemp rfl hpn hrp1 hwi hwp hpgc
      have hfl : w.fl.freePages (X.setBkt bl (rblStart B n rn)).t.mv.txid' (rblClear rn).nv.pgid'
          (1 + pageOverflow pgc) =
          (w.withFl (w.fl.freePages w.wtxid (rblClear rn).nv.pgid' (1 + pageOverflow pgc))).fl := by
        rw [htxid]; rfl
      rw [hfl] at hI4 hR4
      have hb4 : ((X.setBkt bl (rblStart B n rn)).kill bl B4 n r1').t.bs !! bl = some B4 :=
        GMap.lookup_insert _ _ _
      have hrp4 : B4.ns !! rn.nv.parent' = some (rmParent rp i n sI sC) := by
        show (rmBkt (rblStart B n rn) n rn.nv.parent' (rblClear rn).nv.pgid' (rmParent rp i n sI sC)).ns !! _ = _
        rw [rm_ns, if_pos rfl]
      ihave Hw : wtxW K tx r m ((X.setBkt bl (rblStart B n rn)).kill bl B4 n r1') $$
        [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
      · iapply (wtxW_split K tx r m _).2; unfold wtxCore
        simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc, WX.kill_v, WX.kill_handles, WX.kill_nloc, WX.setNode_v, WX.setNode_handles, WX.setNode_nloc]
        iframe; iframe #; ipureintro; exact Hr
      -- `n.parent.rebalance()`
      wp_apply IH $$ %K %tx %r %m %((X.setBkt bl (rblStart B n rn)).kill bl B4 n r1')
        %(w.withFl (w.fl.freePages w.wtxid (rblClear rn).nv.pgid' (1 + pageOverflow pgc))) %bl %B4
        %rn.nv.parent' %(rmParent rp i n sI sC) %(some rn.nv.parent') [] [Hw Hdb] as ⟨%X5, %fl5, Hw, Hdb, %Hp5⟩
      · ipureintro
        exact ⟨hI4, hb4, hrp4, Or.inr ⟨rfl, rfl⟩, hfp⟩
      · isplitl [Hw]
        · iexact Hw
        simp only [WX.kill_v, WX.setBkt_v]
        iexact Hdb
      try wp_auto
      obtain ⟨h5I, h5R, h5S⟩ := Hp5
      iapply HΦ
      iexists X5, fl5
      iframe Hw
      isplitl [Hdb]
      · rw [← WDb.withFl_withFl w _ fl5]; simp only [WX.kill_v, WX.setBkt_v]; iexact Hdb
      ipureintro
      refine ⟨h5I, rblRel_trans _ _ _ _ _ _ _ hR1 (rblRel_trans _ _ _ _ _ _ _ hR4 h5R), ?_, ?_⟩
      · intro bl' hne
        rw [h5S.1 bl' hne]
        show (((X.t.bs.insert bl (rblStart B n rn)).insert bl B4)) !! bl' = _
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hne), GMap.lookup_insert_ne _ _ (Ne.symm hne)]
      · intro B0 B5 h0 h5
        rw [hb] at h0; cases h0
        exact rblStep_comp B B4 B5 n rn.nv.parent' (rblPre_rm B n rn rn.nv.parent' (rmParent rp i n sI sC))
          (h5S.2 B4 B5 hb4 h5)
    · -- merged with a sibling
      have hne0 : rn.nv.inodes'.len ≠ W64 0 := Hif
      have hB1 := (hI1.2.1 bl _ hb1).1
      rw [if_pos rfl] at hB1
      obtain ⟨hc1, ⟨bnd1, hk1⟩, -, -⟩ := hB1
      obtain ⟨hkey, rp, i, wi, hrp1, hwi, hwp, hwk, -⟩ := (hk1.2.2 n (rblClear rn) hr1).2.1 hpn
      have hn1 := hc1.2.2.2.2.2.2.2.1 n (rblClear rn) hr1
      have hncp := hc1.2.2.2.2.2.2.2.1 _ rp hrp1
      obtain ⟨rq, hrq, hrpbr, -⟩ := hn1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
      rw [hrp1] at hrq; cases hrq
      have hpln : rn.nv.parent' ≠ n := Hok1.2.2.2.1 bl _ n (rblClear rn) hb1 hr1
      -- the parent has two entries (it is not the deficient node)
      have hp2 : 2 ≤ rp.ws.length := by
        have := ((hk1.2.2 _ rp hrp1).2.2.1 hrpbr).1
        exact this (fun h => hpln (Option.some.inj h).symm)
      trace_state
      sorry


theorem node.rebalance.wp_proof
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hNum : node.numChildren.spec (GF := GF) (hG := hG))
    (hIdx : node.childIndex.spec (GF := GF) (hG := hG))
    (hNext : node.nextSibling.spec (GF := GF) (hG := hG))
    (hPrev : node.prevSibling.spec (GF := GF) (hG := hG))
    (hDel : node.del.spec (GF := GF) (hG := hG))
    (hRm : node.removeChild.spec (GF := GF) (hG := hG))
    (hFree : node.free.spec (GF := GF) (hG := hG))
    (hNode : Bucket.node.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncRebalance.spec (GF := GF) (hG := hG))
    (hAssert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hPg : internal.common.Inode.Pgid.spec (GF := GF) (hG := hG)) :
    node.rebalance.spec' (GF := GF) (hG := hG) := by
  intro K tx r m X w bl B n rn dfc H1 H2 H3 H4 H5
  have H := rebal_loeb hSize hNum hIdx hNext hPrev hDel hRm hFree hNode hInc hAssert hPg
  unfold rebalW at H
  iintro %Φ HP HΦ
  ihave #H := H
  iapply H $$ %K %tx %r %m %X %w %bl %B %n %rn %dfc [] [HP] HΦ
  · ipureintro; exact ⟨H1, H2, H3, H4, H5⟩
  · iexact HP

end proof

end bbolt
end EtcdGrove
end Perennial
