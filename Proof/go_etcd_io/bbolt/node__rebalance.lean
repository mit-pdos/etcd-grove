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
  unfold wtxW wtxCore
  icases Hw with ⟨⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩, Hcells, Hmap⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  have Ho := objs_node X.t bl B n rn Hok.2.1 hb hrn
  icases wtxHeap_node_ptr_acc tx (DFrac.own 1) X bl n rn Ho $$ Hh with ⟨Hn, Hback⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  have hnl : n ∈ X.live := (hI.2.1 bl B hb).2.2.2.2 n rn hrn
  have hbll : bl ∈ X.live := hI.2.2.2.2.1.2.2.1 bl B hb
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
    iapply HΦ
    iexists X, w.fl
    rw [show w.withFl w.fl = w from rfl]
    iframe; iframe #
    isplitr
    · ipureintro; exact Hr
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
  wp_auto
  wp_apply wp_ArbitraryInt as %thr _
  ihave Hn : (n ↦ ({ rn.nv with unbalanced' := false } : node) : IProp GF)
    $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn'
    simp only [TypedPointsto.typedPointstoDef]; rw [hnc.1]
    iframe
  wp_apply hSize n ({ rn.nv with unbalanced' := false } : node) rn.ins (DFrac.own 1) (DFrac.own 1)
    (rblX_insSize X w.fl bl dfc bl B n rn hI hb hrn) $$ [Hn Hins] as ⟨Hn, Hins⟩
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
  · unfold wtxW wtxCore; iframe; iframe #; ipureintro; exact Hr
  have hlen : rn.ws.length = sint.nat rn.nv.inodes'.len := by rw [← hnc.2.2.1, Hsl.1]
  wp_if_destruct
  · -- big enough: done
    have hmk := Hif.2
    have h2 : rn.nv.isLeaf' = false → 2 ≤ rn.ws.length := by
      intro hl; rw [hl] at hmk; simp only [Bool.false_eq_true, ↓reduceIte] at hmk; rw [hlen]; word
    have h1 : rn.nv.isLeaf' = true → rn.nv.parent' ≠ null → 0 < rn.ws.length := by
      intro hl _; rw [hl] at hmk; simp only [↓reduceIte] at hmk; rw [hlen]; word
    obtain ⟨hD1, hD2, hD3⟩ := rblX_done X w.fl bl dfc B n rn hI hb hrn hdfc' h2 h1
    iapply HΦ
    iexists X.setBkt bl (rblStart B n rn), w.fl
    rw [show w.withFl w.fl = w from rfl]
    unfold wtxW wtxCore
    iframe
    ipureintro
    refine ⟨hD1, hD2, fun bl' hne => ?_, fun B1 B2 h1' h2' => ?_⟩
    · show (X.t.bs.insert bl _) !! bl' = _; rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]
    · rw [hb] at h1'; cases h1'
      have : (X.setBkt bl (rblStart B n rn)).t.bs !! bl = some (rblStart B n rn) := GMap.lookup_insert _ _ _
      rw [this] at h2'; cases h2'; exact hD3
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
