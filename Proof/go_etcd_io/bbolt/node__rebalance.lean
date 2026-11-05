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
public import Proof.go_etcd_io.bbolt.Write.NodeDelS
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
public import Proof.go_etcd_io.bbolt.Rebalance.RblColMat
public import Proof.go_etcd_io.bbolt.Inv.MatReady
public import Proof.go_etcd_io.bbolt.Rebalance.RblMgSel

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

/-- The merge's siblings selected (`nextSibling`/`prevSibling`, `X2` after a materialization):
`ll`, `lr` the parent `pl`'s children at its entries `k`, `k + 1`, one of them `n`. -/
def mgSel (X X2 : WX) (fl : FLPg) (bl : Loc) (B : BRec) (n : Loc) (rn : NRec) (pl ll lr : Loc)
    (k : Nat) : Prop :=
  ∃ (B2 : BRec) (rp2 rl rr : NRec) (wl wr : WEntry), X2.t.bs !! bl = some B2 ∧
    B2.ns !! pl = some rp2 ∧ rp2.nv.isLeaf' = false ∧ rp2.ws[k]? = some wl ∧
    rp2.ws[k + 1]? = some wr ∧ B2.nm !! wl.pgid = some ll ∧ B2.nm !! wr.pgid = some lr ∧
    B2.ns !! ll = some rl ∧ B2.ns !! lr = some rr ∧ (n = ll ∨ n = lr) ∧
    B2.ns !! n = some (rblClear rn) ∧
    rblX X2 fl bl (some n) ∧ rblRel (X.setBkt bl (rblStart B n rn)) fl X2 fl X.t.mv.txid' ∧
    (∀ bl', bl' ≠ bl → X2.t.bs !! bl' = (X.setBkt bl (rblStart B n rn)).t.bs !! bl') ∧
    (∀ y ry', B2.ns !! y = some ry' → ry'.nv.unbalanced' = true →
      ∃ ry, (rblStart B n rn).ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
        ry'.nv.pgid' = ry.nv.pgid')

omit hos in
/-- A field of `n`, one of the merge's two nodes `ll`, `lr` (`n.bucket`, `n.parent`). -/
theorem pair_field_acc (n ll lr : Loc) (hn : n = ll ∨ n = lr) (f : GoString) (x xL xR : Loc)
    (hL : xL = x) (hR : xR = x) :
    ((ll.[node, f] ↦ xL) ∗ (lr.[node, f] ↦ xR) : IProp GF) ⊢
      n.[node, f] ↦ x ∗ (n.[node, f] ↦ x -∗ ll.[node, f] ↦ xL ∗ lr.[node, f] ↦ xR) := by
  subst hL hR
  rcases hn with rfl | rfl
  · iintro ⟨H1, H2⟩; iframe H1; iintro H; iframe
  · iintro ⟨H1, H2⟩; iframe H2; iintro H; iframe

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
        (fun h => ⟨Hready h, Or.inr ⟨rblClear rn, hr1, hlf', hnl⟩⟩) (fun _ h => hc1.2.2.2.2.2.1 h)
        $$ [Hw] as %lc ⟨%X2, Hw, %Hmat⟩
      · iexact Hw
      -- the child's record (`rblX_colMat`) and the collapse's pure facts
      have hnlc : ((X.setBkt bl (rblStart B n rn)).t.objs !! lc).isNone →
          (X.setBkt bl (rblStart B n rn)).nloc !! lc = none := by
        intro h
        cases hx : (X.setBkt bl (rblStart B n rn)).nloc !! lc with
        | none => rfl
        | some y =>
          have := Hok1.2.2.2.2.1 lc y hx
          rw [Option.isNone_iff_eq_none] at h; rw [h] at this; cases this
      obtain ⟨B2, rn2, rc, hb2, hrn2, hlc, hrc, hI2, hR2, hoth2, hnv2, hws2, hins2, hkey2, hks2,
        hco2, hU2⟩ := rblX_colMat _ X2 w.fl bl _ n (rblClear rn) w0 lc hI1 hb1 hr1 hlf' hw0 Hmat hnlc
      have hpn2 : rn2.nv.parent' = null := by rw [hnv2]; exact hpn
      have hbr2 : rn2.nv.isLeaf' = false := by rw [hnv2]; exact hlf
      have hws2' : rn2.ws = [w0] := hws2.trans hw0
      have hB2 := (hI2.2.1 bl B2 hb2).1
      rw [if_pos rfl] at hB2
      obtain ⟨hc2, -, ha2, -⟩ := hB2
      obtain ⟨hp1, hlcn, hpg3, -, -, hroot2, -⟩ :=
        col_basic X2.v _ bl B2 n rn2 w0 lc rc hc2 ha2 hrn2 hbr2 hpn2 hws2' hlc hrc
      obtain ⟨hchar, hnd, hkn⟩ :=
        col_kids X2 w.fl bl (some n) B2 n rn2 w0 lc rc hI2 hb2 hrn2 hbr2 hpn2 hws2' hlc hrc
      have hX2v : X2.v = X.v := hR2.1
      have hlive2 : ∀ y ry, B2.ns !! y = some ry → y ∈ X2.live :=
        fun y ry h => (hI2.2.1 bl B2 hb2).2.2.2.2 y ry h
      -- open the root, the child and the child's children
      icases (wtxW_split K tx r m X2).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
      unfold wtxCore
      icases Hc with ⟨-, -, %Hr2, -, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
      ihave %Hok2 := wtxHeap_heapOK tx (DFrac.own 1) _ $$ Hh
      icases wtxHeap_setBkt_live_acc tx (DFrac.own 1) X2 bl B2 ([n, lc] ++ kidsOf B2 rc.ws)
        (fun l => if l = n then rn2 else if l = lc then rc else colKid B2 rc.ws n rc 0 l) hb2 hnd
        (by
          intro l hl
          simp only [List.cons_append, List.nil_append, List.mem_cons] at hl
          rcases hl with rfl | rfl | hl
          · simp only [ite_true]; exact hrn2
          · simp only [if_neg hlcn, ite_true]; exact hrc
          · obtain ⟨rk, hrk, -⟩ := (hchar l).1 hl
            simp only [if_neg (hkn l hl).1, if_neg (hkn l hl).2, colKid_zero, hrk, Option.getD_some])
        $$ Hh with ⟨HL, Hbo, Htf, Hrf, Hback⟩
      icases (BigSepL.bigSepL_append).1 $$ HL with ⟨⟨Hno, Hlo, -⟩, Hks⟩
      isimp only [ite_true, if_neg hlcn] at Hno Hlo
      rw [decide_eq_true (hlive2 n _ hrn2), decide_eq_true (hlive2 lc _ hrc)]
      icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
      icases (objOwn_live_node _ _ _ _ _).1 $$ Hlo
        with ⟨Hl, Hlins, Hlcap, Hlws, Hlch, Hlchcap, Hlkey⟩
      icases (objOwn_bkt_unf _ _ _ _ _).1 $$ Hbo
        with ⟨Hb1, Hbtx, Hb3, Hb4, Hb5, Hbnodes, Hib, Hnm, Hbm, Hpgo⟩
      ihave %Hlwf := ownSlice_wf _ _ _ $$ Hlins
      icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn4⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hlnn⟩
      iStructNamed Hn
      iStructNamedSuffix Hl "C"
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧
        sint.Z (W64 0) ≤ sint.Z rc.nv.inodes'.len ∧ sint.Z rc.nv.inodes'.len ≤ sint.Z rc.nv.inodes'.cap
        from ⟨by word, Hlwf.1, Hlwf.2⟩)), ← slice_slice_trivial (V := Inode)]
      wp_auto
      -- the reparenting loop over the child's entries
      ihave %Hlwl := BigSepL2.bigSepL2_length $$ Hlws
      have hbkt2 : rn2.nv.bucket' = bl := by rw [hnv2]; exact hnc.1
      rw [hbkt2]
      ihave IHl : iprop(∃ (j : w64),
          "i" ∷ i_ptr ↦ j ∗ "Hlins" ∷ rc.nv.inodes' ↦* rc.ins ∗
          "Hlws" ∷ ([∗list] it;w ∈ rc.ins;rc.ws, wOwn X2.v true it w) ∗
          "Hks" ∷ ([∗list] l ∈ kidsOf B2 rc.ws, objOwn X2.v l (DFrac.own 1) (decide (l ∈ X2.live))
            (.node bl (if l = n then rn2 else if l = lc then rc else
              colKid B2 rc.ws n rc (sint.nat j) l))) ∗
          "Hnm" ∷ B2.bv.nodes' ↦$ B2.nm ∗ "Hbnodes" ∷ bl.[Bucket, go!"nodes"] ↦ B2.bv.nodes' ∗
          "bucket" ∷ n.[node, go!"bucket"] ↦ bl ∗ "n" ∷ n_ptr ↦ n ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rc.nv.inodes'.len⌝)
        $$ [i Hlins Hlws Hks Hnm Hbnodes bucket n]
      · iexists W64 0
        iframe
        ipureintro; exact ⟨by word, by word⟩
      repeat (irename : ("_" ∷ True : IProp GF) => Htriv; iclear Htriv)
      repeat (irename : (True : IProp GF) => Htriv; iclear Htriv)
      wp_for IHl
      wp_if_destruct
      · have Hlt : sint.Z j < sint.Z rc.nv.inodes'.len := by simpa using Hif
        ihave %Hlsl := ownSlice_len _ _ _ $$ Hlins
        have Hjn : sint.nat j < rc.ins.length := by rw [Hlsl.1]; word
        list_elem rc.ins (sint.nat j) as itj
        obtain ⟨wj, hwj⟩ : ∃ wj, rc.ws[sint.nat j]? = some wj :=
          ⟨_, List.getElem?_eq_getElem (by rw [← Hlwl]; exact Hjn)⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z rc.nv.inodes'.len
          from ⟨Hj.1, Hlt⟩))]
        wp_apply wp_load_slice_index _ (sint.Z j) rc.ins _ itj Hj.1 $$ [Hlins] as Hlins
        · iframe; ipureintro; simpa using Hitj_lookup
        try wp_auto
        icases BigSepL2.bigSepL2_lookup_acc (by simpa using Hitj_lookup) hwj $$ Hlws with ⟨Hwj, Hlwsb⟩
        icases (Write.wOwn_live _ _ _).1 $$ Hwj with ⟨%Hfpj, Hwjr⟩
        ihave Hlws := Hlwsb $$ [Hwjr]
        · iapply (Write.wOwn_live _ _ _).2; iframe; ipureintro; exact Hfpj
        wp_apply hPg $$ [$inode] as inode
        rw [Hfpj.2]
        wp_apply wp_map_lookup2 $$ [Hnm] as Hnm
        · iexact Hnm
        try wp_auto
        have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        rcases hkk : B2.nm !! wj.pgid with _ | k
        · -- no node at this entry
          simp only [Option.isSome_none, Option.getD_none, decide_false, Bool.false_eq_true]
          try wp_auto
          wp_for_post
          iframe
          iexists j + W64 1
          rw [Hj1]
          simp only [colKid_none B2 rc.ws n rc (sint.nat j) wj hwj hkk]
          iframe
          ipureintro; exact ⟨by word, by word⟩
        · -- the node `k`: reparented to `n`
          simp only [Option.isSome_some, Option.getD_some, _root_.decide_true]
          try wp_auto
          have hkm : k ∈ kidsOf B2 rc.ws := List.mem_filterMap.2 ⟨wj, List.mem_of_getElem? hwj, hkk⟩
          obtain ⟨hkn1, hkn2⟩ := hkn k hkm
          obtain ⟨rk, hrk, -⟩ := (hchar k).1 hkm
          obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.1 hkm
          obtain ⟨hks1, hks2⟩ := colKid_some B2 rc.ws n rc (sint.nat j) wj hwj k hkk
          have hndk : (kidsOf B2 rc.ws).Nodup := (List.nodup_append.1 hnd).2.1
          icases BigSepL.bigSepL_lookup_acc_impl hidx $$ Hks with ⟨Hk, Hkb⟩
          isimp only [if_neg hkn1, if_neg hkn2] at Hk
          rw [decide_eq_true (hlive2 k rk hrk)]
          icases (objOwn_live_node _ _ _ _ _).1 $$ Hk
            with ⟨Hkn, Hkins, Hkcap, Hkws, Hkch, Hkchcap, Hkkey⟩
          icases typedPointsto_not_null_dup _ _ _ $$ Hkn with ⟨Hkn, %Hknn⟩
          iStructNamedSuffix Hkn "K"
          try wp_auto
          ihave Hk : objOwn X2.v k (DFrac.own 1) true
              (.node bl (colRe (colKid B2 rc.ws n rc (sint.nat j) k) n))
            $$ [bucketK isLeafK unbalancedK spilledK keyK pgidK parentK childrenK inodesK
              Hkins Hkcap Hkws Hkch Hkchcap Hkkey]
          · iapply (objOwn_live_node _ _ _ _ _).2
            isplitl [bucketK isLeafK unbalancedK spilledK keyK pgidK parentK childrenK inodesK]
            · iapply typedPointsto_combine _ _ _ Hknn
              simp only [TypedPointsto.typedPointstoDef, colRe]
              iframe
            simp only [colRe]
            iframe
          ihave Hks := Hkb $$ %(fun _ l => objOwn X2.v l (DFrac.own 1) (decide (l ∈ X2.live))
              (.node bl (if l = n then rn2 else if l = lc then rc else
                colKid B2 rc.ws n rc (sint.nat j + 1) l))) [] [Hk]
          · imodintro
            iintro %k' %y %hy %hne H
            have hyk : y ≠ k := by
              intro he; subst he
              apply hne
              obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hy
              obtain ⟨h1', h2'⟩ := List.getElem?_eq_some_iff.1 hidx
              exact (List.Nodup.getElem_inj hndk).1 (h2.trans h2'.symm)
            simp only [hks2 y hyk]
            iexact H
          · simp only [if_neg hkn1, if_neg hkn2, hks1, decide_eq_true (hlive2 k rk hrk)]
            iexact Hk
          wp_for_post
          iframe
          iexists j + W64 1
          rw [Hj1]
          iframe
          ipureintro; exact ⟨by word, by word⟩
      · have Hge : ¬ sint.Z j < sint.Z rc.nv.inodes'.len := by simpa using Hif
        ihave %Hlsl := ownSlice_len _ _ _ $$ Hlins
        have Hjlen : sint.nat j = rc.ws.length := by rw [← Hlwl, Hlsl.1]; word
        rw [Hjlen]
        try wp_auto
        -- `delete(n.bucket.nodes, child.pgid)`
        wp_apply (wp_mapDelete (K := w64) (V := Loc) B2.bv.nodes' B2.nm rc.nv.pgid'
          internal.common.Pgid.ty (go.GoType.PointerType node.ty)) $$ [Hnm] as Hnm
        · iexact Hnm
        try wp_auto
        -- close the heap: the root holds the child's entries, the child only its struct
        obtain ⟨hcl1, hcl2, hcl3⟩ := colBktL_close B2 n lc rn2 rc hrn2 hrc hlcn Hnn Hlnn hpn2 hchar hkn
        have hlv : ∀ k, k ≠ lc → (k ∈ GMap.delete lc X2.live ↔ k ∈ X2.live) := fun k hk => by
          rw [GMap.mem_iff, GMap.mem_iff, GMap.lookup_delete_ne _ (Ne.symm hk)]
        have hlv0 : decide (lc ∈ GMap.delete lc X2.live) = false := by
          rw [decide_eq_false_iff_not, GMap.mem_iff, GMap.lookup_delete]; simp
        have hnlv : decide (n ∈ GMap.delete lc X2.live) = true :=
          decide_eq_true ((hlv n (Ne.symm hlcn)).2 (hlive2 n _ hrn2))
        ihave Hks := (BigSepL.bigSepL_mono (Ψ := fun _ x => objOwn X2.v x (DFrac.own 1)
            (decide (x ∈ GMap.delete lc X2.live)) (.node bl (colF B2 n lc rn2 rc x)))
          (fun {k x} hx => by
            obtain ⟨h1, h2⟩ := hkn x (List.mem_of_getElem? hx)
            simp only [colF, if_neg h1, if_neg h2, hlv x h2]
            exact .rfl)) $$ Hks
        ihave Hh := Hback $$ %(colBktL B2 n lc rn2 rc) %(colF B2 n lc rn2 rc)
          %(GMap.delete lc X2.live) [] [isLeaf inodes children Hlins Hlcap Hlws Hlch Hlchcap Hkey
            Hks bucket unbalanced spilled key pgid parent bucketC isLeafC unbalancedC spilledC keyC
            pgidC parentC childrenC inodesC]
          [Hb1 Hbtx Hb3 Hb4 Hb5 Hbnodes Hib Hnm Hbm Hpgo] [Htf] [Hrf]
        · ipureintro
          refine ⟨hcl1, hcl2, rfl, hcl3, fun k hk => hlv k (fun h => hk (by simp [h]))⟩
        · iapply (BigSepL.bigSepL_append).2
          isplitr [Hks]
          · iapply BigSepL.bigSepL_cons.2
            isplitl [isLeaf inodes children Hlins Hlcap Hlws Hlch Hlchcap Hkey bucket unbalanced
              spilled key pgid parent]
            · simp only [colF, ite_true]
              rw [hnlv]
              iapply (objOwn_live_node _ _ _ _ _).2
              isimp only [true_and] at Hkey
              simp only [colRoot, eq_self_iff_true, true_and]
              isplitl [isLeaf inodes children bucket unbalanced spilled key pgid parent]
              · iapply typedPointsto_combine _ _ _ Hnn4
                simp only [TypedPointsto.typedPointstoDef]
                rw [hbkt2]
                iframe
              iframe
            iapply BigSepL.bigSepL_cons.2
            isplitl [bucketC isLeafC unbalancedC spilledC keyC pgidC parentC childrenC inodesC]
            · simp only [colF, if_neg hlcn, ite_true]
              rw [hlv0]
              unfold objOwn
              iapply typedPointsto_combine _ _ _ Hlnn
              simp only [TypedPointsto.typedPointstoDef, colRe]
              iframe
            iapply BigSepL.bigSepL_nil.2; iempintro
          · iexact Hks
        · iapply (objOwn_bkt_unf _ _ _ _ _).2
          iframe
        · iframe
        · iframe
        have hb3 : ({ X2.setBkt bl (colBktL B2 n lc rn2 rc) with live := GMap.delete lc X2.live } :
            WX).t.bs !! bl = some (colBktL B2 n lc rn2 rc) := GMap.lookup_insert _ _ _
        ihave Hw : wtxW K tx r m
            { X2.setBkt bl (colBktL B2 n lc rn2 rc) with live := GMap.delete lc X2.live } $$
          [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
        · iapply (wtxW_split K tx r m _).2; unfold wtxCore
          simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc]
          iframe; iframe #; ipureintro; exact Hr2
        -- `child.free()`
        icases wdbW_view_rbl K tx X.v w $$ Hdb with ⟨%Hwv, Hdb⟩
        have htxid2 : X2.t.mv.txid' = w.wtxid :=
          rblX_wtxid X2 w.fl bl _ w hI2 (by rw [hX2v]; simpa using Hwv)
        obtain ⟨pgc0, -, hp0c⟩ := rbl_node_page X2 w.fl bl (some n) bl B2 lc rc hI2 hb2 hrc hroot2
        obtain ⟨pgc, hpgc, hlenc, hidc, hflc, hcanc⟩ :=
          rblX_canFree X2 w.fl bl (some n) B2 lc rc hI2 hb2 hrc hp0c
        have hX3n : ({ X2.setBkt bl (colBktL B2 n lc rn2 rc) with live := GMap.delete lc X2.live } :
            WX).node bl lc = some (colRe rc null) := by
          unfold WX.node; rw [hb3]; exact GMap.lookup_insert _ _ _
        have hbk3 : (colRe rc null).nv.bucket' = bl := (hc2.2.2.2.2.2.2.2.1 lc rc hrc).1
        wp_apply hFree K tx r m _ w bl lc (colRe rc null) hX3n hbk3
          (fun _ => ⟨by show X2.t.pm !! _ = none; rw [hI2.1.2.1]; rfl, htxid2, pgc, hpgc, hlenc, hidc,
            hflc, by rw [← htxid2]; exact hcanc⟩)
          $$ [Hw Hdb] as ⟨%X4, %w4, Hw, Hdb, %Hfr⟩
        · rw [show ({ X2.setBkt bl (colBktL B2 n lc rn2 rc) with live := GMap.delete lc X2.live } :
            WX).v = X.v from hX2v]
          iframe
        obtain ⟨hX4, hw4⟩ : X4 = ({ X2.setBkt bl (colBktL B2 n lc rn2 rc) with
              live := GMap.delete lc X2.live } : WX).setNode bl lc
              { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } } ∧
            w4 = w.withFl (w.fl.freePages w.wtxid rc.nv.pgid' (1 + pageOverflow pgc)) := by
          rcases Hfr with ⟨h0, -, -⟩ | ⟨pg', -, hpg', hX4, hw4⟩
          · exact absurd h0 hp0c
          · have := hpgc.symm.trans hpg'; cases this; exact ⟨hX4, hw4⟩
        subst hX4 hw4
        try wp_auto
        -- the child goes dead: the collapse's records
        icases (wtxW_split K tx r m _).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
        unfold wtxCore
        icases Hc with ⟨-, -, -, -, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
        have hb4 : (({ X2.setBkt bl (colBktL B2 n lc rn2 rc) with
              live := GMap.delete lc X2.live } : WX).setNode bl lc
              { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } }).t.bs !! bl =
            some { colBktL B2 n lc rn2 rc with ns := ((colBktL B2 n lc rn2 rc).ns.insert lc
              { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } }) } := by
          unfold WX.setNode; rw [hb3]; exact GMap.lookup_insert _ _ _
        have hns5 : (colBkt B2 n lc rc.nv.pgid' (colRoot rn2 rc rc.nv.inodes')).ns =
            GMap.delete lc ((colBktL B2 n lc rn2 rc).ns.insert lc
              { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } }) := by
          show _ = GMap.delete lc
            (((colBkt B2 n lc rc.nv.pgid' (colRoot rn2 rc rc.nv.inodes')).ns.insert lc
              (colRe rc null)).insert lc _)
          rw [GMap.insert_insert, GMap.delete_insert_eq,
            GMap.delete_notin _ _ (by rw [col_ns, if_neg hlcn, if_pos rfl])]
        ihave Hh := wtxHeap_kill_node tx (DFrac.own 1) _ bl _
          (colBkt B2 n lc rc.nv.pgid' (colRoot rn2 rc rc.nv.inodes')) lc
          { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } } hb4
          (GMap.lookup_insert _ _ _) rfl rfl rfl rfl rfl rfl rfl hns5 $$ Hh
        have hK : (({ X2.setBkt bl (colBktL B2 n lc rn2 rc) with
              live := GMap.delete lc X2.live } : WX).setNode bl lc
              { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } }).kill bl
              (colBkt B2 n lc rc.nv.pgid' (colRoot rn2 rc rc.nv.inodes')) lc
              { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } } =
            X2.kill bl (colBkt B2 n lc rc.nv.pgid' (colRoot rn2 rc rc.nv.inodes')) lc
              { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } } := by
          unfold WX.setNode; rw [hb3]
          simp only [WX.kill, WX.setBkt, GMap.insert_insert, GMap.delete_idemp]
        rw [hK]
        obtain ⟨hIc, hRc, -, hUc⟩ := rblX_col X2 w.fl bl B2 n rn2 w0 lc rc rc.nv.inodes' pgc hI2 hb2
          hrn2 hbr2 hpn2 hws2' hlc hrc hpgc
        have hflc' : w.fl.freePages X2.t.mv.txid' rc.nv.pgid' (1 + pageOverflow pgc) =
            (w.withFl (w.fl.freePages w.wtxid rc.nv.pgid' (1 + pageOverflow pgc))).fl := by
          rw [htxid2]; rfl
        rw [hflc'] at hIc hRc
        obtain ⟨hRf, hothf, hstepf⟩ := rbl_col_post X X2 w.fl _ bl B B2 _ n lc rn rn2 _ hb hR1 hR2
          hb2 hoth2 hU2 (by rw [hnv2]; rfl) hRc hUc ⟨rfl, rfl, rfl⟩
        ihave Hw : wtxW K tx r m (X2.kill bl (colBkt B2 n lc rc.nv.pgid' (colRoot rn2 rc rc.nv.inodes'))
            lc { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } }) $$
          [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
        · iapply (wtxW_split K tx r m _).2; unfold wtxCore
          simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc, WX.kill_v, WX.kill_handles,
            WX.kill_nloc, WX.setNode_v, WX.setNode_handles, WX.setNode_nloc]
          iframe; iframe #; ipureintro; exact Hr2
        iapply HΦ
        iexists _, w.fl.freePages w.wtxid rc.nv.pgid' (1 + pageOverflow pgc)
        isplitl [Hw]
        · iexact Hw
        isplitl [Hdb]
        · isimp only [WX.setNode_v, WX.setBkt_v] at Hdb
          rw [← hX2v]
          iexact Hdb
        ipureintro
        refine ⟨hIc, hRf, hothf, fun B0 B5 h0 h5 => ?_⟩
        rw [hb] at h0; cases h0
        rw [show (X2.kill bl (colBkt B2 n lc rc.nv.pgid' (colRoot rn2 rc rc.nv.inodes')) lc
          { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } }).t.bs !! bl =
          some (colBkt B2 n lc rc.nv.pgid' (colRoot rn2 rc rc.nv.inodes')) from
          GMap.lookup_insert _ _ _] at h5
        cases h5; exact hstepf
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
      wp_apply node.del.specS hDel (X.setBkt bl (rblStart B n rn)).v rn.nv.parent' bl rp wq rn.nv.key'
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
      have hpp : rp.nv.parent' ≠ rn.nv.parent' := Hok1.2.2.2.1 bl _ _ rp hb1 hrp1
      have hplive : rn.nv.parent' ∈ X.live := (hI1.2.1 bl _ hb1).2.2.2.2 _ rp hrp1
      have hks : rn.ksrc ≠ Src.stale := (hn1.2.2.2.2.2.2.2.2.2.2.1.resolve_left hkey).2
      have hidx := wsIdx_at rp.ws i wi hncp.2.2.2.1 hwi
      rw [hwk] at hidx
      simp only [rblClear] at hidx
      ihave %Hbase := wtxW_base_pos K tx r m _ $$ Hw
      -- `n.parent.numChildren()`, the assertion, `n.parent.childIndex(n)`
      icases (wtxW_split K tx r m _).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
      unfold wtxCore
      icases Hc with ⟨-, -, -, -, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
      have hLs : [n, rn.nv.parent'].Nodup := by simp [Ne.symm hpln]
      have hfLs : ∀ l ∈ [n, rn.nv.parent'],
          (rblStart B n rn).ns !! l = some ((fun l => if l = n then rblClear rn else rp) l) := by
        intro l hl
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hl
        rcases hl with rfl | rfl
        · simp only [ite_true]; exact hr1
        · simp only [if_neg hpln]; exact hrp1
      icases wtxHeap_setBkt_acc tx (DFrac.own 1) _ bl _ [n, rn.nv.parent']
        (fun l => if l = n then rblClear rn else rp) hb1 hLs hfLs $$ Hh
        with ⟨⟨Hno, Hpo, -⟩, Hbo, Htf, Hrf, Hback⟩
      isimp only [ite_true, if_neg hpln] at Hno Hpo
      have hnl1 : n ∈ (X.setBkt bl (rblStart B n rn)).live := hnl
      have hpl1 : rn.nv.parent' ∈ (X.setBkt bl (rblStart B n rn)).live := hplive
      rw [decide_eq_true hnl1, decide_eq_true hpl1]
      icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
      rw [if_pos (show true = true ∧ (rblClear rn).nv.key' ≠ slice.nil from ⟨rfl, hkey⟩)]
      icases Hkey with #Hkey
      icases (objOwn_live_node _ _ _ _ _).1 $$ Hpo
        with ⟨Hp, Hpins, Hpcap, Hpws, Hpch, Hpchcap, Hpkey⟩
      ihave %Hpsl := ownSlice_len _ _ _ $$ Hpins
      ihave %Hpwl := BigSepL2.bigSepL2_length $$ Hpws
      icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn2⟩
      iStructNamed Hn
      wp_auto
      wp_apply hNum rn.nv.parent' rp.nv (DFrac.own 1) $$ [Hp] as Hp
      · iframe
      ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
      · iPkgInit
      try wp_auto
      rw [decide_eq_true (show sint.Z (W64 1) < sint.Z rp.nv.inodes'.len by
        have : rp.ins.length = rp.ws.length := Hpwl
        have h1 := Hpsl.1; have h2 := Hpsl.2; word)]
      wp_apply hAssert
      try wp_auto
      ihave Hn : (n ↦ (rblClear rn).nv : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn2
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Hpo : objOwn (X.setBkt bl (rblStart B n rn)).v rn.nv.parent' (DFrac.own 1) true
          (.node bl rp) $$ [Hp Hpins Hpcap Hpws Hpch Hpchcap Hpkey]
      · iapply (objOwn_live_node _ _ _ _ _).2
        isimp only [true_and] at Hpkey
        simp only [eq_self_iff_true, true_and]
        iframe
      wp_apply hIdx (X.setBkt bl (rblStart B n rn)).v rn.nv.parent' bl rp (DFrac.own 1) wq n
        (rblClear rn).nv (DFrac.own 1) (rblClear rn).ksrc (rblClear rn).key hncp.2.2.2.1
        hncp.2.2.2.2.2.1 hks Hbase $$ [Hpo Hcells Hn Hkey] as ⟨Hpo, Hcells, Hn⟩
      · iframe; iframe #
      -- the heap closed again (nothing changed)
      ihave Hh := Hback $$ %(rblStart B n rn) %(fun l => if l = n then rblClear rn else rp) []
        [Hn Hins Hcap Hws Hch Hchcap Hpo] [Hbo] [Htf] [Hrf]
      · ipureintro
        refine ⟨hfLs, fun _ _ => rfl, rfl, ?_⟩
        intro l hl
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
        isplitl [Hpo]
        · simp only [if_neg hpln]
          rw [decide_eq_true hpl1]
          simp only [WX.setBkt_v]
          iexact Hpo
        iapply BigSepL.bigSepL_nil.2; iempintro
      · iexact Hbo
      · iexact Htf
      · iexact Hrf
      have hXX : (X.setBkt bl (rblStart B n rn)).setBkt bl (rblStart B n rn) =
          X.setBkt bl (rblStart B n rn) := by
        simp only [WX.setBkt, GMap.insert_insert]
      rw [hXX]
      ihave Hw : wtxW K tx r m (X.setBkt bl (rblStart B n rn)) $$
        [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
      · iapply (wtxW_split K tx r m _).2; unfold wtxCore
        simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc]
        iframe; iframe #; ipureintro; exact Hr
      rw [hidx]
      have hnlc : ∀ lc, ((X.setBkt bl (rblStart B n rn)).t.objs !! lc).isNone →
          (X.setBkt bl (rblStart B n rn)).nloc !! lc = none := by
        intro lc h
        cases hx : (X.setBkt bl (rblStart B n rn)).nloc !! lc with
        | none => rfl
        | some y =>
          have := Hok1.2.2.2.2.1 lc y hx
          rw [Option.isNone_iff_eq_none] at h; rw [h] at this; cases this
      have hil : i < rp.ws.length := (List.getElem?_eq_some_iff.1 hwi).1
      have hnmn : (rblStart B n rn).nm !! wi.pgid = some n := by
        rw [hwp]; exact hn1.2.2.2.2.2.2.2.1
      have hpkd := ((hk1.2.2 _ rp hrp1).2.2.1 hrpbr).2.2
      -- the sibling: `n.nextSibling()` or `n.prevSibling()`
      wp_join iprop(∃ (X2 : WX) (ll lr : Loc) (k : Nat), n_ptr ↦ n ∗ leftNode_ptr ↦ ll ∗
          rightNode_ptr ↦ lr ∗ wtxW K tx r m X2 ∗
          ⌜mgSel X X2 w.fl bl B n rn rn.nv.parent' ll lr k⌝)
        with [n leftNode rightNode Hw] as ⟨%X2, %ll, %lr, %k, n, leftNode, rightNode, Hw, %Hsel⟩
      · -- the first child: the next sibling
        have hi0 : i = 0 := by
          have h : W64 (i : Int) = W64 0 := Hif
          have h1 := Hpsl.1; have h2 := Hpsl.2
          have : rp.ins.length = rp.ws.length := Hpwl
          word
        subst hi0
        obtain ⟨w1, hw1⟩ : ∃ w1, rp.ws[1]? = some w1 :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        ihave %Hready : ⌜(rblStart B n rn).nm !! w1.pgid = none →
            matReady (X.setBkt bl (rblStart B n rn)) (rblStart B n rn) w1.pgid⌝ $$ [Hw]
        · by_cases hnone : (rblStart B n rn).nm !! w1.pgid = none
          · obtain ⟨kind1, pkd⟩ := hpkd
            obtain ⟨pg1, hpg1, -⟩ := (pkd 1 w1 hw1).2 hnone
            ihave %Hmr := wtxW_matReady K tx r m _ (rblStart B n rn) w1.pgid pg1
              (rbl_root_ne _ _ _ _ bl _ _ rp hI1 hb1 hrp1 hrpbr) hI1.2.2.2.2.2.2.1 hpg1
              (by show X.t.pm !! _ = none; rw [hI.1.2.1]; rfl) $$ Hw
            ipureintro; exact fun _ => Hmr
          · ipureintro; exact fun h => absurd h hnone
        try wp_auto
        icases wtxW_nm_acc K tx r m _ bl _ hb1 _ _ rfl rfl $$ Hw with ⟨Hnm, Hw⟩
        ihave %Hnodes := ownMap_not_nil _ _ _ $$ Hnm
        ihave Hw := Hw $$ Hnm
        have hidx1 : wsIdx rp.ws (rblClear rn).key + 1 = 1 := by
          show wsIdx rp.ws rn.key + 1 = 1; rw [hidx]
        wp_apply hNext K tx r m _ bl _ n (rblClear rn) hb1 hr1 hnc.1 hnl hbll Hnodes
          (fun _ => ⟨hkey, hks, rp, hrp1, hrpbr, hncp.1, hplive, hncp.2.2.2.1, hncp.2.2.2.2.2.1,
            fun w h => by
              rw [hidx1, hw1] at h; cases h
              exact ⟨fun l hl => (hc1.2.2.2.2.1 _ l hl).1, Hready⟩⟩)
          (fun h => hc1.2.2.2.2.2.1 h) $$ [Hw] as %s ⟨%X2, Hw, %Hnx⟩
        · iexact Hw
        try wp_auto
        rcases Hnx with ⟨-, -, hnull | ⟨rq, hrq, hlen1⟩⟩ | ⟨rq, w', hrq, hw', hmat⟩
        · exact absurd hnull hpn
        · rw [hrp1] at hrq; cases hrq; rw [hidx1] at hlen1; omega
        rw [hrp1] at hrq; cases hrq
        rw [hidx1, hw1] at hw'; cases hw'
        obtain ⟨B2, rp2, rs, hb2, hrp2, hnm2, hrs2, hI2, hR2, hoth2, hnv2, hws2, -, -, -, -, hold2,
          hnmext, hU2⟩ := rblX_sibMat _ X2 w.fl bl (some n) _ _ rp 1 w1 s hI1 hb1 hrp1 hrpbr hw1 hmat
            (hnlc s)
        try wp_join_done
        iexists X2, n, s, 0
        iframe
        ipureintro
        exact ⟨B2, rp2, rblClear rn, rs, wi, w1, hb2, hrp2, by rw [hnv2]; exact hrpbr,
          by rw [hws2]; exact hwi, by rw [hws2]; exact hw1, hnmext _ _ hnmn, hnm2,
          hold2 n _ (Ne.symm hpln) hr1, hrs2, Or.inl rfl, hold2 n _ (Ne.symm hpln) hr1, hI2, hR2, hoth2,
          hU2⟩
      · -- a later child: the previous sibling
        have hi0 : i ≠ 0 := by intro h; apply Hif; rw [h]; rfl
        obtain ⟨w0, hw0⟩ : ∃ w0, rp.ws[i - 1]? = some w0 :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        ihave %Hready : ⌜(rblStart B n rn).nm !! w0.pgid = none →
            matReady (X.setBkt bl (rblStart B n rn)) (rblStart B n rn) w0.pgid⌝ $$ [Hw]
        · by_cases hnone : (rblStart B n rn).nm !! w0.pgid = none
          · obtain ⟨kind1, pkd⟩ := hpkd
            obtain ⟨pg1, hpg1, -⟩ := (pkd (i - 1) w0 hw0).2 hnone
            ihave %Hmr := wtxW_matReady K tx r m _ (rblStart B n rn) w0.pgid pg1
              (rbl_root_ne _ _ _ _ bl _ _ rp hI1 hb1 hrp1 hrpbr) hI1.2.2.2.2.2.2.1 hpg1
              (by show X.t.pm !! _ = none; rw [hI.1.2.1]; rfl) $$ Hw
            ipureintro; exact fun _ => Hmr
          · ipureintro; exact fun h => absurd h hnone
        icases wtxW_nm_acc K tx r m _ bl _ hb1 _ _ rfl rfl $$ Hw with ⟨Hnm, Hw⟩
        ihave %Hnodes := ownMap_not_nil _ _ _ $$ Hnm
        ihave Hw := Hw $$ Hnm
        have hidx1 : wsIdx rp.ws (rblClear rn).key = i := hidx
        wp_apply hPrev K tx r m _ bl _ n (rblClear rn) hb1 hr1 hnc.1 hnl hbll Hnodes
          (fun _ => ⟨hkey, hks, rp, hrp1, hrpbr, hncp.1, hplive, hncp.2.2.2.1, hncp.2.2.2.2.2.1,
            fun w _ h => by
              rw [hidx1, hw0] at h; cases h
              exact ⟨fun l hl => (hc1.2.2.2.2.1 _ l hl).1, Hready⟩⟩)
          (fun h => hc1.2.2.2.2.2.1 h) $$ [Hw] as %s ⟨%X2, Hw, %Hnx⟩
        · iexact Hw
        try wp_auto
        rcases Hnx with ⟨-, -, hnull | ⟨rq, hrq, h0⟩⟩ | ⟨rq, w', hrq, -, hw', hmat⟩
        · exact absurd hnull hpn
        · rw [hrp1] at hrq; cases hrq; rw [hidx1] at h0; exact absurd h0 hi0
        rw [hrp1] at hrq; cases hrq
        rw [hidx1, hw0] at hw'; cases hw'
        obtain ⟨B2, rp2, rs, hb2, hrp2, hnm2, hrs2, hI2, hR2, hoth2, hnv2, hws2, -, -, -, -, hold2,
          hnmext, hU2⟩ := rblX_sibMat _ X2 w.fl bl (some n) _ _ rp (i - 1) w0 s hI1 hb1 hrp1 hrpbr hw0
            hmat (hnlc s)
        have hi1 : i - 1 + 1 = i := by omega
        try wp_join_done
        iexists X2, s, n, i - 1
        iframe
        ipureintro
        exact ⟨B2, rp2, rs, rblClear rn, w0, wi, hb2, hrp2, by rw [hnv2]; exact hrpbr,
          by rw [hws2]; exact hw0, by rw [hws2, hi1]; exact hwi, hnm2, hnmext _ _ hnmn, hrs2,
          hold2 n _ (Ne.symm hpln) hr1, Or.inr rfl, hold2 n _ (Ne.symm hpln) hr1, hI2, hR2, hoth2,
          hU2⟩
      obtain ⟨B2, rp2, rl, rr, wl, wr, hb2, hrp2, hbr2, hwl, hwr, hll, hlr, hrl, hrr, hn, hrn2, hI2,
        hR2, hoth2, hU2⟩ := Hsel
      -- the merge's facts
      have hB2 := (hI2.2.1 bl B2 hb2).1
      rw [if_pos rfl] at hB2
      obtain ⟨hc2, ⟨bnd2, hk2⟩, ha2, -⟩ := hB2
      obtain ⟨hp1, hp2', hllr, hllp, hlrp, -, hpgr, -, -, h02, -, -, -, -, hpp2⟩ :=
        mg_basic X2.v _ bl B2 _ rp2 k wl wr ll lr rl rr hc2 ha2 hpn hrp2 hbr2 hwl hwr hll hlr hrl hrr
      obtain ⟨hchar, hnd, hkn⟩ :=
        mg_kids X2 w.fl bl (some n) B2 _ rp2 k wl wr ll lr rl rr hI2 hb2 hpn hrp2 hbr2 hwl hwr hll hlr
          hrl hrr
      obtain ⟨hrkey, hrks, hridx, hrfound, hrdel⟩ :=
        mg_rkey X2 w.fl bl (some n) B2 _ rp2 k wl wr ll lr rl rr hI2 hb2 hpn hrp2 hbr2 hwl hwr hll hlr
          hrl hrr
      have hcl := hc2.2.2.2.2.2.2.2.1 ll rl hrl
      have hcr := hc2.2.2.2.2.2.2.2.1 lr rr hrr
      have hcp := hc2.2.2.2.2.2.2.2.1 _ rp2 hrp2
      have hlive2 : ∀ y ry, B2.ns !! y = some ry → y ∈ X2.live :=
        fun y ry h => (hI2.2.1 bl B2 hb2).2.2.2.2 y ry h
      -- open the parent, the siblings and the right node's children
      icases (wtxW_split K tx r m X2).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
      unfold wtxCore
      icases Hc with ⟨-, -, %Hr2, -, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
      ihave %Hok2 := wtxHeap_heapOK tx (DFrac.own 1) _ $$ Hh
      icases wtxHeap_setBkt_live_acc tx (DFrac.own 1) X2 bl B2 ([rn.nv.parent', ll, lr] ++ kidsOf B2 rr.ws)
        (fun l => if l = rn.nv.parent' then rp2 else if l = ll then rl else if l = lr then rr else
          colKid B2 rr.ws ll rr 0 l) hb2 hnd
        (by
          intro l hl
          simp only [List.cons_append, List.nil_append, List.mem_cons] at hl
          rcases hl with rfl | rfl | rfl | hl
          · simp only [ite_true]; exact hrp2
          · simp only [if_neg hllp, ite_true]; exact hrl
          · simp only [if_neg hlrp, if_neg (Ne.symm hllr), ite_true]; exact hrr
          · obtain ⟨rk, hrk, -⟩ := (hchar l).1 hl
            obtain ⟨h1, h2, h3⟩ := hkn l hl
            simp only [if_neg h1, if_neg h2, if_neg h3, colKid_zero, hrk, Option.getD_some])
        $$ Hh with ⟨HL, Hbo, Htf, Hrf, Hback⟩
      icases (BigSepL.bigSepL_append).1 $$ HL with ⟨⟨Hpo, Hlo, Hro, -⟩, Hks⟩
      isimp only [ite_true, if_neg hllp, if_neg hlrp, if_neg (Ne.symm hllr)] at Hpo Hlo Hro
      rw [decide_eq_true (hlive2 _ _ hrp2), decide_eq_true (hlive2 ll _ hrl),
        decide_eq_true (hlive2 lr _ hrr)]
      icases (objOwn_live_node _ _ _ _ _).1 $$ Hlo
        with ⟨Hl, Hlins, Hlcap, Hlws, Hlch, Hlchcap, Hlkey⟩
      icases (objOwn_live_node _ _ _ _ _).1 $$ Hro
        with ⟨Hrr, Hrins, Hrcap, Hrws, Hrch, Hrchcap, Hrkey⟩
      icases (objOwn_bkt_unf _ _ _ _ _).1 $$ Hbo
        with ⟨Hb1, Hbtx, Hb3, Hb4, Hb5, Hbnodes, Hib, Hnm, Hbm, Hpgo⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hlnn⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hrr with ⟨Hrr, %Hrnn⟩
      iStructNamedSuffix Hl "L"
      iStructNamedSuffix Hrr "R"
      wp_auto
      ihave Hlr : (lr ↦ ({ rr.nv with children' := rr.nv.children' } : node) : IProp GF)
        $$ [bucketR isLeafR unbalancedR spilledR keyR pgidR parentR childrenR inodesR]
      · iapply typedPointsto_combine _ _ _ Hrnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave %Hrwl := BigSepL2.bigSepL2_length $$ Hrws
      have hndk : (kidsOf B2 rr.ws).Nodup := (List.nodup_append.1 hnd).2.1
      ihave Hks := (BigSepL.bigSepL_mono (Ψ := fun _ x => objOwn X2.v x (DFrac.own 1)
          (decide (x ∈ X2.live)) (.node bl (colKid B2 rr.ws ll rr 0 x)))
        (fun {k x} hx => by
          obtain ⟨h1, h2, h3⟩ := hkn x (List.mem_of_getElem? hx)
          simp only [if_neg h1, if_neg h2, if_neg h3]
          exact .rfl)) $$ Hks
      -- the reparenting loop over the right node's entries
      ihave %Hrsl0 := ownSlice_len _ _ _ $$ Hrins
      ihave IHl : iprop(∃ (j : w64) (sCl sCr : GoSlice) (csr : List Loc),
          "i" ∷ i_ptr ↦ j ∗
          "childrenL" ∷ ll.[node, go!"children"] ↦ sCl ∗
          "HlchS" ∷ sCl ↦* (rl.cs ++ kidsOf B2 (rr.ws.take (sint.nat j))) ∗
          "HlchcapS" ∷ ownSliceCap Loc sCl (DFrac.own 1) ∗
          "bucketL" ∷ ll.[node, go!"bucket"] ↦ rl.nv.bucket' ∗
          "Hlr" ∷ lr ↦ ({ rr.nv with children' := sCr } : node) ∗
          "HrchS" ∷ sCr ↦* csr ∗ "HrchcapS" ∷ ownSliceCap Loc sCr (DFrac.own 1) ∗
          "Hrins" ∷ rr.nv.inodes' ↦* rr.ins ∗
          "Hrws" ∷ ([∗list] it;w ∈ rr.ins;rr.ws, wOwn X2.v true it w) ∗
          "Hks" ∷ ([∗list] l ∈ kidsOf B2 rr.ws, objOwn X2.v l (DFrac.own 1) (decide (l ∈ X2.live))
            (.node bl (colKid B2 rr.ws ll rr (sint.nat j) l))) ∗
          "Hnm" ∷ B2.bv.nodes' ↦$ B2.nm ∗ "Hbnodes" ∷ bl.[Bucket, go!"nodes"] ↦ B2.bv.nodes' ∗
          "n" ∷ n_ptr ↦ n ∗ "leftNode" ∷ leftNode_ptr ↦ ll ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rr.nv.inodes'.len⌝)
        $$ [i childrenL Hlch Hlchcap bucketL Hlr Hrch Hrchcap Hrins Hrws Hks Hnm Hbnodes n leftNode]
      · iexists W64 0, rl.nv.children', rr.nv.children', rr.cs
        have h0 : sint.nat (W64 0) = 0 := rfl
        rw [h0, show kidsOf B2 (rr.ws.take 0) = [] from rfl, List.append_nil]
        iframe
        ipureintro; exact ⟨Int.le_refl _, Hrsl0.2⟩
      repeat (irename : ("_" ∷ True : IProp GF) => Htriv; iclear Htriv)
      repeat (irename : (True : IProp GF) => Htriv; iclear Htriv)
      wp_for IHl
      wp_if_destruct
      · have Hlt : sint.Z j < sint.Z rr.nv.inodes'.len := Hif
        ihave %Hrsl := ownSlice_len _ _ _ $$ Hrins
        have Hjn : sint.nat j < rr.ins.length := by rw [Hrsl.1]; word
        list_elem rr.ins (sint.nat j) as itj
        obtain ⟨wj, hwj⟩ : ∃ wj, rr.ws[sint.nat j]? = some wj :=
          ⟨_, List.getElem?_eq_getElem (by rw [← Hrwl]; exact Hjn)⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧
          sint.Z j < sint.Z rr.nv.inodes'.len from ⟨Hj.1, Hlt⟩))]
        wp_apply wp_load_slice_index _ (sint.Z j) rr.ins _ itj Hj.1 $$ [Hrins] as Hrins
        · iframe; ipureintro; simpa using Hitj_lookup
        -- `n.bucket`: one of the two nodes'
        iStructNamedSuffix Hlr "R"
        icases pair_field_acc n ll lr hn go!"bucket" bl rl.nv.bucket' rr.nv.bucket' hcl.1 hcr.1
          $$ [bucketL bucketR] with ⟨Hnb, Hnbb⟩
        · isplitl [bucketL]; iexact bucketL; iexact bucketR
        try wp_auto
        icases BigSepL2.bigSepL2_lookup_acc (by simpa using Hitj_lookup) hwj $$ Hrws
          with ⟨Hwj, Hrwsb⟩
        icases (Write.wOwn_live _ _ _).1 $$ Hwj with ⟨%Hfpj, Hwjr⟩
        ihave Hrws := Hrwsb $$ [Hwjr]
        · iapply (Write.wOwn_live _ _ _).2; iframe; ipureintro; exact Hfpj
        wp_apply hPg $$ [$inode] as inode
        rw [Hfpj.2]
        wp_apply wp_map_lookup2 $$ [Hnm] as Hnm
        · iexact Hnm
        try wp_auto
        icases Hnbb $$ Hnb with ⟨bucketL, bucketR⟩
        ihave Hlr : (lr ↦ ({ rr.nv with children' := sCr } : node) : IProp GF)
          $$ [bucketR isLeafR unbalancedR spilledR keyR pgidR parentR childrenR inodesR]
        · iapply typedPointsto_combine _ _ _ Hrnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        rcases hkk : B2.nm !! wj.pgid with _ | kk
        · -- no node at this entry
          simp only [Option.isSome_none, Option.getD_none, decide_false, Bool.false_eq_true]
          try wp_auto
          wp_for_post
          iframe
          iexists j + W64 1, sCl, sCr, csr
          rw [Hj1, kidsOf_take_succ_eq B2 rr.ws (sint.nat j) wj hwj, hkk]
          simp only [colKid_none B2 rr.ws ll rr (sint.nat j) wj hwj hkk, Option.toList_none,
            List.append_nil]
          iframe
          ipureintro; exact ⟨by word, by word⟩
        · -- the node `kk`: moved from `lr` to `ll`
          simp only [Option.isSome_some, Option.getD_some, _root_.decide_true]
          try wp_auto
          have hkm : kk ∈ kidsOf B2 rr.ws := List.mem_filterMap.2 ⟨wj, List.mem_of_getElem? hwj, hkk⟩
          obtain ⟨hkn1, hkn2, hkn3⟩ := hkn kk hkm
          obtain ⟨rk, hrk, hpk⟩ := (hchar kk).1 hkm
          obtain ⟨idx, hidx'⟩ := List.mem_iff_getElem?.1 hkm
          obtain ⟨hks1, hks2⟩ := colKid_some B2 rr.ws ll rr (sint.nat j) wj hwj kk hkk
          have hfr := colKid_fresh B2 rr.ws ll rr (sint.nat j) wj kk hndk hwj hkk
          rw [hrk, Option.getD_some] at hfr
          icases BigSepL.bigSepL_lookup_acc_impl hidx' $$ Hks with ⟨Hk, Hkb⟩
          isimp only [hfr] at Hk
          rw [decide_eq_true (hlive2 kk rk hrk)]
          icases (objOwn_live_node _ _ _ _ _).1 $$ Hk
            with ⟨Hkn, Hkins, Hkcap, Hkws, Hkch, Hkchcap, Hkkey⟩
          icases typedPointsto_not_null_dup _ _ _ $$ Hkn with ⟨Hkn, %Hknn⟩
          iStructNamedSuffix Hkn "K"
          try wp_auto
          rw [hpk]
          wp_apply hRm lr ({ rr.nv with children' := sCr } : node) csr kk $$ [Hlr HrchS HrchcapS]
            as ⟨%sCr', Hlr, HrchS, HrchcapS⟩
          · iframe
          try wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl ⟨Hsl, -⟩
          wp_apply wp_slice_append $$ [$HlchS $HlchcapS $Hsl] as %sCl' ⟨HlchS, HlchcapS, -⟩
          try wp_auto
          ihave Hk : objOwn X2.v kk (DFrac.own 1) true (.node bl (colRe rk ll))
            $$ [bucketK isLeafK unbalancedK spilledK keyK pgidK parentK childrenK inodesK
              Hkins Hkcap Hkws Hkch Hkchcap Hkkey]
          · iapply (objOwn_live_node _ _ _ _ _).2
            isplitl [bucketK isLeafK unbalancedK spilledK keyK pgidK parentK childrenK inodesK]
            · iapply typedPointsto_combine _ _ _ Hknn
              simp only [TypedPointsto.typedPointstoDef, colRe]
              iframe
            simp only [colRe]
            iframe
          ihave Hks := Hkb $$ %(fun _ l => objOwn X2.v l (DFrac.own 1) (decide (l ∈ X2.live))
              (.node bl (colKid B2 rr.ws ll rr (sint.nat j + 1) l))) [] [Hk]
          · imodintro
            iintro %k' %y %hy %hne H
            have hyk : y ≠ kk := by
              intro he; subst he
              apply hne
              obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hy
              obtain ⟨h1', h2'⟩ := List.getElem?_eq_some_iff.1 hidx'
              exact (List.Nodup.getElem_inj hndk).1 (h2.trans h2'.symm)
            simp only [hks2 y hyk]
            iexact H
          · simp only [hks1, hfr, decide_eq_true (hlive2 kk rk hrk)]
            iexact Hk
          wp_for_post
          iframe
          iexists j + W64 1, sCl', sCr', csr.erase kk
          rw [Hj1, kidsOf_take_succ_eq B2 rr.ws (sint.nat j) wj hwj, hkk]
          simp only [Option.toList_some, List.append_assoc]
          iframe
          ipureintro; exact ⟨by word, by word⟩
      have Hge : ¬ sint.Z j < sint.Z rr.nv.inodes'.len := Hif
      ihave %Hrsl := ownSlice_len _ _ _ $$ Hrins
      have Hjlen : sint.nat j = rr.ws.length := by rw [← Hrwl, Hrsl.1]; word
      rw [Hjlen, List.take_length]
      try simp only [decide_eq_false Hge, _root_.decide_true, ↓reduceIte]
      -- `leftNode.inodes = append(leftNode.inodes, rightNode.inodes...)`
      iStructNamedSuffix Hlr "R"
      rw [hcl.2.1, if_pos rfl]
      try wp_auto
      wp_apply wp_slice_append $$ [$Hlins $Hlcap $Hrins] as %sI ⟨Hlins, Hlcap, Hrins⟩
      try wp_auto
      -- `n.parent.del(rightNode.key)`
      rw [if_pos (show True ∧ rr.nv.key' ≠ slice.nil from ⟨trivial, hrkey⟩)]
      icases Hrkey with #Hrkey
      icases pair_field_acc n ll lr hn go!"parent" rn.nv.parent' rl.nv.parent' rr.nv.parent' hp1 hp2'
        $$ [parentL parentR] with ⟨Hnp, Hnpb⟩
      · isplitl [parentL]; iexact parentL; iexact parentR
      try wp_auto
      have hbase2 : 0 < X2.v.base.addr := by rw [hR2.1]; exact Hbase
      wp_apply node.del.specS hDel X2.v rn.nv.parent' bl rp2 wq rr.nv.key' rr.key rr.ksrc hcp.2.1 hcp.2.2.2.1
        hcp.2.2.2.2.2.1 hrks hbase2 $$ [Hpo Hcells Hrkey] as ⟨Hd, Hcells⟩
      · iframe; iframe #
      icases Hd with (⟨%Hnf, -⟩ | ⟨-, %sI', Hpo⟩)
      · exact absurd hrfound Hnf
      rw [hrdel, hridx]
      icases (objOwn_live_node _ _ _ _ _).1 $$ Hpo
        with ⟨Hp, Hpins, Hpcap, Hpws, Hpch, Hpchcap, Hpkey⟩
      try wp_auto
      -- `n.parent.removeChild(rightNode)`
      wp_apply hRm rn.nv.parent'
        (rp2.withEntsU sI' (rp2.ins.eraseIdx (k + 1)) (rp2.ws.eraseIdx (k + 1)) true).nv rp2.cs lr
        $$ [Hp Hpch Hpchcap] as ⟨%sC', Hp, Hpch, Hpchcap⟩
      · simp only [NRec.withEntsU]; iframe
      icases Hnpb $$ Hnp with ⟨parentL, parentR⟩
      -- `delete(n.bucket.nodes, rightNode.pgid)`
      icases pair_field_acc n ll lr hn go!"bucket" bl rl.nv.bucket' rr.nv.bucket' hcl.1 hcr.1
        $$ [bucketL bucketR] with ⟨Hnb, Hnbb⟩
      · isplitl [bucketL]; iexact bucketL; iexact bucketR
      try wp_auto
      wp_apply (wp_mapDelete (K := w64) (V := Loc) B2.bv.nodes' B2.nm rr.nv.pgid'
        internal.common.Pgid.ty (go.GoType.PointerType node.ty)) $$ [Hnm] as Hnm
      · iexact Hnm
      try wp_auto
      icases Hnbb $$ Hnb with ⟨bucketL, bucketR⟩
      -- close the heap: the bucket after the merge's code (`mgBktL`), `lr` no longer live
      obtain ⟨hcl1, hcl2, hcl3⟩ := mgBktL_close B2 rn.nv.parent' rp2 k ll lr rl rr sI sCl sI' sC' sCr
        csr hrl hrr hp1 hp2' hpp2 hllp hlrp hllr hchar hkn
      have hlv : ∀ y, y ≠ lr → (y ∈ GMap.delete lr X2.live ↔ y ∈ X2.live) := fun y hy => by
        rw [GMap.mem_iff, GMap.mem_iff, GMap.lookup_delete_ne _ (Ne.symm hy)]
      have hlv0 : decide (lr ∈ GMap.delete lr X2.live) = false := by
        rw [decide_eq_false_iff_not, GMap.mem_iff, GMap.lookup_delete]; simp
      have hplv : decide (rn.nv.parent' ∈ GMap.delete lr X2.live) = true :=
        decide_eq_true ((hlv _ (Ne.symm hlrp)).2 (hlive2 _ _ hrp2))
      have hllv : decide (ll ∈ GMap.delete lr X2.live) = true :=
        decide_eq_true ((hlv _ hllr).2 (hlive2 _ _ hrl))
      ihave Hks := (BigSepL.bigSepL_mono (Ψ := fun _ x => objOwn X2.v x (DFrac.own 1)
          (decide (x ∈ GMap.delete lr X2.live))
          (.node bl (mgF B2 rn.nv.parent' rp2 k ll lr rl rr sI sCl sI' sC' sCr csr x)))
        (fun {k' x} hx => by
          obtain ⟨h1, h2, h3⟩ := hkn x (List.mem_of_getElem? hx)
          simp only [mgF, if_neg h1, if_neg h2, if_neg h3, hlv x h3]
          exact .rfl)) $$ Hks
      ihave Hlws := BigSepL2.bigSepL2_app_wand (Φ := fun _ it w => wOwn (GF := GF) X2.v true it w)
        $$ Hlws Hrws
      ihave Hh := Hback $$ %(mgBktL B2 rn.nv.parent' rp2 k ll lr rl rr sI sCl sI' sC' sCr csr)
          %(mgF B2 rn.nv.parent' rp2 k ll lr rl rr sI sCl sI' sC' sCr csr)
          %(GMap.delete lr X2.live) []
          [Hp Hpins Hpcap Hpws Hpch Hpchcap Hpkey bucketL isLeafL unbalancedL spilledL keyL pgidL
            parentL childrenL inodesL Hlins Hlcap Hlws HlchS HlchcapS Hlkey bucketR isLeafR
            unbalancedR spilledR keyR pgidR parentR childrenR inodesR Hks]
          [Hb1 Hbtx Hb3 Hb4 Hb5 Hbnodes Hib Hnm Hbm Hpgo] [Htf] [Hrf]
      · ipureintro
        exact ⟨hcl1, hcl2, rfl, hcl3, fun y hy => hlv y (fun h => hy (by simp [h]))⟩
      · iapply (BigSepL.bigSepL_append).2
        isplitr [Hks]
        · iapply BigSepL.bigSepL_cons.2
          isplitl [Hp Hpins Hpcap Hpws Hpch Hpchcap Hpkey]
          · simp only [mgF, ite_true]
            rw [hplv]
            iapply (objOwn_live_node _ _ _ _ _).2
            dsimp only [mgParent, NRec.withEntsU]
            simp only [hcp.2.1, ↓reduceIte]
            by_cases hpk : rp2.nv.key' = slice.nil
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
            try isimp only [_root_.true_and] at Hpkey
            try simp only [eq_self_iff_true, _root_.true_and]
            iexact Hpkey
          iapply BigSepL.bigSepL_cons.2
          isplitl [bucketL isLeafL unbalancedL spilledL keyL pgidL parentL childrenL inodesL Hlins
            Hlcap Hlws HlchS HlchcapS Hlkey]
          · simp only [mgF, if_neg hllp, ite_true]
            rw [hllv]
            iapply (objOwn_live_node _ _ _ _ _).2
            simp only [mgLeft, hcl.2.1, ↓reduceIte]
            isplitl [bucketL isLeafL unbalancedL spilledL keyL pgidL parentL childrenL inodesL]
            · iapply typedPointsto_combine _ _ _ Hlnn
              simp only [TypedPointsto.typedPointstoDef]
              iframe
            try isimp only [_root_.true_and] at Hlkey
            try simp only [eq_self_iff_true, _root_.true_and]
            iframe
          iapply BigSepL.bigSepL_cons.2
          isplitl [bucketR isLeafR unbalancedR spilledR keyR pgidR parentR childrenR inodesR]
          · simp only [mgF, if_neg hlrp, if_neg (Ne.symm hllr), ite_true]
            rw [hlv0]
            unfold objOwn
            iapply typedPointsto_combine _ _ _ Hrnn
            simp only [TypedPointsto.typedPointstoDef, mgR]
            iframe
          iapply BigSepL.bigSepL_nil.2; iempintro
        · iexact Hks
      · iapply (objOwn_bkt_unf _ _ _ _ _).2
        iframe
        all_goals
          simp only [ite_true, eq_self_iff_true, if_true]
          rw [pageOwn_congr' _ B2 _ rfl rfl rfl rfl]
          iexact Hpgo
      · iframe
      · iframe
      let BL : BRec := mgBktL B2 rn.nv.parent' rp2 k ll lr rl rr sI sCl sI' sC' sCr csr
      let BX : BRec := mgBktX B2 rn.nv.parent' rp2 k ll lr rl rr sI sCl sI' sC'
      have hb3 : ({ X2.setBkt bl BL with live := GMap.delete lr X2.live } : WX).t.bs !! bl =
          some BL := GMap.lookup_insert _ _ _
      ihave Hw : wtxW K tx r m { X2.setBkt bl BL with live := GMap.delete lr X2.live } $$
        [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
      · iapply (wtxW_split K tx r m _).2; unfold wtxCore
        simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc]
        iframe; iframe #; ipureintro; exact Hr2
      -- `rightNode.free()`
      icases wdbW_view_rbl K tx X.v w $$ Hdb with ⟨%Hwv, Hdb⟩
      have hX2v : X2.v = X.v := hR2.1
      have htxid2 : X2.t.mv.txid' = w.wtxid :=
        rblX_wtxid X2 w.fl bl _ w hI2 (by rw [hX2v]; simpa using Hwv)
      obtain ⟨pgc0, -, hp0c⟩ := rbl_node_page X2 w.fl bl (some n) bl B2 lr rr hI2 hb2 hrr h02
      obtain ⟨pgc, hpgc, hlenc, hidc, hflc, hcanc⟩ :=
        rblX_canFree X2 w.fl bl (some n) B2 lr rr hI2 hb2 hrr hp0c
      have hX3n : ({ X2.setBkt bl BL with live := GMap.delete lr X2.live } : WX).node bl lr =
          some (mgR rr sCr csr) := by
        unfold WX.node; rw [hb3]
        show (mgBktL B2 rn.nv.parent' rp2 k ll lr rl rr sI sCl sI' sC' sCr csr).ns !! lr = _
        rw [hcl1 lr (by simp)]; unfold mgF; rw [if_neg hlrp, if_neg (Ne.symm hllr), if_pos rfl]
      wp_apply hFree K tx r m _ w bl lr (mgR rr sCr csr) hX3n hcr.1
        (fun _ => ⟨by show X2.t.pm !! _ = none; rw [hI2.1.2.1]; rfl, htxid2, pgc, hpgc, hlenc, hidc,
          hflc, by rw [← htxid2]; exact hcanc⟩)
        $$ [Hw Hdb] as ⟨%X4, %w4, Hw, Hdb, %Hfr⟩
      · rw [show ({ X2.setBkt bl BL with live := GMap.delete lr X2.live } : WX).v = X.v from hX2v]
        iframe
      obtain ⟨hX4, hw4⟩ : X4 = ({ X2.setBkt bl BL with live := GMap.delete lr X2.live } : WX).setNode
            bl lr (mgDead rr sCr csr) ∧
          w4 = w.withFl (w.fl.freePages w.wtxid rr.nv.pgid' (1 + pageOverflow pgc)) := by
        rcases Hfr with ⟨h0, -, -⟩ | ⟨pg', -, hpg', hX4, hw4⟩
        · exact absurd h0 hp0c
        · have := hpgc.symm.trans hpg'; cases this; exact ⟨hX4, hw4⟩
      subst hX4 hw4
      try wp_auto
      -- `n.parent` read (`n` is the left node, or the right one, dead but its struct kept)
      icases (wtxW_split K tx r m _).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
      unfold wtxCore
      icases Hc with ⟨-, -, -, -, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
      ihave %Hok4 := wtxHeap_heapOK tx (DFrac.own 1) _ $$ Hh
      let B4 : BRec := { BL with ns := BL.ns.insert lr (mgDead rr sCr csr) }
      have hb4 : (({ X2.setBkt bl BL with live := GMap.delete lr X2.live } : WX).setNode
          bl lr (mgDead rr sCr csr)).t.bs !! bl = some B4 := by
        unfold WX.setNode; rw [hb3]; exact GMap.lookup_insert _ _ _
      have hnrec : ∃ rN, B4.ns !! n = some rN ∧ rN.nv.parent' = rn.nv.parent' := by
        rcases hn with h | h
        · refine ⟨mgLeft rl rr (kidsOf B2 rr.ws) sI sCl, ?_, hp1⟩
          rw [h]
          show (BL.ns.insert lr _) !! ll = _
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hllr), hcl1 ll (by simp)]
          unfold mgF; rw [if_neg hllp, if_pos rfl]
        · exact ⟨mgDead rr sCr csr, by rw [h]; exact GMap.lookup_insert _ _ _, hp2'⟩
      obtain ⟨rN, hrN, hrNp⟩ := hnrec
      have Ho4 := objs_node _ bl _ n _ Hok4.2.1 hb4 hrN
      icases wtxHeap_node_ptr_acc tx (DFrac.own 1) _ bl n rN Ho4 $$ Hh with ⟨Hn, Hback⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn5⟩
      iStructNamed Hn
      wp_auto
      ihave Hn : (n ↦ rN.nv : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn5
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Hh := Hback $$ Hn
      rw [hrNp]
      -- `lr` goes dead: the records after the merge
      have hns5 : BX.ns = GMap.delete lr B4.ns := by
        show _ = GMap.delete lr ((BX.ns.insert lr (mgR rr sCr csr)).insert lr (mgDead rr sCr csr))
        rw [GMap.insert_insert, GMap.delete_insert_eq, GMap.delete_notin _ _ (by
          show (mgBkt B2 _ ll lr _ _ _).ns !! lr = none
          rw [mg_ns, if_neg hlrp, if_neg (Ne.symm hllr), if_pos rfl])]
      ihave Hh := wtxHeap_kill_node tx (DFrac.own 1) _ bl B4 BX lr (mgDead rr sCr csr) hb4
        (GMap.lookup_insert _ _ _) rfl rfl rfl rfl rfl rfl rfl hns5 $$ Hh
      have hK : (({ X2.setBkt bl BL with live := GMap.delete lr X2.live } : WX).setNode
            bl lr (mgDead rr sCr csr)).kill bl BX lr (mgDead rr sCr csr) =
          X2.kill bl BX lr (mgDead rr sCr csr) := by
        unfold WX.setNode; rw [hb3]
        simp only [WX.kill, WX.setBkt, GMap.insert_insert, GMap.delete_idemp]
      rw [hK]
      have hsl2 : 0 ≤ sint.Z rn.nv.inodes'.len := Hsl.2
      have hne' : 0 < (rl.ws ++ rr.ws).length := by
        have h0 : 0 < rn.ws.length := by rw [hlen]; word
        rw [List.length_append]
        rcases hn with h | h
        · rw [h, hrl] at hrn2; cases hrn2; simp only [rblClear]; omega
        · rw [h, hrr] at hrn2; cases hrn2; simp only [rblClear]; omega
      obtain ⟨hI4, hR4, -, hU4⟩ := rblX_mg X2 w.fl bl B2 n rn.nv.parent' rp2 k wl wr ll lr rl rr sI
        sCl sI' sC' sCr csr pgc hI2 hb2 hn hpn hrp2 hbr2 hwl hwr hll hlr hrl hrr hne' hpgc
      have hfl : w.fl.freePages X2.t.mv.txid' rr.nv.pgid' (1 + pageOverflow pgc) =
          (w.withFl (w.fl.freePages w.wtxid rr.nv.pgid' (1 + pageOverflow pgc))).fl := by
        rw [htxid2]; rfl
      rw [hfl] at hI4 hR4
      ihave Hw : wtxW K tx r m (X2.kill bl BX lr (mgDead rr sCr csr)) $$
        [Hh Hfills Hbk Hnl Hdbf Hview Hst Hcells Hmap]
      · iapply (wtxW_split K tx r m _).2; unfold wtxCore
        simp only [WX.setBkt_v, WX.setBkt_handles, WX.setBkt_nloc, WX.kill_v, WX.kill_handles,
          WX.kill_nloc, WX.setNode_v, WX.setNode_handles, WX.setNode_nloc]
        iframe; iframe #; ipureintro; exact Hr2
      -- `n.parent.rebalance()`
      have hpX : BX.ns !! rn.nv.parent' = some (mgParent rp2 (k + 1) lr sI' sC') := by
        show (mgBkt B2 _ ll lr _ _ _).ns !! _ = _
        rw [mg_ns, if_pos rfl]
      have hfp' : bl = (X2.kill bl BX lr (mgDead rr sCr csr)).rl ∨
          ((X2.kill bl BX lr (mgDead rr sCr csr)).handles !! bl).isSome := by
        show bl = X2.rl ∨ (X2.handles !! bl).isSome
        rw [hR2.2.2.1, hR2.2.1]; exact hfp
      wp_apply IH $$ %K %tx %r %m %(X2.kill bl BX lr (mgDead rr sCr csr))
        %(w.withFl (w.fl.freePages w.wtxid rr.nv.pgid' (1 + pageOverflow pgc))) %bl %BX
        %rn.nv.parent' %(mgParent rp2 (k + 1) lr sI' sC') %(some rn.nv.parent') [] [Hw Hdb]
        as ⟨%X5, %fl5, Hw, Hdb, %Hp5⟩
      · ipureintro
        exact ⟨hI4, GMap.lookup_insert _ _ _, hpX, Or.inr ⟨rfl, rfl⟩, hfp'⟩
      · isplitl [Hw]
        · iexact Hw
        simp only [WX.kill_v, WX.setNode_v, WX.setBkt_v]
        iexact Hdb
      try wp_auto
      obtain ⟨h5I, h5R, h5S⟩ := Hp5
      have hmv : X2.t.mv = X.t.mv := hR2.2.2.2.2.2.1
      rw [hmv] at hR4
      have e5 : (X2.kill bl BX lr (mgDead rr sCr csr)).t.mv.txid' = X.t.mv.txid' := by
        show X2.t.mv.txid' = _; rw [hmv]
      rw [e5] at h5R
      iapply HΦ
      iexists X5, fl5
      iframe Hw
      isplitl [Hdb]
      · rw [← WDb.withFl_withFl w _ fl5]
        try simp only [WX.kill_v]
        rw [← hX2v]
        iexact Hdb
      ipureintro
      refine ⟨h5I, rblRel_trans _ _ _ _ _ _ _ hR1 (rblRel_trans _ _ _ _ _ _ _ hR2
        (rblRel_trans _ _ _ _ _ _ _ hR4 h5R)), ?_, ?_⟩
      · intro bl' hne
        rw [h5S.1 bl' hne]
        show (X2.t.bs.insert bl _) !! bl' = _
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hne), hoth2 bl' hne]
        show (X.t.bs.insert bl _) !! bl' = _
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]
      · intro B0 B5 h0 h5
        rw [hb] at h0; cases h0
        have he := hR2.2.2.2.2.2.2.2.2.2.1 bl _ B2 hb1 hb2
        exact rblStep_comp B BX B5 n rn.nv.parent'
          (rblPre_mg B B2 BX n rn.nv.parent' lr rn he hU2 ⟨rfl, rfl, rfl⟩ hU4)
          (h5S.2 BX B5 (GMap.lookup_insert _ _ _) h5)


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
