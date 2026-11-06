/-
U7p (`notes/bbolt-proof-plan.md`): **`DeleteBucket`'s post, the records' facts** (`dbk_core`, for
`Write/DelBktPure`'s `dbk_post`): after the deletion's middle records (`delMid`), the
materializations of `Cursor.node` (`matGrow`) and `node.del` of `n` in the root's leaf, the records
are well-formed, hold the data without `n`, have the generations of `T.dropBkt n`, the writer's
carried facts, and the view and meta copy kept. Across `delMid`: the live buckets stay reachable
(the root caches every other bucket: `liveReach_delMid`), and the data but at `n` is kept
(`wtxData_delMid`: the logical trees of the root and the other buckets are kept, `leaves_congr`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktPost
public import Proof.go_etcd_io.bbolt.Write.WOkLeafPut
public import Proof.go_etcd_io.bbolt.Write.DelBkt
public import Proof.go_etcd_io.bbolt.Write.DelBktPath
public import Proof.go_etcd_io.bbolt.Read.PubWBkt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section delpost2
variable [GooseExts]

/-- **The live buckets stay reachable** across `delMid` (the root caches every bucket but itself). -/
theorem liveReach_delMid (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec)
    (hok1 : wOK X1) (hwr1 : wrFacts X1) (hR1 : X1.t.bs !! X1.rl = some R1)
    (hn : R1.bm !! n = some c) : liveReach (delMid X1 c C R1 n D) := by
  have hcr : c ≠ X1.rl := hwr1.2.2 R1 hR1 n c hn
  obtain ⟨rB, rN⟩ := hwr1.1
  have hinv : ∀ x, bktReach X1 x → x = X1.rl ∨ ∃ k, R1.bm !! k = some x := by
    intro x h
    induction h with
    | root => exact Or.inl rfl
    | child bl c' B k hB hk _ ih =>
      rcases ih with e | ⟨k', hk'⟩
      · subst e; rw [hR1] at hB; cases hB; exact Or.inr ⟨k, hk⟩
      · exact (bm_nonroot X1 hok1 bl B hB (hwr1.2.2 R1 hR1 k' bl hk') k c' hk).elim
  have hYrl : (delMid X1 c C R1 n D).t.bs !! X1.rl = some (bUnopen R1 n) := by
    rw [delMid_bs, if_neg hcr, if_pos rfl]
  refine ⟨fun bl B hB hl => ?_, fun bl B l r hB hr hl => ?_⟩
  · obtain ⟨hbc, hcase⟩ := delMid_back X1 c C R1 n D hcr bl B hB
    have hl1 := ((delMid_liveB X1 c C R1 n D bl).1 hl).2
    rcases hcase with ⟨e, -⟩ | ⟨hbr, hB0⟩
    · subst e; exact bktReach.root
    · rcases hinv bl (rB bl B hB0 hl1) with e | ⟨k, hk⟩
      · exact absurd e hbr
      · have hkn : k ≠ n := by
          intro e; subst e; rw [hn] at hk; cases hk; exact hbc rfl
        refine bktReach.child X1.rl bl (bUnopen R1 n) k hYrl ?_ bktReach.root
        show (GMap.delete n R1.bm) !! k = some bl
        rw [GMap.lookup_delete_ne _ (Ne.symm hkn)]; exact hk
  · obtain ⟨-, hcase⟩ := delMid_back X1 c C R1 n D hcr bl B hB
    have hl1 := ((delMid_live X1 c C R1 n D l).1 hl).1
    rcases hcase with ⟨rfl, rfl⟩ | ⟨-, hB0⟩
    · obtain ⟨rt, h1, h2⟩ := rN X1.rl R1 l r hR1 hr hl1
      exact ⟨rt, PubW.nodeRootIn_congr (B := R1) (B' := bUnopen R1 n) rfl h1,
        PubW.descIn_congr (B := R1) (B' := bUnopen R1 n) rfl h2⟩
    · exact rN bl B l r hB0 hr hl1

/-- **The data but at `n` is kept** across `delMid`. -/
theorem wtxData_delMid (T : TxView) (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec)
    (hok1 : wOK X1) (hokY : wOK (delMid X1 c C R1 n D)) (hwr1 : wrFacts X1)
    (hgens1 : gensOK T X1) (hR1 : X1.t.bs !! X1.rl = some R1) (hn : R1.bm !! n = some c) :
    (wtxData (delMid X1 c C R1 n D)).delete n = (wtxData X1).delete n := by
  have hcr : c ≠ X1.rl := hwr1.2.2 R1 hR1 n c hn
  have hYrl : (delMid X1 c C R1 n D).t.bs !! X1.rl = some (bUnopen R1 n) := by
    rw [delMid_bs, if_neg hcr, if_pos rfl]
  have hsame : ∀ k B, k ≠ c → k ≠ X1.rl → X1.t.bs !! k = some B →
      (delMid X1 c C R1 n D).t.bs !! k = some B := by
    intro k B h1 h2 h3; rw [delMid_bs, if_neg (Ne.symm h1), if_neg h2]; exact h3
  have hLR := ltree_congr_bkt X1 (delMid X1 c C R1 n D) X1.rl R1 (bUnopen R1 n) rfl hR1 hYrl
    (sameTreeB_bm R1 _)
  have hPR := rootPid_congr_bkt X1 (delMid X1 c C R1 n D) X1.rl R1 (bUnopen R1 n) rfl hR1 hYrl
    (sameTreeB_bm R1 _)
  have hleavesR := leaves_congr X1 (delMid X1 c C R1 n D) X1.rl hok1 hokY (by rw [hR1]; rfl)
    (by rw [hYrl]; rfl) hLR hPR
  have hroot : rootEnts (delMid X1 c C R1 n D) = rootEnts X1 := by
    unfold rootEnts; exact congrArg _ hleavesR
  have hloc : ∀ m, m ≠ n → bktLoc (delMid X1 c C R1 n D) m = bktLoc X1 m := by
    intro m hm
    unfold bktLoc
    rw [show (delMid X1 c C R1 n D).rl = X1.rl from rfl, hYrl, hR1]
    simp only [Option.bind_some]
    exact GMap.lookup_delete_ne _ (Ne.symm hm)
  have hdo : ∀ m v, m ≠ n → bktDataOf (delMid X1 c C R1 n D) m v = bktDataOf X1 m v := by
    intro m v hm
    rw [bktDataOf_eq, bktDataOf_eq, hloc m hm]
    cases hc : bktLoc X1 m with
    | none => rfl
    | some c' =>
      simp only
      unfold bktLoc at hc; rw [hR1] at hc; simp only [Option.bind_some] at hc
      have hc'c : c' ≠ c := by
        intro e; subst e
        have h1 := hgens1.2.1 n c' (by unfold bktLoc; rw [hR1]; exact hn)
        have h2 := hgens1.2.1 m c' (by unfold bktLoc; rw [hR1]; exact hc)
        rw [h1] at h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        exact hm h2.1.symm
      have hc'r : c' ≠ X1.rl := hwr1.2.2 R1 hR1 m c' hc
      obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.1 ((hok1.1.2.2.2.2.2 X1.rl R1 hR1).2 m c' hc)
      have hYB' := hsame c' B' hc'c hc'r hB'
      have hst : sameTreeB B' B' := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hl := leaves_congr X1 (delMid X1 c C R1 n D) c' hok1 hokY (by rw [hB']; rfl)
        (by rw [hYB']; rfl) (ltree_congr_bkt X1 _ c' B' B' rfl hB' hYB' hst)
        (rootPid_congr_bkt X1 _ c' B' B' rfl hB' hYB' hst)
      unfold lbktEnts; rw [hl]
  apply GMap.ext; intro m
  show (GMap.delete n (wtxData (delMid X1 c C R1 n D))) !! m = (GMap.delete n (wtxData X1)) !! m
  rw [GMap.lookup_delete_iff, GMap.lookup_delete_iff]
  split
  · rfl
  · rename_i hm
    rw [wtxData_lookup, wtxData_lookup]
    unfold bktData
    rw [hroot]
    cases (rootEnts X1).find? (fun e => decide (e.1 = m)) with
    | none => rfl
    | some e => simp only [Option.map_some]; rw [hdo m e.2 (Ne.symm hm)]

/-- **`DeleteBucket`'s post, the records' facts** (see the module doc). -/
theorem dbk_core (T : TxView) (X X1 X6 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec)
    (l : Loc) (B6 : BRec) (rl : NRec) (s : GoSlice) (ins : List Inode)
    (hcur : T.cur = wtxData X) (hok1 : wOK X1) (hd1 : wtxData X1 = wtxData X)
    (hR1 : X1.t.bs !! X.rl = some R1) (hn : R1.bm !! n = some c) (hC : X1.t.bs !! c = some C)
    (hrl1 : X1.rl = X.rl) (hv1 : X1.v = X.v) (hmv1 : X1.t.mv = X.t.mv) (hgens1 : gensOK T X1)
    (hwr1 : wrFacts X1) (hdo1 : objsDisj X1.t) (hpx : pagesExt X1.v.pages)
    (hmg : matGrow (delMid X1 c C R1 n D) X6 X.rl) (hok6 : wOK X6) (hd6 : objsDisj X6.t)
    (hB6 : X6.t.bs !! X.rl = some B6) (hrl : B6.ns !! l = some rl) (hlf : leafFor X6 X.rl n l)
    (hins : ins.length = (wsDelAt rl.ws n).length) :
    wOK (X6.setNode X.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)) ∧
      wtxData (X6.setNode X.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)) = T.cur.delete n ∧
      gensOK (T.dropBkt n) (X6.setNode X.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)) ∧
      wrFacts (X6.setNode X.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)) ∧
      (X6.setNode X.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)).v = X.v ∧
      (X6.setNode X.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)).t.mv = X.t.mv := by
  rw [← hrl1] at hR1 hmg hB6 hlf ⊢
  have hcr : c ≠ X1.rl := hwr1.2.2 R1 hR1 n c hn
  have hokY := wOK_delMid T X1 c C R1 n D hok1 hwr1 hgens1 hR1 hn hC hdo1 hpx
  obtain ⟨k1, k2, k3, k4, k5, -, -, k8⟩ := matGrow_keepW hmg
  have hYrl : (delMid X1 c C R1 n D).t.bs !! X1.rl = some (bUnopen R1 n) := by
    rw [delMid_bs, if_neg hcr, if_pos rfl]
  have hbm6 : B6.bm = GMap.delete n R1.bm := by
    obtain ⟨B, hB, e⟩ := k8 X1.rl B6 hB6
    rw [hYrl] at hB; cases hB; exact e
  have h6r : X6.rl = X1.rl := k2
  have hbmn : B6.bm !! n = none := by rw [hbm6]; exact GMap.lookup_delete _ _
  have hnr : ∀ k c', B6.bm !! k = some c' → c' ≠ X1.rl := by
    intro k c' e
    rw [hbm6] at e
    exact hwr1.2.2 R1 hR1 k c' ((GMap.lookup_delete_Some _ _ _ _).1 e).2
  obtain ⟨B', r', bnd, hB', hr', hleaf, hbk, hkin⟩ := id hlf
  rw [hB6] at hB'; cases hB'; rw [hrl] at hr'; cases hr'
  have hpw : wsPw rl.ws :=
    wsSorted_pw _ ((wOK_bktClean X6 hok6 X1.rl B6 hB6).2.2.2.2.2.2.2.1 l rl hrl).2.2.2.1
  -- the final records
  have hXf := setNode_eqT X6 X1.rl l B6 (rl.withEntsU s ins (wsDelAt rl.ws n) true) hB6
  have hlocf : ∀ m, bktLoc (X6.setNode X1.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)) m =
      (GMap.delete n R1.bm) !! m := by
    intro m
    rw [hXf]
    unfold bktLoc
    show ((X6.t.bs.insert X1.rl { B6 with ns := B6.ns.insert l _ }) !! X6.rl).bind _ = _
    rw [h6r, GMap.lookup_insert]
    simp only [Option.bind_some]
    rw [hbm6]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h6r] at hB6 hlf ⊢
    exact wOK_delRoot X6 l B6 rl n s ins hok6 hd6 hlf hB6 hrl hbmn (by rw [h6r]; exact hnr) hins
  · rw [wtxData_setNode X6 X1.rl l B6 rl (rl.withEntsU s ins (wsDelAt rl.ws n) true) hB6 hrl rfl]
    show wtxData (X6.withWs X1.rl l (wsDelAt rl.ws n)) = _
    rw [wsDelAt_wsDel rl.ws n hpw, ← h6r]
    rw [← h6r] at hB6
    rw [wtxData_delRoot X6 l B6 rl bnd n hok6 hB6 hrl hleaf hbk hkin (fun m c' hm => by
      unfold bktLoc at hm; rw [hB6] at hm; simp only [Option.bind_some] at hm
      rw [h6r]; exact hnr m c' hm)]
    rw [wtxData_matGrow _ X6 _ hokY hmg, wtxData_delMid T X1 c C R1 n D hok1 hokY hwr1 hgens1 hR1 hn,
      hd1, hcur]
  · have hh : (X6.setNode X1.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)).handles =
        X1.handles := by rw [hXf]; exact k1
    refine gensOK_dropBkt T X1 _ n hh (fun m hm => ?_) (by rw [hlocf]; exact GMap.lookup_delete _ _)
      hgens1
    rw [hlocf, GMap.lookup_delete_ne _ (Ne.symm hm)]
    unfold bktLoc; rw [hR1]; rfl
  · refine ⟨liveReach_setNode X6 X1.rl l B6 rl _ hB6 hrl rfl rfl
      (liveReach_matGrow hmg hokY (liveReach_delMid X1 c C R1 n D hok1 hwr1 hR1 hn)), ?_, ?_⟩
    · rw [hXf]; show X6.t.t.commitHandlers' = _; rw [k4]; exact hwr1.2.1
    · intro B hB k c' hk
      rw [hXf] at hB
      change (X6.t.bs.insert X1.rl { B6 with ns := B6.ns.insert l _ }) !! X6.rl = some B at hB
      rw [h6r, GMap.lookup_insert] at hB
      cases hB
      rw [hXf]; show c' ≠ X6.rl; rw [h6r]
      exact hnr k c' hk
  · rw [hXf]; show X6.v = _; rw [k3, ← hv1]; rfl
  · rw [hXf]; show X6.t.mv = _; rw [k5, ← hmv1]; rfl

end delpost2

end Write

end bbolt
end EtcdGrove
end Perennial
