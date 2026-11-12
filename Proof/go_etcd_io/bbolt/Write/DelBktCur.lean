/-
U7q (`notes/bbolt-proof-plan.md`): **the cursor's writer facts across `DeleteBucket`**
(`wrCurFacts`, for `Write/DelBktWp.deleteOK`'s last conjunct). `delMid` keeps them at `T`
(`wrCurFacts_delMid`: the root's entry `n` still there, the child out of `liveB` but in `deadB`);
the root leaf's delete of `n` moves them to `T.dropBkt n` (`wrCurFacts_dropRoot`: no entry `n`
left, so its recorded root is `0`, `wRoot` of the bumped generation).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktFlvCov
public import Proof.go_etcd_io.bbolt.Write.CreateBktData

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section delbktcur
variable [GooseExts]

/-- **`delMid` keeps `wrCurFacts`.** -/
theorem wrCurFacts_delMid (T : TxView) (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec)
    (hok1 : wOK X1) (hok5 : wOK (delMid X1 c C R1 n D)) (hwr1 : wrFacts X1) (hgens1 : gensOK T X1)
    (hR1 : X1.t.bs !! X1.rl = some R1) (hn : R1.bm !! n = some c) (hw : wrCurFacts T X1) :
    wrCurFacts T (delMid X1 c C R1 n D) := by
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := hw
  have hcr : c ≠ X1.rl := hwr1.2.2 R1 hR1 n c hn
  have hYrl : (delMid X1 c C R1 n D).t.bs !! X1.rl = some (bUnopen R1 n) := by
    rw [delMid_bs, if_neg hcr, if_pos rfl]
  have hst : ∀ bl, bl ≠ c → ∀ B, X1.t.bs !! bl = some B →
      ∃ B', (delMid X1 c C R1 n D).t.bs !! bl = some B' ∧ sameTreeB B B' := by
    intro bl hbc B hB
    rw [delMid_bs, if_neg (Ne.symm hbc)]
    by_cases hr : bl = X1.rl
    · subst hr; rw [if_pos rfl]; rw [hR1] at hB; cases hB; exact ⟨_, rfl, sameTreeB_bm R1 _⟩
    · rw [if_neg hr]; exact ⟨B, hB, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hback : ∀ bl B', (delMid X1 c C R1 n D).t.bs !! bl = some B' →
      bl ≠ c ∧ ∃ B, X1.t.bs !! bl = some B ∧ sameTreeB B B' := by
    intro bl B' hB'
    obtain ⟨hbc, hcase⟩ := delMid_back X1 c C R1 n D hcr bl B' hB'
    refine ⟨hbc, ?_⟩
    rcases hcase with ⟨rfl, rfl⟩ | ⟨-, hB0⟩
    · exact ⟨R1, hR1, sameTreeB_bm R1 _⟩
    · exact ⟨B', hB0, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hroot : rootEnts (delMid X1 c C R1 n D) = rootEnts X1 := by
    have hLR := ltree_congr_bkt X1 (delMid X1 c C R1 n D) X1.rl R1 (bUnopen R1 n) rfl hR1 hYrl
      (sameTreeB_bm R1 _)
    have hPR := rootPid_congr_bkt X1 (delMid X1 c C R1 n D) X1.rl R1 (bUnopen R1 n) rfl hR1 hYrl
      (sameTreeB_bm R1 _)
    unfold rootEnts
    exact congrArg _ (leaves_congr X1 (delMid X1 c C R1 n D) X1.rl hok1 hok5 (by rw [hR1]; rfl)
      (by rw [hYrl]; rfl) hLR hPR)
  refine ⟨⟨fun l b p hl hb => ?_, fun b B c' l hB hb hc => ?_⟩, fun m b hm => ?_,
    fun m => ?_, fun l b p hl => ?_⟩
  · obtain ⟨hbc, hb1⟩ := (delMid_liveB X1 c C R1 n D b).1 hb
    obtain ⟨B0, hB0, hm0⟩ := h1 l b p hl hb1
    obtain ⟨B', hB', hs⟩ := hst b hbc B0 hB0
    exact ⟨B', hB', by rw [hs.2.2.1]; exact hm0⟩
  · obtain ⟨-, B0, hB0, hs⟩ := hback b B hB
    have hb1 := ((delMid_liveB X1 c C R1 n D b).1 hb).2
    exact h2 b B0 c' l hB0 hb1 (by rw [← hs.2.2.1]; exact hc)
  · have hm' : (GMap.delete n R1.bm) !! m = some b := by
      unfold bktLoc at hm
      rw [show (delMid X1 c C R1 n D).rl = X1.rl from rfl, hYrl] at hm
      exact hm
    have hmn : m ≠ n := by
      intro e; subst e; rw [GMap.lookup_delete] at hm'; cases hm'
    rw [GMap.lookup_delete_ne _ (Ne.symm hmn)] at hm'
    have hloc1 : bktLoc X1 m = some b := by unfold bktLoc; rw [hR1]; exact hm'
    have hbc : b ≠ c := by
      intro e; subst e
      have e1 := hgens1.2.1 n b (by unfold bktLoc; rw [hR1]; exact hn)
      have e2 := hgens1.2.1 m b hloc1
      rw [e1] at e2
      simp only [Option.some.injEq, Prod.mk.injEq] at e2
      exact hmn e2.1.symm
    obtain ⟨B0, hB0⟩ := Option.isSome_iff_exists.1 ((hok1.1.2.2.2.2.2 X1.rl R1 hR1).2 m b hm')
    obtain ⟨B', hB', hs⟩ := hst b hbc B0 hB0
    rw [rootPid_congr_bkt X1 (delMid X1 c C R1 n D) b B0 B' rfl hB0 hB' hs]
    exact h3 m b hloc1
  · rw [rootEntRef_of_rootEnts _ _ hroot]; exact h4 m
  · have hb1 := h5 l b p hl
    unfold WTx.bobjs at hb1 ⊢
    rw [GMap.lookup_union] at hb1 ⊢
    by_cases hbc : c = b
    · subst hbc
      rw [delMid_bs_c, delMid_deadB, if_pos rfl]; rfl
    · rw [delMid_deadB, if_neg hbc]
      cases hB : X1.t.bs !! b with
      | none => rw [hB] at hb1; cases e : (delMid X1 c C R1 n D).t.bs !! b <;> simp_all
      | some B0 =>
        obtain ⟨B', hB', -⟩ := hst b (Ne.symm hbc) B0 hB
        rw [hB']; rfl

/-- **The root leaf's delete of `n` moves `wrCurFacts` to `T.dropBkt n`** (`n` not cached). -/
theorem wrCurFacts_dropRoot (T : TxView) (X6 : WX) (n : GoString) (l : Loc) (B6 : BRec) (rl : NRec)
    (s : GoSlice) (ins : List Inode)
    (hok6 : wOK X6) (hB6 : X6.t.bs !! X6.rl = some B6) (hrl : B6.ns !! l = some rl)
    (hlf : leafFor X6 X6.rl n l) (hbmn : B6.bm !! n = none) (hw : wrCurFacts T X6) :
    wrCurFacts (T.dropBkt n) (X6.setNode X6.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)) := by
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := hw
  obtain ⟨B', r0, bnd, hB', hr', hleaf, hbk, hkin⟩ := id hlf
  rw [hB6] at hB'; cases hB'; rw [hrl] at hr'; cases hr'
  have hXf : X6.setNode X6.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true) =
      X6.setBkt X6.rl { B6 with ns := B6.ns.insert l (rl.withEntsU s ins (wsDelAt rl.ws n) true) } := by
    unfold WX.setNode; rw [hB6]
  generalize hr' : rl.withEntsU s ins (wsDelAt rl.ws n) true = r' at hXf ⊢
  have hlf' : r'.nv.isLeaf' = rl.nv.isLeaf' := by rw [← hr']; rfl
  have hws' : r'.ws = wsDelAt rl.ws n := by rw [← hr']; rfl
  have hlk : ∀ b, (X6.setNode X6.rl l r').t.bs !! b =
      if b = X6.rl then some { B6 with ns := B6.ns.insert l r' } else X6.t.bs !! b := by
    intro b; rw [hXf]; unfold WX.setBkt; simp only
    by_cases hb : b = X6.rl
    · subst hb; rw [if_pos rfl, GMap.lookup_insert]
    · rw [if_neg hb, GMap.lookup_insert_ne _ _ (Ne.symm hb)]
  have hmap : ∀ {β : Type} (f : BRec → β), (∀ D : BRec, f { D with ns := D.ns.insert l r' } = f D) →
      ∀ b, ((X6.setNode X6.rl l r').t.bs !! b).map f = (X6.t.bs !! b).map f := by
    intro β f hf b
    rw [hlk]; split
    · rename_i e; subst e; rw [hB6]; simp only [Option.map_some, hf]
    · rfl
  have hv : (X6.setNode X6.rl l r').v = X6.v := by rw [hXf]; rfl
  have hrl7 : (X6.setNode X6.rl l r').rl = X6.rl := by rw [hXf]; rfl
  have hnl : (X6.setNode X6.rl l r').nloc = X6.nloc := by rw [hXf]; rfl
  have hlb : (X6.setNode X6.rl l r').liveB = X6.liveB := by rw [hXf]; rfl
  have hloc : ∀ m, bktLoc (X6.setNode X6.rl l r') m = bktLoc X6 m := by
    intro m; unfold bktLoc; rw [hrl7, hlk, if_pos rfl, hB6]; rfl
  have hpw : wsPw rl.ws :=
    wsSorted_pw _ ((wOK_bktClean X6 hok6 X6.rl B6 hB6).2.2.2.2.2.2.2.1 l rl hrl).2.2.2.1
  have hroot : rootEnts (X6.setNode X6.rl l r') =
      (rootEnts X6).filter fun x => decide (x.1 ≠ n) := by
    rw [rootEnts_setNode_withWs X6 X6.rl l B6 rl r' hB6 hrl hlf', hws', wsDelAt_wsDel rl.ws n hpw]
    exact rootEnts_delRoot X6 l B6 rl bnd n hok6 hB6 hrl hleaf hbk hkin
  have hwr : ∀ m, m ≠ n → wRoot X6.v (T.dropBkt n) m = wRoot X6.v T m := by
    intro m hm; unfold wRoot TxView.dropBkt; simp only [if_neg hm]
  refine ⟨⟨fun l0 b p hl hb => ?_, fun b B c' l0 hB hb hc => ?_⟩, fun m b hm => ?_,
    fun m => ?_, fun l0 b p hl => ?_⟩
  · rw [hnl] at hl; rw [hlb] at hb
    obtain ⟨B, hB, hm⟩ := h1 l0 b p hl hb
    have e := hmap BRec.nm (fun _ => rfl) b
    rw [hB] at e
    cases hB' : (X6.setNode X6.rl l r').t.bs !! b with
    | none => rw [hB'] at e; cases e
    | some B' =>
      rw [hB'] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact ⟨B', rfl, by rw [e]; exact hm⟩
  · rw [hnl]; rw [hlb] at hb
    have e := hmap BRec.nm (fun _ => rfl) b
    rw [hB] at e
    cases hB0 : X6.t.bs !! b with
    | none => rw [hB0] at e; cases e
    | some B0 =>
      rw [hB0] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact h2 b B0 c' l0 hB0 hb (by rw [← e]; exact hc)
  · rw [hloc] at hm
    have hmn : m ≠ n := by
      intro e; subst e; unfold bktLoc at hm; rw [hB6] at hm; simp only [Option.bind_some] at hm
      rw [hbmn] at hm; cases hm
    have := hmap (fun D => D.ib.root') (fun _ => rfl) b
    have hrp : (X6.setNode X6.rl l r').rootPid b = X6.rootPid b := by
      unfold WX.rootPid; rw [this]
    rw [hrp, hv, hwr m hmn]; exact h3 m b hm
  · unfold rootEntRef rootEntVal
    rw [hroot, hv]
    by_cases hmn : m = n
    · subst hmn
      have : ((rootEnts X6).filter fun x => decide (x.1 ≠ m)).find? (fun e => decide (e.1 = m)) =
          none := by
        apply List.find?_eq_none.2
        intro x hx
        have := (List.mem_filter.1 hx).2
        simpa using this
      rw [this]
      unfold wRoot TxView.dropBkt; simp
    · have himp : ∀ x : GoString × List w8, decide (x.1 = m) = true → decide (x.1 ≠ n) = true := by
        intro x hx; simp only [decide_eq_true_eq] at hx ⊢; rw [hx]; exact hmn
      rw [← find?_filter_of_imp _ _ himp, hwr m hmn]
      exact h4 m
  · rw [hnl] at hl
    have hb := h5 l0 b p hl
    unfold WTx.bobjs at hb ⊢
    have hd : (X6.setNode X6.rl l r').t.deadB = X6.t.deadB := by rw [hXf]; rfl
    have := hmap (fun _ => ()) (fun _ => rfl) b
    rw [GMap.lookup_union] at hb ⊢; rw [hd]
    cases h1 : (X6.setNode X6.rl l r').t.bs !! b <;> cases h2 : X6.t.bs !! b <;>
      rw [h1, h2] at this <;> simp_all

end delbktcur

end Write

end bbolt
end EtcdGrove
end Perennial
