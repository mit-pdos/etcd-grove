/-
U7q (`notes/bbolt-proof-plan.md`): **what covers a base slot across `DeleteBucket`'s records**, for
`Write/DelBktFlv.dbk_flView`. `cwSame X Y c n`: every cover (`coverW`) but a position of the
child `c` and the root's entry `n` is a cover of `X` iff of `Y` (`cwSame_cover`). It holds across
`delMid` (`cwSame_delMid`: the root's cache without `n`, the child out of `bs`), a materialization
(`cwSame_matGrow`) and the root leaf's delete of `n` (`cwSame_delRoot`, which also drops every
root entry `n`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktPost2
public import Proof.go_etcd_io.bbolt.Write.CovUMat
public import Proof.go_etcd_io.bbolt.Write.WrCur

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section flvcov
variable [GooseExts]

/-- A cover that is neither a position of `c` nor the root's entry `n`. -/
def cwReg (c : Loc) (n : GoString) : CovW → Prop
  | .pos bl _ => bl ≠ c
  | .bkt m => m ≠ n

/-- `X` and `Y` agree on the covers `cwReg c n` (see the module doc). -/
def cwSame (X Y : WX) (c : Loc) (n : GoString) : Prop :=
  Y.v = X.v ∧ (∀ bl, bl ≠ c → (Y.t.bs !! bl).isSome = (X.t.bs !! bl).isSome) ∧
  (∀ bl, bl ≠ c → (X.t.bs !! bl).isSome → Y.positions bl = X.positions bl ∧
      ∀ pid ∈ X.positions bl, Y.posExtent bl pid = X.posExtent bl pid) ∧
  (∀ m v, m ≠ n → ((m, v) ∈ rootEnts Y ↔ (m, v) ∈ rootEnts X)) ∧
  (∀ m, m ≠ n → bktLoc Y m = bktLoc X m)

theorem cwSame_refl (X : WX) (c : Loc) (n : GoString) : cwSame X X c n :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem cwSame_trans {X Y Z : WX} {c : Loc} {n : GoString} (h1 : cwSame X Y c n)
    (h2 : cwSame Y Z c n) : cwSame X Z c n := by
  obtain ⟨a1, b1, c1, d1, e1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2⟩ := h2
  refine ⟨a2.trans a1, fun bl h => (b2 bl h).trans (b1 bl h), fun bl h hs => ?_,
    fun m v h => (d2 m v h).trans (d1 m v h), fun m h => (e2 m h).trans (e1 m h)⟩
  have hs' : (Y.t.bs !! bl).isSome := by rw [b1 bl h]; exact hs
  obtain ⟨p1, x1⟩ := c1 bl h hs
  obtain ⟨p2, x2⟩ := c2 bl h hs'
  refine ⟨p2.trans p1, fun pid hp => ?_⟩
  rw [x2 pid (by rw [p1]; exact hp), x1 pid hp]

theorem cwSame_cover {X Y : WX} {c : Loc} {n : GoString} (h : cwSame X Y c n) (s : Nat)
    (cw : CovW) (hr : cwReg c n cw) : coverW Y s cw ↔ coverW X s cw := by
  obtain ⟨hv, hbs, hpos, hroot, hbkt⟩ := h
  cases cw with
  | pos bl pid =>
    have hbc : bl ≠ c := hr
    have hne : (Y.t.bs !! bl ≠ none ↔ X.t.bs !! bl ≠ none) := by
      have := hbs bl hbc
      cases h1 : Y.t.bs !! bl <;> cases h2 : X.t.bs !! bl <;> simp_all
    have hsome : X.t.bs !! bl ≠ none → (X.t.bs !! bl).isSome := by
      intro h; cases e : X.t.bs !! bl <;> simp_all
    constructor
    · rintro ⟨h1, h2, e, h3, h4⟩
      have h1' := hne.1 h1
      obtain ⟨p, x⟩ := hpos bl hbc (hsome h1')
      have h2' : pid ∈ X.positions bl := by rw [← p]; exact h2
      exact ⟨h1', h2', e, by rw [← x pid h2']; exact h3, h4⟩
    · rintro ⟨h1, h2, e, h3, h4⟩
      obtain ⟨p, x⟩ := hpos bl hbc (hsome h1)
      exact ⟨hne.2 h1, by rw [p]; exact h2, e, by rw [x pid h2]; exact h3, h4⟩
  | bkt m =>
    have hmn : m ≠ n := hr
    constructor
    · rintro ⟨v, h1, h2, h3⟩
      exact ⟨v, (hroot m v hmn).1 h1, by rw [← hbkt m hmn]; exact h2, by rw [← hv]; exact h3⟩
    · rintro ⟨v, h1, h2, h3⟩
      exact ⟨v, (hroot m v hmn).2 h1, by rw [hbkt m hmn]; exact h2, by rw [hv]; exact h3⟩

/-- **A materialization keeps every cover.** -/
theorem cwSame_matGrow {X Y : WX} {bl : Loc} (c : Loc) (n : GoString) (h : matGrow X Y bl)
    (hok : wOK X) : cwSame X Y c n := by
  induction h with
  | refl => exact cwSame_refl _ c n
  | step X Y Z bl l pgid parent hadd hpos _ ih =>
    refine cwSame_trans ?_ (ih (wOK_nodeAdded X Y bl l pgid parent hok hadd hpos))
    have hf := wOK_matFresh X Y bl l pgid parent hok hadd hpos
    obtain ⟨hroot, hbkt, -, hvv, -, -, -, hbs⟩ :=
      nodeAdded_facts X Y bl l pgid parent hadd hf (wOK_inlineLeaf X bl pgid hok)
    refine ⟨hvv, fun b _ => hbs b, fun b _ _ => ?_, fun m v _ => by rw [hroot], fun m _ => hbkt m⟩
    obtain ⟨p, x⟩ := nodeAdded_posParts X Y bl l pgid parent hok hadd hpos b
    exact ⟨p, x⟩

/-- **Two well-formed records with one logical tree of a bucket have its positions.** -/
theorem positions_congr (X Y : WX) (bl : Loc) (hokX : wOK X) (hokY : wOK Y)
    (hbX : (X.t.bs !! bl).isSome) (hbY : (Y.t.bs !! bl).isSome)
    (hL : ltree Y bl = ltree X bl) (hrp : Y.rootPid bl = X.rootPid bl) :
    Y.positions bl = X.positions bl := by
  obtain ⟨tX, htX, hpX, hhX, -⟩ := rtOK_init X bl hokX hokX.2.2.2.2.2.2.2 hbX
  obtain ⟨tY, htY, hpY, hhY, -⟩ := rtOK_init Y bl hokY hokY.2.2.2.2.2.2.2 hbY
  have e1 := lposF_ltIs (ltree X) bl tX (X.fuel + Y.fuel) htX (by omega)
  have e2 := lposF_ltIs (ltree Y) bl tY (X.fuel + Y.fuel) htY (by omega)
  rw [← lposF_congr (ltree X) (ltree Y) bl (fun q => by rw [hL]), hpX, ← hrp, ← hpY, e2] at e1
  rw [positions_rt Y bl tY htY hpY hhY, positions_rt X bl tX htX hpX hhX, e1]

/-- The page id of a position is the bucket's tree's (`sameTreeB`). -/
theorem posIdOf_congr (B B' : BRec) (h : sameTreeB B B') (pid : w64) :
    posIdOf B' pid = posIdOf B pid := by
  unfold posIdOf; rw [resolve_congr B B' h, h.2.2.2.1]

theorem delMid_bs_c (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec) :
    (delMid X1 c C R1 n D).t.bs !! c = none := by
  rw [delMid_bs, if_pos rfl]

/-- **`delMid` keeps every cover but the child's positions and the root's entry `n`.** -/
theorem cwSame_delMid (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec)
    (hok1 : wOK X1) (hok5 : wOK (delMid X1 c C R1 n D)) (hcr : c ≠ X1.rl)
    (hR1 : X1.t.bs !! X1.rl = some R1) :
    cwSame X1 (delMid X1 c C R1 n D) c n := by
  have hYrl : (delMid X1 c C R1 n D).t.bs !! X1.rl = some (bUnopen R1 n) := by
    rw [delMid_bs, if_neg hcr, if_pos rfl]
  have hv : (delMid X1 c C R1 n D).v = X1.v := rfl
  have hst : ∀ bl, bl ≠ c → ∀ B, X1.t.bs !! bl = some B →
      ∃ B', (delMid X1 c C R1 n D).t.bs !! bl = some B' ∧ sameTreeB B B' := by
    intro bl hbc B hB
    rw [delMid_bs, if_neg (Ne.symm hbc)]
    by_cases hr : bl = X1.rl
    · subst hr; rw [if_pos rfl]; rw [hR1] at hB; cases hB; exact ⟨_, rfl, sameTreeB_bm R1 _⟩
    · rw [if_neg hr]; exact ⟨B, hB, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hroot : rootEnts (delMid X1 c C R1 n D) = rootEnts X1 := by
    have hLR := ltree_congr_bkt X1 (delMid X1 c C R1 n D) X1.rl R1 (bUnopen R1 n) rfl hR1 hYrl
      (sameTreeB_bm R1 _)
    have hPR := rootPid_congr_bkt X1 (delMid X1 c C R1 n D) X1.rl R1 (bUnopen R1 n) rfl hR1 hYrl
      (sameTreeB_bm R1 _)
    unfold rootEnts
    exact congrArg _ (leaves_congr X1 (delMid X1 c C R1 n D) X1.rl hok1 hok5 (by rw [hR1]; rfl)
      (by rw [hYrl]; rfl) hLR hPR)
  refine ⟨hv, fun bl hbc => ?_, fun bl hbc hs => ?_, fun m v _ => by rw [hroot], fun m hm => ?_⟩
  · rw [delMid_bs, if_neg (Ne.symm hbc)]
    by_cases hr : bl = X1.rl
    · subst hr; rw [if_pos rfl, hR1]; rfl
    · rw [if_neg hr]
  · obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨B', hB', hs'⟩ := hst bl hbc B hB
    refine ⟨positions_congr X1 _ bl hok1 hok5 hs (by rw [hB']; rfl)
      (ltree_congr_bkt X1 _ bl B B' rfl hB hB' hs') (rootPid_congr_bkt X1 _ bl B B' rfl hB hB' hs'),
      fun pid _ => ?_⟩
    apply posExtent_eq X1 _ bl pid hv
    rw [hB, hB']; simp only [Option.map_some, posIdOf_congr B B' hs' pid]
  · unfold bktLoc
    rw [show (delMid X1 c C R1 n D).rl = X1.rl from rfl, hYrl, hR1]
    simp only [Option.bind_some]
    exact GMap.lookup_delete_ne _ (Ne.symm hm)

/-- **The root leaf's delete of `n` keeps every other cover**, and leaves no root entry `n`. -/
theorem cwSame_delRoot (X6 : WX) (c : Loc) (n : GoString) (l : Loc) (B6 : BRec) (rl : NRec)
    (s : GoSlice) (ins : List Inode)
    (hok6 : wOK X6) (hB6 : X6.t.bs !! X6.rl = some B6) (hrl : B6.ns !! l = some rl)
    (hlf : leafFor X6 X6.rl n l) :
    cwSame X6 (X6.setNode X6.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)) c n ∧
      ∀ v, (n, v) ∉ rootEnts (X6.setNode X6.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)) := by
  obtain ⟨B', r0, bnd, hB', hr', hleaf, hbk, hkin⟩ := id hlf
  rw [hB6] at hB'; cases hB'; rw [hrl] at hr'; cases hr'
  have hXf : X6.setNode X6.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true) =
      X6.setBkt X6.rl { B6 with ns := B6.ns.insert l (rl.withEntsU s ins (wsDelAt rl.ws n) true) } := by
    unfold WX.setNode; rw [hB6]
  generalize hr' : rl.withEntsU s ins (wsDelAt rl.ws n) true = r' at hXf ⊢
  have hpg' : r'.nv.pgid' = rl.nv.pgid' := by rw [← hr']; rfl
  have hlf' : r'.nv.isLeaf' = rl.nv.isLeaf' := by rw [← hr']; rfl
  have hws' : r'.ws = wsDelAt rl.ws n := by rw [← hr']; rfl
  have hlk : ∀ b, (X6.setNode X6.rl l r').t.bs !! b =
      if b = X6.rl then some { B6 with ns := B6.ns.insert l r' } else X6.t.bs !! b := by
    intro b; rw [hXf]; unfold WX.setBkt; simp only
    by_cases hb : b = X6.rl
    · subst hb; rw [if_pos rfl, GMap.lookup_insert]
    · rw [if_neg hb, GMap.lookup_insert_ne _ _ (Ne.symm hb)]
  have hv : (X6.setNode X6.rl l r').v = X6.v := by rw [hXf]; rfl
  have hrl7 : (X6.setNode X6.rl l r').rl = X6.rl := by rw [hXf]; rfl
  have hfuel : (X6.setNode X6.rl l r').fuel = X6.fuel := by
    rw [hXf]; unfold WX.fuel WX.setBkt; simp only; rw [GMap.map_size_insert_Some _ _ _ _ hB6]
  have hrp : ∀ b, (X6.setNode X6.rl l r').rootPid b = X6.rootPid b := by
    intro b; unfold WX.rootPid; rw [hlk]
    split
    · rename_i hb; subst hb; rw [hB6]; rfl
    · rfl
  have hshape : ∀ b q, shp (ltree (X6.setNode X6.rl l r') b q) = shp (ltree X6 b q) := by
    intro b q
    unfold ltree; rw [hlk, hv]
    by_cases hb : b = X6.rl
    · subst hb
      rw [if_pos rfl, hB6]
      simp only
      rw [show resolve { B6 with ns := B6.ns.insert l r' } q = resolve B6 q from rfl,
        show wpageAt X6.v { B6 with ns := B6.ns.insert l r' } q = wpageAt X6.v B6 q from rfl]
      cases resolve B6 q with
      | none => rfl
      | some l0 =>
        simp only
        by_cases hl0 : l0 = l
        · subst hl0
          rw [GMap.lookup_insert, hrl]
          simp [shp, hleaf, hlf']
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hl0)]
    · rw [if_neg hb]
  have hpw : wsPw rl.ws :=
    wsSorted_pw _ ((wOK_bktClean X6 hok6 X6.rl B6 hB6).2.2.2.2.2.2.2.1 l rl hrl).2.2.2.1
  have hroot : rootEnts (X6.setNode X6.rl l r') =
      (rootEnts X6).filter fun x => decide (x.1 ≠ n) := by
    rw [rootEnts_setNode_withWs X6 X6.rl l B6 rl r' hB6 hrl hlf', hws', wsDelAt_wsDel rl.ws n hpw]
    exact rootEnts_delRoot X6 l B6 rl bnd n hok6 hB6 hrl hleaf hbk hkin
  refine ⟨⟨hv, fun b _ => ?_, fun b _ _ => ⟨?_, fun pid _ => ?_⟩, fun m v hm => ?_, fun m _ => ?_⟩,
    fun v hv' => ?_⟩
  · rw [hlk]; split
    · rename_i hb; subst hb; rw [hB6]; rfl
    · rfl
  · unfold WX.positions; rw [hfuel, hrp]; exact lposF_congr _ _ b (hshape b) _ _
  · apply posExtent_eq X6 _ b pid hv
    rw [hlk]; split
    · rename_i hb; subst hb; rw [hB6]
      simp only [Option.map_some, Option.some.injEq]
      unfold posIdOf
      rw [show resolve { B6 with ns := B6.ns.insert l r' } pid = resolve B6 pid from rfl]
      cases resolve B6 pid with
      | none => rfl
      | some l0 =>
        simp only
        by_cases hl0 : l0 = l
        · subst hl0; rw [GMap.lookup_insert, hrl]; simp [hpg']
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hl0)]
    · rfl
  · rw [hroot, List.mem_filter]; simp [hm]
  · unfold bktLoc; rw [hrl7, hlk, if_pos rfl, hB6]; rfl
  · rw [hroot, List.mem_filter] at hv'; simp at hv'

end flvcov

end Write

end bbolt
end EtcdGrove
end Perennial
