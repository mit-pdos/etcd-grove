/-
`rblX` through a bucket's records changed only in what the invariants do not read (U8b,
`Rebalance/RblXSteps.lean`): `X.setBkt bl B'` with `bktSim B B'` (`Rebalance/RblFrame`) keeps the
logical tree, its positions, extents and leaves, the root's entries, the objects and the reached
ones, so `rblX` holds again given the bucket's `rblB` and its nested entries (`rblX_sim`), and
`rblRel` with no free.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblX
public import Proof.go_etcd_io.bbolt.Rebalance.RblFrame
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSObjs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section sim
variable [GooseExts]

theorem bktSim_look {B B' : BRec} (hs : bktSim B B') (y : Loc) :
    (B.ns !! y = none ∧ B'.ns !! y = none) ∨
      ∃ ry ry', B.ns !! y = some ry ∧ B'.ns !! y = some ry' ∧ nrecEq ry ry' := by
  cases h : B.ns !! y with
  | none =>
    left; refine ⟨rfl, ?_⟩
    cases h' : B'.ns !! y with
    | none => rfl
    | some ry' =>
      obtain ⟨ry, hry, -⟩ := hs.2.2.2.2.2.2.2 y ry' h'
      rw [h] at hry; cases hry
  | some ry =>
    obtain ⟨ry', hry', e⟩ := hs.2.2.2.2.2.2.1 y ry h
    exact Or.inr ⟨ry, ry', rfl, hry', e⟩

theorem setBkt_look (X : WX) (bl : Loc) (B' : BRec) (c : Loc) :
    (X.setBkt bl B').t.bs !! c = if c = bl then some B' else X.t.bs !! c := by
  show (X.t.bs.insert bl B') !! c = _
  by_cases h : c = bl
  · subst h; rw [if_pos rfl]; exact GMap.lookup_insert _ _ _
  · rw [if_neg h]; exact GMap.lookup_insert_ne _ _ (Ne.symm h)

section
variable (X : WX) (bl : Loc) (B B' : BRec) (hb : X.t.bs !! bl = some B) (hs : bktSim B B')
include hb hs

theorem sim_dom (c : Loc) : ((X.setBkt bl B').t.bs !! c).isSome = (X.t.bs !! c).isSome := by
  rw [setBkt_look]; split
  · subst c; rw [hb]; rfl
  · rfl

theorem sim_ltree : ltree (X.setBkt bl B') = ltree X := by
  funext c q
  unfold ltree
  rw [setBkt_look]
  by_cases hc : c = bl
  · subst c
    rw [if_pos rfl, hb]
    have hbv := hs.1; have hib := hs.2.1; have hnm := hs.2.2.1; have hipg := hs.2.2.2.2.1
    have hres : resolve B' q = resolve B q := by simp only [resolve, hib, hbv, hnm]
    have hwp : wpageAt (X.setBkt bl B').v B' q = wpageAt X.v B q := by
      simp only [wpageAt, hib, hbv, hipg]; rfl
    simp only
    rw [hres, hwp]
    cases resolve B q with
    | none => rfl
    | some l =>
      simp only
      rcases bktSim_look hs l with ⟨h1, h2⟩ | ⟨ry, ry', h1, h2, e⟩
      · rw [h1, h2]
      · rw [h1, h2]; simp only [Option.map_some, e.1, e.2.2.2.2.2.2.1]
  · rw [if_neg hc]; rfl

theorem sim_rootPid : (X.setBkt bl B').rootPid = X.rootPid := by
  funext c
  unfold WX.rootPid
  rw [setBkt_look]; split
  · subst c; rw [hb]; simp only [Option.map_some, Option.getD_some, hs.2.1]
  · rfl

theorem sim_fuel : (X.setBkt bl B').fuel = X.fuel :=
  fuel_eq X (X.setBkt bl B') rfl (sim_dom X bl B B' hb hs)

theorem sim_leaves : (X.setBkt bl B').leaves = X.leaves := by
  funext c; unfold WX.leaves
  rw [sim_ltree X bl B B' hb hs, sim_fuel X bl B B' hb hs, sim_rootPid X bl B B' hb hs]

theorem sim_positions : (X.setBkt bl B').positions = X.positions := by
  funext c; unfold WX.positions
  rw [sim_ltree X bl B B' hb hs, sim_fuel X bl B B' hb hs, sim_rootPid X bl B B' hb hs]

theorem sim_posExtent : (X.setBkt bl B').posExtent = X.posExtent := by
  funext c q
  unfold WX.posExtent
  rw [setBkt_look]
  by_cases hc : c = bl
  · subst c
    rw [if_pos rfl, hb]
    have hbv := hs.1; have hib := hs.2.1; have hnm := hs.2.2.1
    have hres : resolve B' q = resolve B q := by simp only [resolve, hib, hbv, hnm]
    simp only
    rw [hres]
    cases resolve B q with
    | none => rfl
    | some l =>
      simp only
      rcases bktSim_look hs l with ⟨h1, h2⟩ | ⟨ry, ry', h1, h2, e⟩
      · rw [h1, h2]; rfl
      · rw [h1, h2]; simp only [Option.map_some, e.2.2.2.2.2.2.2.2.2.1]; rfl
  · rw [if_neg hc]; rfl

theorem sim_extents : (X.setBkt bl B').extents = X.extents := by
  funext c; unfold WX.extents
  rw [sim_positions X bl B B' hb hs, sim_posExtent X bl B B' hb hs]

theorem sim_rootEnts : rootEnts (X.setBkt bl B') = rootEnts X := by
  unfold rootEnts; rw [sim_leaves X bl B B' hb hs]; rfl

theorem sim_bktLoc : bktLoc (X.setBkt bl B') = bktLoc X := by
  funext n; unfold bktLoc
  show ((X.setBkt bl B').t.bs !! X.rl).bind _ = _
  rw [setBkt_look]; split
  · rename_i h; rw [h, hb]; simp only [Option.bind_some, hs.2.2.2.1]
  · rfl

theorem sim_lCovers : lCovers (X.setBkt bl B') = lCovers X := by
  funext s
  unfold lCovers
  have hd : ∀ c, ((X.setBkt bl B').t.bs !! c ≠ none) = (X.t.bs !! c ≠ none) := by
    intro c
    have := sim_dom X bl B B' hb hs c
    apply propext
    rw [Option.ne_none_iff_isSome, Option.ne_none_iff_isSome, this]
  simp only [hd, sim_extents X bl B B' hb hs, sim_rootEnts X bl B B' hb hs,
    sim_bktLoc X bl B B' hb hs]
  rfl

theorem sim_coverW : coverW (X.setBkt bl B') = coverW X := by
  funext s c
  cases c with
  | pos c pid =>
    unfold coverW
    have hd : ((X.setBkt bl B').t.bs !! c ≠ none) = (X.t.bs !! c ≠ none) := by
      have := sim_dom X bl B B' hb hs c
      apply propext
      rw [Option.ne_none_iff_isSome, Option.ne_none_iff_isSome, this]
    simp only [hd, sim_positions X bl B B' hb hs, sim_posExtent X bl B B' hb hs]
  | bkt n =>
    unfold coverW
    rw [sim_rootEnts X bl B B' hb hs, sim_bktLoc X bl B B' hb hs]
    rfl

theorem sim_flView (fl : FLPg) (h : flView X fl) : flView (X.setBkt bl B') fl := by
  unfold flView at h ⊢
  rw [sim_lCovers X bl B B' hb hs]
  exact h

theorem sim_covU (h : covU X) : covU (X.setBkt bl B') := by
  unfold covU at h ⊢
  rw [sim_coverW X bl B B' hb hs]
  exact h

theorem sim_rtOK (c : Loc) (h : rtOK X c) : rtOK (X.setBkt bl B') c := by
  unfold rtOK at h ⊢
  rw [sim_ltree X bl B B' hb hs, sim_rootPid X bl B B' hb hs, sim_fuel X bl B B' hb hs]
  exact h

theorem sim_objs (k : Loc) (h : (X.t.objs !! k).isSome = true) :
    ((X.setBkt bl B').t.objs !! k).isSome = true := by
  apply objs_isSome_mono X.t (X.setBkt bl B').t (fun _ h => h)
    (fun c h => by rw [sim_dom X bl B B' hb hs]; exact h) _ k h
  intro c C k hC hk
  right
  by_cases hc : c = bl
  · subst hc; rw [hb] at hC; cases hC
    refine ⟨c, B', by rw [setBkt_look, if_pos rfl], ?_⟩
    rcases bktSim_look hs k with ⟨h1, -⟩ | ⟨ry, ry', -, h2, -⟩
    · rw [h1] at hk; cases hk
    · rw [h2]; rfl
  · exact ⟨c, C, by rw [setBkt_look, if_neg hc]; exact hC, hk⟩

theorem sim_bktReach (c : Loc) (h : bktReach X c) : bktReach (X.setBkt bl B') c := by
  induction h with
  | root => exact bktReach.root
  | child d e C n hC hm _ ih =>
    by_cases hd : d = bl
    · subst hd; rw [hb] at hC; cases hC
      exact bktReach.child d e B' n (by rw [setBkt_look, if_pos rfl]) (by rw [hs.2.2.2.1]; exact hm) ih
    · exact bktReach.child d e C n (by rw [setBkt_look, if_neg hd]; exact hC) hm ih

end

theorem nodeRootIn_sim {B B' : BRec} (hs : bktSim B B') (a rt : Loc) (h : nodeRootIn B a rt) :
    nodeRootIn B' a rt := by
  induction h with
  | top n r hr hp =>
    obtain ⟨r', hr', e⟩ := hs.2.2.2.2.2.2.1 n r hr
    exact nodeRootIn.top n r' hr' (by rw [e.2.2.2.2.2.2.2.2.2.2.1]; exact hp)
  | up n rt r hr hp _ ih =>
    obtain ⟨r', hr', e⟩ := hs.2.2.2.2.2.2.1 n r hr
    have hpe := e.2.2.2.2.2.2.2.2.2.2.1
    exact nodeRootIn.up n rt r' hr' (by rw [hpe]; exact hp) (by rw [hpe]; exact ih)

theorem descIn_sim {B B' : BRec} (hs : bktSim B B') (a d : Loc) (h : descIn B a d) :
    descIn B' a d := by
  induction h with
  | self n => exact descIn.self n
  | child n c d r hr hc _ ih =>
    obtain ⟨r', hr', e⟩ := hs.2.2.2.2.2.2.1 n r hr
    exact descIn.child n c d r' hr' (by rw [e.2.1]; exact hc) ih

/-- **`rblX` through a bucket's records changed by `bktSim`**: given the bucket's `rblB` (its
deficient node `dfc'`) and its nested entries kept. -/
theorem rblX_sim (X : WX) (fl : FLPg) (bl : Loc) (dfc dfc' : Option Loc) (B B' : BRec)
    (txid : w64) (hI : rblX X fl bl dfc) (hb : X.t.bs !! bl = some B) (hs : bktSim B B')
    (hB' : rblB X.v X.t.mv.pgid'.toNat bl B' dfc')
    (hent : ∀ k v, entryIn X.v B k v → entryIn X.v B' k v) :
    rblX (X.setBkt bl B') fl bl dfc' ∧ rblRel X fl (X.setBkt bl B') fl txid := by
  obtain ⟨⟨htw, hpm, hhwm, htx, hrl⟩, hBk, hEB, hH, hL, hN, hV, hLR, hFV, hU⟩ := hI
  have hdom := sim_dom X bl B B' hb hs
  -- buckets of X' from X's
  have hback : ∀ c C, (X.setBkt bl B').t.bs !! c = some C → ∃ C0, X.t.bs !! c = some C0 ∧
      (c = bl ∧ C0 = B ∧ C = B' ∨ c ≠ bl ∧ C = C0) := by
    intro c C hC
    rw [setBkt_look] at hC
    split at hC
    · subst c; cases hC; exact ⟨B, hb, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨C, hC, Or.inr ⟨‹_›, rfl⟩⟩
  have hfwd : ∀ c C0, X.t.bs !! c = some C0 → ∃ C, (X.setBkt bl B').t.bs !! c = some C ∧
      C.ib = C0.ib ∧ C.bv = C0.bv ∧ C.bm = C0.bm := by
    intro c C0 hC0
    by_cases hc : c = bl
    · subst hc; rw [hb] at hC0; cases hC0
      exact ⟨B', by rw [setBkt_look, if_pos rfl], hs.2.1, hs.1, hs.2.2.2.1⟩
    · exact ⟨C0, by rw [setBkt_look, if_neg hc]; exact hC0, rfl, rfl, rfl⟩
  have hnest : ∀ C0 C, bktNested X.v X.t C0 → C.bm = C0.bm →
      (∀ k v, entryIn X.v C0 k v → entryIn X.v C k v) → bktNested X.v (X.setBkt bl B').t C := by
    intro C0 C hn hbm he k c hk
    rw [hbm] at hk
    obtain ⟨D0, v, hD0, hev, hlen, hinl, hroot, hib⟩ := hn k c hk
    obtain ⟨D, hD, hDib, hDbv, -⟩ := hfwd c D0 hD0
    exact ⟨D, v, hD, he k v hev, hlen, hinl, by rw [hDib]; exact hroot,
      fun h => by rw [hDib]; exact hib (by rw [← hDbv]; exact h)⟩
  refine ⟨⟨⟨htw, hpm, hhwm, htx, by rw [hdom]; exact hrl⟩, ?_, ?_, ?_, ?_, ?_, hV, ?_, ?_, ?_⟩, ?_⟩
  · intro c C hC
    obtain ⟨C0, hC0, hcase⟩ := hback c C hC
    obtain ⟨h1, h2, h3, h4, h5⟩ := hBk c C0 hC0
    rcases hcase with ⟨hc, hC0e, hCe⟩ | ⟨hc, rfl⟩
    · subst C; subst C0; subst c
      refine ⟨by rw [if_pos rfl]; exact hB', fun n d hd => ?_, hnest B B' h3 hs.2.2.2.1 hent,
        sim_rtOK X bl B B' hb hs bl h4, fun l r hr => ?_⟩
      · rw [hs.2.2.2.1] at hd; rw [hdom]; exact h2 n d hd
      · rcases bktSim_look hs l with ⟨-, h⟩ | ⟨ry, ry', h1', h2', -⟩
        · rw [h] at hr; cases hr
        · exact h5 l ry h1'
    · refine ⟨by rw [if_neg hc]; rw [if_neg hc] at h1; exact h1, fun n d hd => by
          rw [hdom]; exact h2 n d hd, hnest C C h3 rfl (fun _ _ h => h),
        sim_rtOK X bl B B' hb hs c h4, h5⟩
  · intro c C hC l r hr w hw
    obtain ⟨C0, hC0, hcase⟩ := hback c C hC
    rcases hcase with ⟨hc, hC0e, hCe⟩ | ⟨hc, rfl⟩
    · subst C; subst C0; subst c
      rcases bktSim_look hs l with ⟨-, h⟩ | ⟨ry, ry', h1, h2, e⟩
      · rw [h] at hr; cases hr
      · rw [h2] at hr; cases hr
        rw [e.1] at hw; rw [e.2.2.2.2.2.2.1]
        exact hEB bl B hC0 l ry h1 w hw
    · exact hEB c C hC0 l r hr w hw
  · intro b nm h; exact sim_objs X bl B B' hb hs b (hH b nm h)
  · obtain ⟨l1, l2, l3⟩ := hL
    refine ⟨l1, fun l h => sim_objs X bl B B' hb hs l (l2 l h), fun c C hC => ?_⟩
    obtain ⟨C0, hC0, -⟩ := hback c C hC
    exact l3 c C0 hC0
  · intro n c p h hl
    obtain ⟨C0, r0, hC0, hr0, hp⟩ := hN n c p h hl
    by_cases hc : c = bl
    · subst hc; rw [hb] at hC0; cases hC0
      obtain ⟨r', hr', e⟩ := hs.2.2.2.2.2.2.1 n r0 hr0
      exact ⟨B', r', by rw [setBkt_look, if_pos rfl], hr', by rw [e.2.2.2.2.2.2.2.2.2.1]; exact hp⟩
    · exact ⟨C0, r0, by rw [setBkt_look, if_neg hc]; exact hC0, hr0, hp⟩
  · obtain ⟨r1, r2⟩ := hLR
    refine ⟨fun c C hC hl => ?_, fun c C l r hC hr hl => ?_⟩
    · obtain ⟨C0, hC0, -⟩ := hback c C hC
      exact sim_bktReach X bl B B' hb hs c (r1 c C0 hC0 hl)
    · obtain ⟨C0, hC0, hcase⟩ := hback c C hC
      rcases hcase with ⟨hc, hC0e, hCe⟩ | ⟨hc, rfl⟩
      · subst C; subst C0; subst c
        rcases bktSim_look hs l with ⟨-, h⟩ | ⟨ry, ry', h1, h2, -⟩
        · rw [h] at hr; cases hr
        · obtain ⟨rt, hrt, hd⟩ := r2 bl B l ry hC0 h1 hl
          exact ⟨rt, by rw [hs.1]; exact nodeRootIn_sim hs _ _ hrt, descIn_sim hs _ _ hd⟩
      · exact r2 c C l r hC0 hr hl
  · exact sim_flView X bl B B' hb hs fl hFV
  · exact sim_covU X bl B B' hb hs hU
  · refine ⟨rfl, rfl, rfl, fun _ _ h => h, rfl, rfl, rfl, rfl, hdom, fun c C0 C hC0 hC => ?_,
      fun c => by rw [sim_leaves X bl B B' hb hs], [], trivial, rfl, fun _ h => by cases h⟩
    obtain ⟨C', hC', h1, h2, h3⟩ := hfwd c C0 hC0
    rw [hC'] at hC; cases hC
    exact ⟨h2, h1, h3⟩

end sim

end bbolt
end EtcdGrove
end Perennial
