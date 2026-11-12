/-
U7q (`notes/bbolt-proof-plan.md`): **the freelist's agreement after `DeleteBucket`**
(`dbk_flView`, for `Write/DelBktPure.dbk_post`). From `flViewU X1 w.fl` directly (the intermediate
records do not agree with either freelist: after `delMid` the root's entry `n` covers the child's
slots again until the leaf's delete). Every cover of the final records `X7` is one of `X1`'s but a
position of the child or the root entry `n` (`Write/DelBktFlvCov`); the child's covers are
exactly the slots of the extents freed (`t.pos`'s, the view tree's: `dbk_childCov`), none for an
inline child (`inline_noCov`), and those become pending (`Write/DelBktFlvFl`). So a slot of the
child is neither covered nor not pending, any other keeps both.
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktFlvCov
public import Proof.go_etcd_io.bbolt.Write.DelBktFlvFl
public import Proof.go_etcd_io.bbolt.Write.DelBktFree
public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Write.DelBktHeap

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section flv
variable [GooseExts]

theorem coverW_of_lCovers {X : WX} {s : Nat} (h : lCovers X s) : ∃ cw, coverW X s cw := by
  rcases h with ⟨bl, e, hne, he, h1, h2⟩ | ⟨m, v, h1, h2, h3⟩
  · obtain ⟨pid, hp, hx⟩ := List.mem_filterMap.1 he
    exact ⟨.pos bl pid, hne, hp, e, hx, h1, h2⟩
  · exact ⟨.bkt m, v, h1, h2, h3⟩

theorem lCovers_of_coverW' {X : WX} {s : Nat} {cw : CovW} (h : coverW X s cw) : lCovers X s := by
  cases cw with
  | pos bl pid =>
    obtain ⟨hne, hp, e, hx, h1, h2⟩ := h
    exact Or.inl ⟨bl, e, hne, List.mem_filterMap.2 ⟨pid, hp, hx⟩, h1, h2⟩
  | bkt m =>
    obtain ⟨v, h1, h2, h3⟩ := h
    exact Or.inr ⟨m, v, h1, h2, h3⟩

/-- **An inline bucket covers no base slot.** -/
theorem inline_noCov (X : WX) (hok : wOK X) (c : Loc) (C : BRec) (hC : X.t.bs !! c = some C)
    (h0 : C.ib.root' = W64 0) (s : Nat) (pid : w64) : ¬ coverW X s (.pos c pid) := by
  rintro ⟨-, hp, e, hx, -, -⟩
  have hc := (hok.1.2.2.2.2.2 c C hC).1
  obtain ⟨t0, ht0, hp0, hh0, -⟩ := rtOK_init X c hok hok.2.2.2.2.2.2.2 (by rw [hC]; rfl)
  rw [positions_rt X c t0 ht0 hp0 hh0] at hp
  have hrp : X.rootPid c = W64 0 := by unfold WX.rootPid; rw [hC]; simp [h0]
  -- the root position is a leaf
  have hleaf0 : ∀ b ws, ltree X c (W64 0) = some (b, ws) → b = true := by
    intro b ws hl
    unfold ltree at hl; rw [hC] at hl; simp only at hl
    cases hres : resolve C (W64 0) with
    | none =>
      rw [hres] at hl
      have hrn : C.bv.rootNode' = null := by
        unfold resolve at hres; rw [if_pos h0] at hres; split at hres
        · assumption
        · cases hres
      cases hpg : wpageAt X.v C (W64 0) with
      | none => rw [hpg] at hl; cases hl
      | some lp =>
        rw [hpg] at hl
        obtain ⟨pa, pg⟩ := lp
        have := wOK_inlineLeaf X c (W64 0) hok C pa pg hC h0 hrn hpg
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
        rw [← hl.1]; simp [this]
    | some l =>
      rw [hres] at hl
      simp only at hl
      cases hr : C.ns !! l with
      | none => rw [hr] at hl; cases hl
      | some r =>
        rw [hr] at hl
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
        rw [← hl.1]; exact hc.2.2.2.2.2.2.1 h0 l r hr
  have hpid : pid = W64 0 := by
    obtain ⟨p, b, ws, cs⟩ := t0
    simp only [RTree.pid] at hp0
    rw [hrp] at hp0; subst hp0
    cases b with
    | true => simp only [RTree.pos, List.mem_singleton] at hp; exact hp
    | false =>
      simp only [ltIs] at ht0
      exact absurd (hleaf0 false ws ht0.1) (by decide)
  subst hpid
  rw [posExtent_def, hC] at hx
  simp only at hx
  have : posIdOf C (W64 0) = W64 0 := by
    unfold posIdOf
    cases hres : resolve C (W64 0) with
    | none => rfl
    | some l =>
      simp only
      have hrn : C.bv.rootNode' ≠ null ∧ C.bv.rootNode' = l := by
        unfold resolve at hres; rw [if_pos h0] at hres; split at hres
        · cases hres
        · rename_i h; cases hres; exact ⟨h, rfl⟩
      have hnm := hc.2.2.2.1 hrn.1
      rw [h0, hrn.2] at hnm
      obtain ⟨-, r, hr, hpg⟩ := hc.2.2.2.2.1 _ l hnm
      rw [hr]; exact hpg
  rw [if_pos this] at hx; cases hx

/-- **The child's covers are the slots of the extents freed** (a file bucket: its positions are
the view tree's, each position's extent its page's). -/
theorem dbk_childCov (X : WX) (hok : wOK X) (c : Loc) (C : BRec) (hC : X.t.bs !! c = some C)
    (h0 : C.ib.root' ≠ W64 0) (t : RTree) (ht : ltIs (pltree X.v) c t) (htp : t.pid = C.ib.root')
    (s : Nat) :
    (∃ e ∈ t.pos.filterMap (pExt X.v), e.1.toNat ≤ s ∧ s < e.1.toNat + e.2) ↔
      ∃ pid, coverW X s (.pos c pid) := by
  have hc := (hok.1.2.2.2.2.2 c C hC).1
  have hvw : viewWF X.v := hok.2.2.2.2.2.2.2
  obtain ⟨t0, ht0, hp0, hh0, -⟩ := rtOK_init X c hok hvw (by rw [hC]; rfl)
  have hrp : X.rootPid c = C.ib.root' := by unfold WX.rootPid; rw [hC]; rfl
  obtain ⟨t', ht', htp', htpos, -⟩ := ltIs_tr (ltree X) (pltree X.v) c
    (ltree_pltree X hok c C hC h0) t0 ht0
  have htt : t' = t := ltIs_det _ c t' t ht' ht (by rw [htp', hp0, hrp, htp])
  subst htt
  have hpos : X.positions c = t'.pos := by rw [positions_rt X c t0 ht0 hp0 hh0, htpos]
  -- a position's extent is its page's
  have hext : ∀ p, X.posExtent c p = pExt X.v p := by
    intro p
    cases hpe : pExt X.v p with
    | some e =>
      obtain ⟨pg, hpg, rfl⟩ := pExt_some hpe
      have h2 := (Read.viewWF_page _ hvw _ pg hpg).1
      have hp0' : p ≠ W64 0 := by intro e; rw [e] at h2; simp at h2
      cases hres : resolve C p with
      | none => exact posExtent_page X c C p pg hC hres hp0' hpg
      | some l =>
        have hnm : C.nm !! p = some l := by unfold resolve at hres; rwa [if_neg h0] at hres
        obtain ⟨-, r, hr, hpid⟩ := hc.2.2.2.2.1 p l hnm
        exact posExtent_node X c C p l r pg hC hres hr hpid hp0' hpg
    | none =>
      have hnp : X.v.pages !! p.toNat = none := by
        unfold pExt at hpe; cases h : X.v.pages !! p.toNat <;> simp_all
      rw [posExtent_def, hC]
      simp only
      have : posIdOf C p = p := by
        unfold posIdOf
        cases hres : resolve C p with
        | none => rfl
        | some l =>
          have hnm : C.nm !! p = some l := by unfold resolve at hres; rwa [if_neg h0] at hres
          obtain ⟨-, r, hr, hpid⟩ := hc.2.2.2.2.1 p l hnm
          simp only [hr, Option.map_some, Option.getD_some, hpid]
      rw [this]; split
      · rfl
      · rw [hnp]; rfl
  constructor
  · rintro ⟨e, he, h1, h2⟩
    obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.1 he
    exact ⟨p, by rw [hC]; simp, by rw [hpos]; exact hp, e, by rw [hext]; exact hpe, h1, h2⟩
  · rintro ⟨pid, -, hp, e, hx, h1, h2⟩
    rw [hpos] at hp; rw [hext] at hx
    exact ⟨e, List.mem_filterMap.2 ⟨pid, hp, hx⟩, h1, h2⟩

/-- **The freelist's agreement after `DeleteBucket`** (see the module doc). -/
theorem dbk_flView (X1 X6 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec) (w w' : WDb)
    (l : Loc) (B6 : BRec) (rl : NRec) (s : GoSlice) (ins : List Inode) (t : RTree)
    (hok1 : wOK X1) (hR1 : X1.t.bs !! X1.rl = some R1) (hn : R1.bm !! n = some c)
    (hC : X1.t.bs !! c = some C) (hwr1 : wrFacts X1) (hfl1 : flViewU X1 w.fl)
    (htx : X1.t.mv.txid' = w.wtxid) (hok5 : wOK (delMid X1 c C R1 n D))
    (hD : (C.ib.root' = W64 0 ∧ D = deadRec { C with ns := ∅ } ∧ w' = w) ∨
      (C.ib.root' ≠ W64 0 ∧ ltIs (pltree X1.v) c t ∧ t.pid = C.ib.root' ∧
        D = { deadRec { C with ns := ∅ } with ib := { C.ib with root' := W64 0 } } ∧
        w' = w.withFl (w.fl.freeAll w.wtxid (t.pos.filterMap (pExt X1.v)))))
    (hmg : matGrow (delMid X1 c C R1 n D) X6 X1.rl) (hok6 : wOK X6)
    (hB6 : X6.t.bs !! X1.rl = some B6) (hrl : B6.ns !! l = some rl) (hlf : leafFor X6 X1.rl n l) :
    flViewU (X6.setNode X1.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)) w'.fl := by
  have hcr : c ≠ X1.rl := hwr1.2.2 R1 hR1 n c hn
  obtain ⟨-, k2, -, -, -, -, -, k8⟩ := matGrow_keepW hmg
  have h6rl : X6.rl = X1.rl := k2
  have hA := cwSame_delMid X1 c C R1 n D hok1 hok5 hcr hR1
  have hB := cwSame_matGrow c n hmg hok5
  have h6c : X6.t.bs !! c = none := by
    cases h : X6.t.bs !! c with
    | none => rfl
    | some B' =>
      obtain ⟨B, hB0, -⟩ := k8 c B' h
      rw [delMid_bs_c] at hB0; cases hB0
  rw [← h6rl] at hB6 hlf ⊢
  obtain ⟨hC', hnone⟩ := cwSame_delRoot X6 c n l B6 rl s ins hok6 hB6 hrl hlf
  have h7c : (X6.setNode X6.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)).t.bs !! c = none := by
    unfold WX.setNode; rw [hB6]; unfold WX.setBkt; simp only
    rw [GMap.lookup_insert_ne _ _ (by rw [h6rl]; exact Ne.symm hcr)]; exact h6c
  have hS := cwSame_trans (cwSame_trans hA hB) hC'
  generalize X6.setNode X6.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true) = X7 at hS hnone h7c ⊢
  obtain ⟨⟨hcov, hmv, hnd, hlt62⟩, hcu, hpx, hpa⟩ := hfl1
  have hv7 : X7.v = X1.v := hS.1
  have hreg7 : ∀ s cw, coverW X7 s cw → cwReg c n cw := by
    intro s cw h
    cases cw with
    | pos bl pid =>
      intro e; subst e; exact h.1 h7c
    | bkt m =>
      intro e; subst e
      obtain ⟨v, h1, -⟩ := h
      exact hnone v h1
  have htr : ∀ s cw, coverW X7 s cw → coverW X1 s cw :=
    fun s cw h => (cwSame_cover hS s cw (hreg7 s cw h)).1 h
  have hX1n : ∀ s, ¬ coverW X1 s (.bkt n) := by
    rintro s ⟨v, -, h2, -⟩
    unfold bktLoc at h2; rw [hR1] at h2; simp only [Option.bind_some] at h2
    rw [hn] at h2; cases h2
  let P : Nat → Prop := fun s => ∃ pid, coverW X1 s (.pos c pid)
  have hl7 : ∀ s, lCovers X7 s → ¬ P s ∧ lCovers X1 s := by
    intro s h
    obtain ⟨cw, hcw⟩ := coverW_of_lCovers h
    refine ⟨fun ⟨pid, hp⟩ => ?_, lCovers_of_coverW' (htr s cw hcw)⟩
    have := hcu s cw _ (htr s cw hcw) hp
    have hr := hreg7 s cw hcw
    subst this
    exact hr rfl
  have hl1 : ∀ s, lCovers X1 s → ¬ P s → lCovers X7 s := by
    intro s h hP
    obtain ⟨cw, hcw⟩ := coverW_of_lCovers h
    have hr : cwReg c n cw := by
      cases cw with
      | pos bl pid => intro e; subst e; exact hP ⟨pid, hcw⟩
      | bkt m => intro e; subst e; exact hX1n s hcw
    exact lCovers_of_coverW' ((cwSame_cover hS s cw hr).2 hcw)
  have hcovU : covU X7 := fun s c1 c2 h1 h2 => hcu s c1 c2 (htr s c1 h1) (htr s c2 h2)
  -- the freelist after the frees
  have hfl' : (∀ s, coversSlot X1.v.pages s → (s ∈ pendSlots w'.fl ↔ s ∈ pendSlots w.fl ∨ P s)) ∧
      mvccView w'.fl X1.v ∧ w'.fl.allIds.Nodup ∧ (∀ id ∈ w'.fl.allIds, id.toNat < 2 ^ 62) ∧
      pendAligned w'.fl := by
    rcases hD with ⟨h0, -, rfl⟩ | ⟨h0, ht, htp, -, rfl⟩
    · refine ⟨fun s _ => ?_, hmv, hnd, hlt62, hpa⟩
      have : ¬ P s := fun ⟨pid, hp⟩ => inline_noCov X1 hok1 c C hC h0 s pid hp
      simp [this]
    · obtain ⟨-, t', ht', htp', hcan⟩ := dbk_freePre X1 c C R1 n w.fl w.wtxid hok1 hwr1 hR1 hn hC
        ⟨⟨hcov, hmv, hnd, hlt62⟩, hcu, hpx, hpa⟩ htx h0
      have htt : t' = t := ltIs_det _ c t' t ht' ht (by rw [htp', htp])
      subst htt
      have hes : ∀ e ∈ t'.pos.filterMap (pExt X1.v),
          ∃ pg, X1.v.pages !! e.1.toNat = some pg ∧ 1 + pageOverflow pg = e.2 := by
        intro e he
        obtain ⟨p, -, hpe⟩ := List.mem_filterMap.1 he
        obtain ⟨pg, hpg, rfl⟩ := pExt_some hpe
        exact ⟨pg, hpg, rfl⟩
      have htxe : X1.v.txid + 1 = w.wtxid.toNat := by rw [← htx]; exact hok1.1.2.2.2.1
      refine ⟨fun s _ => ?_, ?_, ?_⟩
      · show s ∈ pendSlots (w.fl.freeAll _ _) ↔ _
        rw [pendSlots_freeAll w.wtxid s _ w.fl hcan, dbk_childCov X1 hok1 c C hC h0 t' ht' htp' s]
      · refine mvccView_freeAll X1.v w.wtxid (by omega) (fun s ⟨id, pg, hpg, h1, h2⟩ => ?_) _ w.fl
          hcan hpa hes hmv
        have := hpx id pg hpg; omega
      · have hb : ∀ e ∈ t'.pos.filterMap (pExt X1.v), e.1.toNat + e.2 ≤ 2 ^ 62 := by
          intro e he
          obtain ⟨pg, hpg, he2⟩ := hes e he
          rw [← he2]; exact hpx _ pg hpg
        obtain ⟨a, b⟩ := allIds_freeAll_ok w.wtxid _ w.fl hcan hb hnd hlt62
        exact ⟨a, b, pendAligned_freeAll w.wtxid _ w.fl hpa⟩
  obtain ⟨hpend, hmv', hnd', hlt', hpa'⟩ := hfl'
  refine ⟨⟨fun s hs => ?_, by rw [hv7]; exact hmv', hnd', hlt'⟩, hcovU, by rw [hv7]; exact hpx,
    hpa'⟩
  rw [hv7] at hs
  by_cases hP : P s
  · have hp := (hpend s hs).2 (Or.inr hP)
    exact ⟨fun h => absurd hP (hl7 s h).1, fun h => absurd hp h⟩
  · rw [hpend s hs]
    constructor
    · intro h
      have := (hcov s hs).1 (hl7 s h).2
      exact fun h' => h'.elim this hP
    · intro h
      exact hl1 s ((hcov s hs).2 (fun h' => h (Or.inl h'))) hP

end flv

end Write

end bbolt
end EtcdGrove
end Perennial
