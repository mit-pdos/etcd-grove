/-
**The flagged rollback's writer side** (maintainer 11, for `Tx.rollback_f`): `wdb_rollback'` from
`wdbOK' fr` (after `Commit`'s free of the synced freelist page, its slots pending for the writer):
the rollback deletes the writer's pending entry, so the relaxed slot clause (`flCurOKr`) becomes
`flCurOK`'s, and the page's slots, returned by `store_rollback` with the bytes the writer recorded
(`fbRel`), hold the page's bytes again.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.RollbackFacts
public import Proof.go_etcd_io.bbolt.Inv.WdbFlag

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **The relaxed freelist-page clause after the writer's rollback** is `flCurOK`'s (the page's
`allocs` entry comes back from the writer's pending entry, whose allocating transactions are
committed: `hpa`, `flBelow`'s writer clause). -/
theorem flCurOKr_rollback (fl : FLPg) (C : CommitSt) (pg : List w8) (wtx : w64)
    (hwtx : C.txid < wtx.toNat)
    (hpa : ∀ pd, fl.pending !! wtx = some pd → ∀ a ∈ pd.alloctx, a.toNat ≤ C.txid)
    (h : flCurOKr fl C wtx pg) :
    flCurOK (fl.rollback wtx) C pg := by
  intro f hf
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := h f hf
  have hfree : (fl.rollback wtx).free = fl.free := rollback_free _ _
  have hsub : ∀ t pd, (fl.rollback wtx).pending !! t = some pd → fl.pending !! t = some pd :=
    fun t pd hp => rollback_pending_sub _ _ t pd hp
  have hcp : ∀ x, committedPending (fl.rollback wtx) C x → committedPending fl C x := by
    rintro x ⟨t, pd, hp, hx, ht⟩
    exact ⟨t, pd, hsub t pd hp, hx, ht⟩
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun s h1 h2 => ⟨(a9 s h1 h2).1, ?_⟩,
    fun x hx => ?_, fun x hx => a11 x (hcp x hx), fun x hx => ?_, fun a ha => ?_, a14⟩
  · intro hm
    obtain ⟨-, -, hnf, hpt⟩ := a9 s h1 h2
    rcases List.mem_append.1 hm with hm | hm
    · rw [hfree] at hm
      exact hnf hm
    · obtain ⟨t, pd, hp, hx⟩ := (pendingIds_mem_iff _ _).1 hm
      have hp' := hsub t pd hp
      have ht := hpt t pd hp' hx
      subst ht
      have hnone : (fl.rollback t).pending !! t = none := by
        unfold FLPg.rollback
        split
        · assumption
        · unfold FLPg.rollbackEntry; simp
      rw [hnone] at hp
      cases hp
  · rw [hfree] at hx; exact a10 x hx
  · rcases a12 x hx with ⟨t, pd, hp, hx', ht⟩ | h
    · left
      have hne : t ≠ wtx := by intro e; subst e; omega
      exact ⟨t, pd, by rw [rollback_pending_ne _ _ _ hne]; exact hp, hx', ht⟩
    · exact .inr h
  · rcases rollback_allocs_lookup fl wtx _ a ha with h | ⟨pd, hpd, -, hin⟩
    · exact a13 a h
    · exact hpa pd hpd a hin

/-- `flBelow`'s writer clause: the live writer's (`C.txid + 1`) pending entry records committed
allocating transactions. -/
theorem flBelow_wtx_alloctx (fl : FLPg) (C : CommitSt) (wo : Option Nat) (hbl : flBelow fl C wo) :
    ∀ pd, fl.pending !! W64 ((C.txid + 1 : Nat) : Int) = some pd → ∀ a ∈ pd.alloctx,
      a.toNat ≤ C.txid := by
  intro pd hp a ha
  have hT : (W64 ((C.txid + 1 : Nat) : Int)).toNat = C.txid + 1 := toNat_W64_of_lt _ hbl.2.2.2.1
  rcases hbl.2.2.1 _ pd hp with h | ⟨-, h⟩
  · rw [hT] at h; omega
  · have := h a ha; rw [hT] at this; omega

/-- `extentBytes` reads only the extent's slots. -/
theorem extentBytes_congr' (wb wb' : Nat → List w8) (f : Nat)
    (h : ∀ s, f ≤ s → s < f + (1 + pageOverflow (wb f)) → wb' s = wb s) :
    extentBytes wb' f = extentBytes wb f := by
  have hf : wb' f = wb f := h f (Nat.le_refl _) (by omega)
  unfold extentBytes
  rw [hf]
  have key : ∀ l : List Nat, (∀ s ∈ l, wb' s = wb s) → l.flatMap wb' = l.flatMap wb := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.flatMap_cons]
      rw [hl a (List.mem_cons_self), ih (fun s hs => hl s (List.mem_cons_of_mem _ hs))]
  apply key
  intro s hs
  obtain ⟨h1, h2⟩ := List.mem_range'_1.1 hs
  exact h s h1 h2

end pure

section rb
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **The writer side's facts after the rollback, flagged** (`wdbOK_rolledBack'` from `wdbOK' fr`):
the returned slots of the synced page's extent hold the bytes the writer recorded (`hrec`, from
`store_rollback` under `fbCond`), which are `w.wb`'s there (`fbRel`). -/
theorem wdbOK_rolledBack_f (fr : Bool) (w : WDb) (fl' : FLPg) (S : List Nat)
    (bs : Nat → List w8) (F : GMap Nat (List w8))
    (hok : wdbOK' fr w) (hF : fbRel w F) (hfl' : fl' = w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int)))
    (hpa : ∀ pd, w.fl.pending !! W64 ((w.C.txid + 1 : Nat) : Int) = some pd → ∀ a ∈ pd.alloctx,
      a.toNat ≤ w.C.txid)
    (hS : ∀ s, s ∈ S ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C fl')
    (h2s : ∀ s ∈ pendSlots w.fl, 2 ≤ s) (hbs : ∀ s ∈ S, (bs s).length = 4096)
    (hrec : fbCond w.C w.fl (some (w.C.txid + 1)) false →
      ∀ s ∈ S, ∀ v, F !! s = some v → bs s = v) :
    wdbOK { w with fl := fl', W := w.W ++ S, wb := mergeWb S bs w.wb } := by
  cases fr
  · exact wdbOK_rolledBack' w fl' S bs hok hfl' hS h2s hbs
  have h0 := wdbOK'_noFl true w hok
  have h1 := wdbOK_rolledBack' w.noFl fl' S bs h0 hfl' hS h2s hbs
  have hc7 : w.C.txid + 1 < 2 ^ 64 := hok.2.2.2.2.2.2.1
  have hT : (W64 ((w.C.txid + 1 : Nat) : Int)).toNat = w.C.txid + 1 := toNat_W64_of_lt _ hc7
  refine wdbOK'_of_noFl false _ h1 ?_
  intro f hf
  have hr := ((wdbOK'_flClause true w hok) f hf).2
  -- the extent's bytes are kept
  have hSm : ∀ s ∈ S, s ∈ pendSlots w.fl := by
    intro s hs
    obtain ⟨h1, h2⟩ := (hS s).1 hs
    rcases (mem_slotsOf _ _ _).1 h1 with h | h
    · exact absurd ((mem_slotsOf _ _ _).2 (.inl h)) h2
    · exact h
  have hext : extentBytes (mergeWb S bs w.wb) f = extentBytes w.wb f := by
    refine extentBytes_congr' w.wb _ f (fun s hs1 hs2 => ?_)
    simp only [mergeWb]
    split
    · rename_i hsS
      obtain ⟨⟨pd, hpd, x, hx, hxf⟩, hFs⟩ := hF f hf s hs1 hs2 (hSm s hsS)
      have hcov := ((hr f hf).2.2.2.2.2.2.2.2.1 f (Nat.le_refl _) (by omega)).1
      exact hrec ⟨rfl, w.C.txid + 1, f, pd, rfl, hf, hcov, hpd, x, hx, hxf⟩ s hsS _ hFs
    · rfl
  simp only
  rw [hext, hfl']
  exact flCurOKr_rollback w.fl w.C _ _ (by rw [hT]; omega) hpa hr

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **The synced freelist page's half across the flagged rollback** (session S4): the store hands
back the page's slots `X` (half bytes) when the writer had freed it (`fbCond`: then the writer had
no half, `flxS … = []`), nothing otherwise (then the writer keeps its half, which no slot of `S`
meets); after it, the writer's half is the one it had and `X`. -/
theorem rb_flx_facts (fr : Bool) (w : WDb) (fl' : FLPg) (S X : List Nat) (bs : Nat → List w8)
    (F : GMap Nat (List w8)) (hok : wdbOK' fr w) (hF : fbRel w F)
    (hfl' : fl' = w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int)))
    (hS : ∀ s, s ∈ S ∨ s ∈ X ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C fl')
    (hXc : (fbCond w.C w.fl (some (w.C.txid + 1)) false → X = flxS w.C fl' bs) ∧
      (¬ fbCond w.C w.fl (some (w.C.txid + 1)) false → X = [])) :
    (∀ s ∈ S, s ∉ flxS w.C w.fl w.wb) ∧ (∀ s ∈ X, s ∉ flxS w.C w.fl w.wb) ∧
      flxS w.C fl' (mergeWb (S ++ X) bs w.wb) = flxS w.C w.fl w.wb ++ X := by
  have hpS : ∀ s, s ∈ S ∨ s ∈ X → s ∈ pendSlots w.fl := by
    intro s hs
    obtain ⟨h1, h2⟩ := (hS s).1 hs
    rcases (mem_slotsOf _ _ _).1 h1 with h | h
    · exact absurd ((mem_slotsOf _ _ _).2 (.inl h)) h2
    · exact h
  have hcl := wdbOK'_flClause fr w hok
  rcases hf : w.C.flpg with _ | f
  · have e1 : flxS w.C w.fl w.wb = [] := by unfold flxS; rw [hf]
    have e2 : ∀ fl b, flxS w.C fl b = [] := by intro fl b; unfold flxS; rw [hf]
    have hX : X = [] := by
      apply hXc.2
      rintro ⟨-, _, f', _, -, hf', -⟩; rw [hf] at hf'; cases hf'
    rw [e1, e2, hX]
    exact ⟨fun _ _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim, rfl⟩
  · -- the page's `¬ covered`
    have hncov : ¬ coversSlot w.C.pages f := by
      cases fr
      · obtain ⟨-, -, -, -, -, -, -, -, hsl, -⟩ := hcl f hf f hf
        exact (hsl f (Nat.le_refl _) (by omega)).1
      · obtain ⟨-, hr⟩ := hcl f hf
        obtain ⟨-, -, -, -, -, -, -, -, hsl, -⟩ := hr f hf
        exact (hsl f (Nat.le_refl _) (by omega)).1
    by_cases hc : fbCond w.C w.fl (some (w.C.txid + 1)) false
    · have hX := hXc.1 hc
      obtain ⟨-, w0, f0, pd, hw0, hf0, -, hpd, x, hx, hxf⟩ := hc
      rw [hf] at hf0; cases hf0; cases hw0
      have hfp : f ∈ pendSlots w.fl := by
        rw [← hxf]; exact List.mem_map_of_mem (by
          simp only [FLPg.pendingIds, List.mem_flatMap]
          exact ⟨(_, pd), (GMap.mem_toList _ _ _).2 hpd, hx⟩)
      have e1 : flxS w.C w.fl w.wb = [] := by
        unfold flxS; rw [hf]; simp only [hfp, ↓reduceIte]
      rw [e1, List.nil_append]
      refine ⟨fun _ _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim, ?_⟩
      rw [hX]
      unfold flxS; rw [hf]
      by_cases hp' : f ∈ pendSlots fl'
      · simp only [hp', ↓reduceIte]
      · simp only [hp', ↓reduceIte]
        have hfX : f ∈ X := by
          rw [hX]; unfold flxS; rw [hf]; simp only [hp', ↓reduceIte]; exact f_mem_flExt _ _
        unfold flExt
        simp only [mergeWb, List.mem_append]
        rw [if_pos (Or.inr (by rw [List.mem_range'_1]; omega))]
    · have hX := hXc.2 hc
      subst hX
      -- the page is not pending: else the writer's entry frees it (`fbRel`), so `fbCond`
      have hfnp : f ∉ pendSlots w.fl := by
        intro hp
        obtain ⟨⟨pd, hpd, x, hx, hxf⟩, -⟩ :=
          hF f hf f (Nat.le_refl _) (by omega) hp
        exact hc ⟨rfl, w.C.txid + 1, f, pd, rfl, hf, hncov, hpd, x, hx, hxf⟩
      have e1 : flxS w.C w.fl w.wb = flExt w.wb f := by
        unfold flxS; rw [hf]; simp only [hfnp, ↓reduceIte]
      have hfnp' : f ∉ pendSlots fl' := fun h => hfnp (by
        rw [hfl'] at h; exact pendSlots_rollback_sub _ _ _ h)
      -- the page's slots are no pending slots
      have hext : ∀ s ∈ flExt w.wb f, s ∉ pendSlots w.fl := by
        cases fr
        · have h16 := wb_header w hok f hf
          obtain ⟨-, -, -, -, -, -, -, -, hsl, -⟩ := hcl f hf f hf
          intro s hs hp
          rw [mem_flExt] at hs
          rw [pageOverflow_extentBytes _ _ h16] at hsl
          exact (hsl s hs.1 hs.2).2 (mem_allIds_of_pend _ _ hp).1
        · obtain ⟨-, hr⟩ := hcl f hf
          obtain ⟨-, -, -, -, -, -, -, -, hsl, -⟩ := hr f hf
          exact absurd (hsl f (Nat.le_refl _) (by omega)).2.1 hfnp
      rw [e1, List.append_nil]
      refine ⟨fun s hs hx => hext s hx (hpS s (.inl hs)), fun _ h => (List.not_mem_nil h).elim, ?_⟩
      unfold flxS; rw [hf]
      simp only [hfnp', ↓reduceIte]
      have hfS : f ∉ S := fun h => hfnp (hpS f (.inl h))
      unfold flExt
      simp only [mergeWb, List.append_nil, hfS, ↓reduceIte]

omit sem in
/-- **`wdb_rollback'`, flagged** (session S4: the writer's bytes as `wBytesX`, the store handing
back the freed synced freelist page's slots `X` with half their bytes). -/
theorem wdb_rollback_f (p : BFile) (fr : Bool) (w : WDb) (fl' : FLPg) (S X : List Nat)
    (bs : Nat → List w8) (F : GMap Nat (List w8))
    (hok : wdbOK' fr w) (hF : fbRel w F) (hfl' : fl' = w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int)))
    (hpa : ∀ pd, w.fl.pending !! W64 ((w.C.txid + 1 : Nat) : Int) = some pd → ∀ a ∈ pd.alloctx,
      a.toNat ≤ w.C.txid)
    (hS : ∀ s, s ∈ S ∨ s ∈ X ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C fl')
    (hXc : (∀ s ∈ X, s ∉ S) ∧
      (fbCond w.C w.fl (some (w.C.txid + 1)) false → X = flxS w.C fl' bs) ∧
      (¬ fbCond w.C w.fl (some (w.C.txid + 1)) false → X = []))
    (h2s : ∀ s ∈ pendSlots w.fl, 2 ≤ s) (hbs : ∀ s, s ∈ S ∨ s ∈ X → (bs s).length = 4096)
    (hrec : fbCond w.C w.fl (some (w.C.txid + 1)) false →
      ∀ s, s ∈ S ∨ s ∈ X → ∀ v, F !! s = some v → bs s = v) :
    wCells (GF := GF) w.ms w.W ∗ wBytesX p w.W (flxS w.C w.fl w.wb) w.wb w.m.size ∗
        slotsOwn w.ms p S bs ∗ slotsOwnH w.ms p X bs ⊢
      ∃ w' : WDb, ⌜w'.C = w.C ∧ w'.fl = fl' ∧ w'.ms = w.ms ∧ w'.m = w.m ∧ w'.fli = w.fli ∧
          w'.junk = w.junk ∧ w'.f = w.f ∧ w'.fd = w.fd ∧ wdbOK w'⌝ ∗
        wCells w'.ms w'.W ∗ wBytesX p w'.W (flxS w'.C w'.fl w'.wb) w'.wb w'.m.size := by
  have hSX : ∀ s, s ∈ S ++ X ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C fl' := by
    intro s; rw [List.mem_append]; exact hS s
  have hok' := wdbOK_rolledBack_f fr w fl' (S ++ X) bs F hok hF hfl' hpa hSX h2s
    (fun s hs => hbs s (List.mem_append.1 hs))
    (fun hc s hs => hrec hc s (List.mem_append.1 hs))
  obtain ⟨hX0S, hX0X, hX1⟩ := rb_flx_facts fr w fl' S X bs F hok hF hfl' hS ⟨hXc.2.1, hXc.2.2⟩
  obtain ⟨-, -, c3, c4, -, -, -, -, c9, -, c11, -⟩ := hok
  have hpS : ∀ s, s ∈ S ∨ s ∈ X → s ∈ pendSlots w.fl := by
    intro s hs
    obtain ⟨h1, h2⟩ := (hS s).1 hs
    rcases (mem_slotsOf _ _ _).1 h1 with h | h
    · exact absurd ((mem_slotsOf _ _ _).2 (.inl h)) h2
    · exact h
  have hnW : ∀ s, s ∈ S ∨ s ∈ X → s ∉ w.W := fun s hs hw => ((c4 s).1 hw).2.2.2 (hpS s hs)
  have hin : ∀ s, s ∈ S ∨ s ∈ X → 4096 * (s + 1) ≤ w.m.size ∧
      (∀ b l, w.ms = some (b, l) → 4096 * (s + 1) ≤ l) ∧ (bs s).length = 4096 := by
    intro s hs
    have := c11 s (.inr (hpS s hs))
    refine ⟨by omega, fun b l hbl => ?_, hbs s hs⟩
    have := c9 b l hbl; omega
  let X0 := flxS w.C w.fl w.wb
  have hj := wjoin2 (GF := GF) p w.ms w.W (w.W.filter (fun s => decide (s ∉ X0))) S w.wb bs
    w.m.size (fun s hs hw => hnW s (.inl hs) (List.mem_filter.1 hw).1)
    (fun s hs => hin s (.inl hs))
  have hjH := wjoinH (GF := GF) p w.ms (w.W ++ S) X bs
    (fun s hs => ⟨(hin s (.inr hs)).2.1, (hin s (.inr hs)).2.2⟩)
  -- the lists and the bytes after the join
  have hfilt : (w.W ++ (S ++ X)).filter (fun s => decide (s ∉ X0 ++ X)) =
      w.W.filter (fun s => decide (s ∉ X0)) ++ S := by
    rw [List.filter_append, List.filter_append]
    have e1 : w.W.filter (fun s => decide (s ∉ X0 ++ X)) = w.W.filter (fun s => decide (s ∉ X0)) := by
      apply List.filter_congr; intro s hs
      have : s ∉ X := fun h => hnW s (.inr h) hs
      simp [X0, this]
    have e2 : S.filter (fun s => decide (s ∉ X0 ++ X)) = S := by
      rw [List.filter_eq_self]; intro s hs
      have h1 := hX0S s hs
      have h2 : s ∉ X := fun h => hXc.1 s h hs
      simp [X0, h1, h2]
    have e3 : X.filter (fun s => decide (s ∉ X0 ++ X)) = [] := by
      rw [List.filter_eq_nil_iff]; intro s hs; simp [hs]
    rw [e1, e2, e3, List.append_nil]
  have hmS : ∀ s ∈ w.W.filter (fun s => decide (s ∉ X0)) ++ S,
      mergeWb S bs w.wb s = mergeWb (S ++ X) bs w.wb s := by
    intro s hs
    rcases List.mem_append.1 hs with h | h
    · have h1 : s ∉ S := fun h' => hnW s (.inl h') (List.mem_filter.1 h).1
      have h2 : s ∉ X := fun h' => hnW s (.inr h') (List.mem_filter.1 h).1
      simp [mergeWb, h1, h2]
    · simp [mergeWb, h]
  have hm0 : ∀ s ∈ X0, w.wb s = mergeWb (S ++ X) bs w.wb s := by
    intro s hs
    have h1 : s ∉ S := fun h => hX0S s h hs
    have h2 : s ∉ X := fun h => hX0X s h hs
    simp [mergeWb, h1, h2]
  have hmX : ∀ s ∈ X, bs s = mergeWb (S ++ X) bs w.wb s := by
    intro s hs; simp [mergeWb, hs]
  iintro ⟨Hc, Hbx, HS, HX⟩
  iunfold wBytesX at Hbx
  icases Hbx with ⟨Hb, H0⟩
  ihave ⟨Hc, Hb⟩ := hj $$ [Hc Hb HS]
  · iframe
  ihave ⟨Hc, HXh⟩ := hjH $$ [Hc HX]
  · iframe
  iexists { w with fl := fl', W := w.W ++ (S ++ X), wb := mergeWb (S ++ X) bs w.wb }
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hok'⟩
  simp only
  rw [hX1, List.append_assoc]
  iframe Hc
  unfold wBytesX
  rw [hfilt]
  isplitl [Hb]
  · unfold wBytes
    iapply BigSepL.bigSepL_mono (Φ := fun _ s => (if 4096 * (s + 1) ≤ w.m.size then
        iprop(∃ xs : List ByteG, bBytes p (4096 * s) (DFrac.own 1) xs ∗
          ⌜xs.map Prod.fst = mergeWb S bs w.wb s⌝)
        else if 4096 * s < w.m.size then
          iprop(∃ xs : List ByteG, bBytes p (4096 * s) (DFrac.own 1) xs ∗
            ⌜xs.map Prod.fst = (mergeWb S bs w.wb s).take (w.m.size - 4096 * s)⌝)
        else iprop(emp) : IProp GF)) ?_ $$ Hb
    intro k x hk
    rw [hmS x (List.mem_of_getElem? hk)]
  iapply BigSepL.bigSepL_append.2
  isplitl [H0]
  · iapply BigSepL.bigSepL_mono (Φ := fun _ s => osSlotH (GF := GF) p s (w.wb s)) ?_ $$ H0
    intro k x hk
    rw [hm0 x (List.mem_of_getElem? hk)]
  · iapply BigSepL.bigSepL_mono (Φ := fun _ s => osSlotH (GF := GF) p s (bs s)) ?_ $$ HXh
    intro k x hk
    rw [hmX x (List.mem_of_getElem? hk)]

end rb

end bbolt
end EtcdGrove
end Perennial
