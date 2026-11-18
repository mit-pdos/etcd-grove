/-
The page store's transitions keep the synced freelist page's facts (`flxOK`, `Model/StoreFl.lean`;
session S4): one lemma per transition of `Model/Store.lean` that `Inv/Store.lean` takes, under the
transition's side conditions (mostly those of the matching `storeOK_*`), and what a registering
reader learns of its page (`fxOK_fxOf`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.StoreFl

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

section storeflok
variable [GooseExts]

/-! ## Helpers -/

theorem pageOverflow_append' (a b : List w8) (h : 16 ≤ a.length) :
    pageOverflow (a ++ b) = pageOverflow a := by
  unfold pageOverflow pageHdr bytesAt
  simp only [List.drop_zero]
  rw [List.take_append_of_le_length h]

theorem extentBytes_cons (bytes : Nat → List w8) (f : Nat) :
    extentBytes bytes f = bytes f ++ (List.range' (f + 1) (pageOverflow (bytes f))).flatMap bytes := by
  unfold extentBytes
  rw [show 1 + pageOverflow (bytes f) = pageOverflow (bytes f) + 1 by omega, List.range'_succ,
    List.flatMap_cons]

theorem pageOverflow_extentBytes (bytes : Nat → List w8) (f : Nat) (h : 16 ≤ (bytes f).length) :
    pageOverflow (extentBytes bytes f) = pageOverflow (bytes f) := by
  rw [extentBytes_cons]; exact pageOverflow_append' _ _ h

theorem flatMap_range'_len (g : Nat → List w8) :
    ∀ (k a : Nat), (∀ s, a ≤ s → s < a + k → (g s).length = 4096) →
      ((List.range' a k).flatMap g).length = 4096 * k
  | 0, a, _ => by simp
  | k + 1, a, h => by
    rw [List.range'_succ, List.flatMap_cons, List.length_append, h a (Nat.le_refl _) (by omega),
      flatMap_range'_len g k (a + 1) (fun s h1 h2 => h s (by omega) (by omega))]
    omega

theorem mem_flExt (bytes : Nat → List w8) (f s : Nat) :
    s ∈ flExt bytes f ↔ f ≤ s ∧ s < f + (1 + pageOverflow (bytes f)) := by
  unfold flExt; rw [List.mem_range'_1]

theorem extentBytes_length (bytes : Nat → List w8) (f : Nat)
    (h : ∀ s ∈ flExt bytes f, (bytes s).length = 4096) :
    (extentBytes bytes f).length = 4096 * (1 + pageOverflow (bytes f)) :=
  flatMap_range'_len bytes _ f (fun s h1 h2 => h s ((mem_flExt _ _ _).2 ⟨h1, h2⟩))

theorem f_mem_flExt (bytes : Nat → List w8) (f : Nat) : f ∈ flExt bytes f :=
  (mem_flExt _ _ _).2 ⟨Nat.le_refl _, by omega⟩

/-- The current page's slots lie below the high-water mark. -/
theorem flExt_lt_hwm (C : CommitSt) (bytes : Nat → List w8) (f : Nat)
    (hok : flPgOK C f (extentBytes bytes f)) (hl : (bytes f).length = 4096) (s : Nat)
    (hs : s ∈ flExt bytes f) : 2 ≤ s ∧ s < C.hwm := by
  have h1 := hok.1
  have h2 := hok.2.1
  rw [pageOverflow_extentBytes _ _ (by omega)] at h2
  have := (mem_flExt _ _ _).1 hs
  omega

theorem W64_toNat_lt (s : Nat) (h : s < 2 ^ 64) : (W64 (s : Int)).toNat = s := by
  simp only [W64, BitVec.toNat_ofInt]; omega

/-- A reader's facts depend on the committed state, the freelist and the bytes only. -/
theorem rdFlOK_congr (σ σ' : StoreSt) (r : RdInfo) (hC : σ'.C = σ.C) (hfl : σ'.fl = σ.fl)
    (hb : σ'.bytes = σ.bytes) (h : rdFlOK σ r) : rdFlOK σ' r := by
  unfold rdFlOK at *
  rw [hC, hfl, hb]; exact h

theorem flxOK_congr (σ σ' : StoreSt) (hC : σ'.C = σ.C) (hfl : σ'.fl = σ.fl)
    (hb : σ'.bytes = σ.bytes) (hR : σ'.R = σ.R) (hw : σ'.wtx = σ.wtx) (hp : σ'.pub = σ.pub)
    (h : flxOK σ) : flxOK σ' := by
  unfold flxOK rdFlOK at *
  rw [hC, hfl, hb, hR, hw, hp]; exact h

/-! ## Registration -/

/-- **What a registering reader learns of its page.** -/
theorem fxOK_fxOf (σ : StoreSt) (hfx : flxOK σ) : fxOK σ.C (fxOf σ) := by
  unfold fxOK fxOf
  rcases hf : σ.C.flpg with _ | f
  · rfl
  · obtain ⟨hpg, hsl, -⟩ := hfx.1 f hf
    refine ⟨_, rfl, hpg, ?_⟩
    have hl : ∀ s ∈ flExt σ.bytes f, (σ.bytes s).length = 4096 := fun s hs => (hsl s hs).1
    rw [extentBytes_length _ _ hl,
      pageOverflow_extentBytes _ _ (by rw [hl f (f_mem_flExt _ _)]; omega)]

theorem flxOK_register (σ : StoreSt) (k : Nat) (r : RdInfo) (h : storeOK σ) (hfx : flxOK σ)
    (hv : r.v.txid = σ.C.txid) (hr : r.fx = fxOf σ) : flxOK (σ.register k r) := by
  obtain ⟨hf1, hf2⟩ := hfx
  refine ⟨hf1, fun k' r' hr' => ?_⟩
  simp only [StoreSt.register] at hr'
  by_cases hk : k = k'
  · subst hk
    rw [GMap.lookup_insert] at hr'
    cases hr'
    refine rdFlOK_congr σ _ _ rfl rfl rfl ?_
    intro f bs hfb
    rw [hr] at hfb
    unfold fxOf at hfb
    rcases hf : σ.C.flpg with _ | f'
    · rw [hf] at hfb; cases hfb
    rw [hf] at hfb
    cases hfb
    obtain ⟨hpg, hsl, hal⟩ := hf1 f hf
    refine ⟨rfl, fun s hs => (hsl s hs).1, fun a ha => hv ▸ hal a ha, ?_⟩
    by_cases hp : f ∈ pendSlots σ.fl
    · right
      intro s hs
      obtain ⟨-, hnf, hiff, hpo, hat⟩ := hsl s hs
      refine ⟨hiff.2 hp, hnf, fun t pd i hpd hi => ?_⟩
      obtain ⟨hpub, hpo⟩ := hpo hp
      have hwt := hpo t pd hpd (List.mem_of_getElem? hi)
      have h5 := h.2.2.2.2.1 _ hwt
      simp only [hpub, Bool.false_eq_true, ↓reduceIte] at h5
      refine ⟨hv ▸ hat t pd i hpd hi, by omega, Or.inr rfl⟩
    · exact Or.inl ⟨rfl, hp⟩
  · rw [GMap.lookup_insert_ne _ _ hk] at hr'
    exact rdFlOK_congr σ _ _ rfl rfl rfl (hf2 k' r' hr')

theorem flxOK_deregister (σ : StoreSt) (k : Nat) (hfx : flxOK σ) : flxOK (σ.deregister k) := by
  obtain ⟨hf1, hf2⟩ := hfx
  refine ⟨hf1, fun k' r' hr' => ?_⟩
  simp only [StoreSt.deregister] at hr'
  by_cases hk : k = k'
  · subst hk; rw [GMap.lookup_delete] at hr'; cases hr'
  · rw [GMap.lookup_delete_ne _ hk] at hr'
    exact rdFlOK_congr σ _ _ rfl rfl rfl (hf2 k' r' hr')

/-! ## The writer's begin and close -/

/-- With no live writer, the committed state's page is not pending. -/
theorem flx_not_pend_none (σ : StoreSt) (h : storeOK σ) (hfx : flxOK σ) (hw : σ.wtx = none)
    (f : Nat) (hf : σ.C.flpg = some f) : f ∉ pendSlots σ.fl := by
  intro hp
  obtain ⟨-, hsl, -⟩ := hfx.1 f hf
  obtain ⟨-, -, -, hpo, -⟩ := hsl f (f_mem_flExt _ _)
  obtain ⟨-, hpo⟩ := hpo hp
  obtain ⟨t, pd, x, hpd, hx, hxs⟩ := (mem_pendSlots_iff _ _).1 hp
  have := hpo t pd hpd (by rw [← hxs, show W64 (x.toNat : Int) = x from by
    apply BitVec.eq_of_toNat_eq; simp only [W64, BitVec.toNat_ofInt]; omega]; exact hx)
  rw [hw] at this; cases this

theorem flxOK_wbegin (σ : StoreSt) (v : View) (h : storeOK σ) (hfx : flxOK σ)
    (hw : σ.wtx = none) : flxOK (σ.wbegin v) := by
  obtain ⟨hf1, hf2⟩ := hfx
  refine ⟨fun f hf => ?_, fun k r hr => rdFlOK_congr σ _ _ rfl rfl rfl (hf2 k r hr)⟩
  obtain ⟨hpg, hsl, hal⟩ := hf1 f hf
  have hnp := flx_not_pend_none σ h ⟨hf1, hf2⟩ hw f hf
  refine ⟨hpg, fun s hs => ?_, hal⟩
  obtain ⟨a, b, c, -, e⟩ := hsl s hs
  exact ⟨a, b, c, fun hp => absurd hp hnp, e⟩

theorem flxOK_wclose (σ : StoreSt) (h : storeOK σ) (hfx : flxOK σ)
    (hp : σ.pub = true ∨ ∀ w, σ.wtx = some w → σ.fl.pending !! W64 (w : Int) = none) :
    flxOK σ.wclose := by
  obtain ⟨hf1, hf2⟩ := hfx
  refine ⟨fun f hf => ?_, fun k r hr => rdFlOK_congr σ _ _ rfl rfl rfl (hf2 k r hr)⟩
  obtain ⟨hpg, hsl, hal⟩ := hf1 f hf
  -- the page is not pending: only the live writer frees it before its publish
  have hnp : f ∉ pendSlots σ.fl := by
    intro hpd
    obtain ⟨-, -, -, hpo, -⟩ := hsl f (f_mem_flExt _ _)
    obtain ⟨hpub, hpo⟩ := hpo hpd
    obtain ⟨t, pd, x, hp', hx, hxs⟩ := (mem_pendSlots_iff _ _).1 hpd
    have hxe : W64 (x.toNat : Int) = x := by
      apply BitVec.eq_of_toNat_eq; simp only [W64, BitVec.toNat_ofInt]; omega
    have hwt := hpo t pd hp' (by rw [← hxs, hxe]; exact hx)
    rcases hp with hp | hp
    · rw [hpub] at hp; cases hp
    · have := hp _ hwt
      rw [show W64 (t.toNat : Int) = t from by
        apply BitVec.eq_of_toNat_eq; simp only [W64, BitVec.toNat_ofInt]; omega] at this
      rw [this] at hp'; cases hp'
  refine ⟨hpg, fun s hs => ?_, hal⟩
  obtain ⟨a, b, c, -, e⟩ := hsl s hs
  exact ⟨a, b, c, fun hp => absurd hp hnp, e⟩

/-! ## Allocation, reload -/

theorem flxOK_alloc (σ : StoreSt) (T r : w64) (n : Nat) (hfx : flxOK σ) (hrf : r ∈ σ.fl.free) :
    flxOK (σ.alloc T r n) := by
  obtain ⟨hf1, hf2⟩ := hfx
  have hpend : pendSlots (σ.alloc T r n).fl = pendSlots σ.fl := rfl
  have hfree : ∀ x, x ∈ (σ.alloc T r n).fl.free → x ∈ σ.fl.free := by
    intro x hx
    simp only [StoreSt.alloc, FLPg.alloc, List.mem_filter] at hx
    exact hx.1
  have hal : ∀ x a, x ≠ r → (σ.alloc T r n).fl.allocs !! x = some a → σ.fl.allocs !! x = some a := by
    intro x a hx ha
    simp only [StoreSt.alloc, FLPg.alloc] at ha
    rwa [GMap.lookup_insert_ne _ _ (Ne.symm hx)] at ha
  refine ⟨fun f hf => ?_, fun k r' hr' => ?_⟩
  · obtain ⟨hpg, hsl, hall⟩ := hf1 f hf
    have hfr : W64 (f : Int) ≠ r := fun e => (hsl f (f_mem_flExt _ _)).2.1 (e ▸ hrf)
    refine ⟨hpg, fun s hs => ?_, fun a ha => hall a (hal _ a hfr ha)⟩
    obtain ⟨a, b, c, d, e⟩ := hsl s hs
    exact ⟨a, fun hx => b (hfree _ hx), c, d, e⟩
  · intro f bs hfb
    obtain ⟨h1, h2, h3, h4⟩ := hf2 k r' hr' f bs hfb
    have hfr : W64 (f : Int) ≠ r := by
      intro e
      rcases h4 with ⟨hf, -⟩ | h4
      · exact (hf1 f hf).2.1 f (f_mem_flExt _ _) |>.2.1 (e ▸ hrf)
      · exact (h4 f (f_mem_flExt _ _)).2.1 (e ▸ hrf)
    refine ⟨h1, h2, fun a ha => h3 a (hal _ a hfr ha), ?_⟩
    rcases h4 with h4 | h4
    · exact Or.inl h4
    · exact Or.inr fun s hs => by
        obtain ⟨a, b, c⟩ := h4 s hs
        exact ⟨a, fun hx => b (hfree _ hx), c⟩

theorem flxOK_reload (σ : StoreSt) (ids : List w64) (h : storeOK σ) (hfx : flxOK σ)
    (hids : ∀ f, σ.C.flpg = some f → f ∉ pendSlots σ.fl → ∀ x ∈ ids, x.toNat ∉ flExt σ.bytes f) :
    flxOK (σ.reload ids) := by
  obtain ⟨hf1, hf2⟩ := hfx
  have hfree : ∀ x, x ∈ (σ.reload ids).fl.free → x ∈ ids ∧ x ∉ σ.fl.pendingIds := by
    intro x hx
    simp only [StoreSt.reload, FLPg.reload] at hx
    have := (List.mem_mergeSort (le := fun x y : w64 => decide (x.toNat ≤ y.toNat))).1 hx
    simpa using this
  have hpend : pendSlots (σ.reload ids).fl = pendSlots σ.fl := rfl
  refine ⟨fun f hf => ?_, fun k r hr f bs hfb => ?_⟩
  · obtain ⟨hpg, hsl, hall⟩ := hf1 f hf
    refine ⟨hpg, fun s hs => ?_, hall⟩
    obtain ⟨a, b, c, d, e⟩ := hsl s hs
    refine ⟨a, fun hx => ?_, c, d, e⟩
    have hlt := flExt_lt_hwm σ.C σ.bytes f hpg (hsl f (f_mem_flExt _ _)).1 s hs
    have hs64 : s < 2 ^ 64 := by
      have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
    by_cases hfp : f ∈ pendSlots σ.fl
    · obtain ⟨t, pd, x, hp, hx', hxs⟩ := (mem_pendSlots_iff _ _).1 (c.2 hfp)
      apply (hfree _ hx).2
      rw [show W64 (s : Int) = x from by
        rw [← hxs]; apply BitVec.eq_of_toNat_eq; simp only [W64, BitVec.toNat_ofInt]; omega]
      simp only [FLPg.pendingIds, List.mem_flatMap]
      exact ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx'⟩
    · have := hids f hf hfp _ (hfree _ hx).1
      rw [W64_toNat_lt s hs64] at this
      exact this hs
  · obtain ⟨h1, h2, h3, h4⟩ := hf2 k r hr f bs hfb
    refine ⟨h1, h2, h3, ?_⟩
    rcases h4 with h4 | h4
    · exact Or.inl h4
    · refine Or.inr fun s hs => ?_
      obtain ⟨a, -, c⟩ := h4 s hs
      refine ⟨a, fun hx => ?_, c⟩
      obtain ⟨t, pd, x, hp, hx', hxs⟩ := (mem_pendSlots_iff _ _).1 a
      apply (hfree _ hx).2
      have hxe : W64 (s : Int) = x := by
        rw [← hxs]; apply BitVec.eq_of_toNat_eq; simp only [W64, BitVec.toNat_ofInt]; omega
      rw [hxe]
      simp only [FLPg.pendingIds, List.mem_flatMap]
      exact ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx'⟩

theorem flxOK_setFl (σ : StoreSt) (fl : FLPg) (hfx : flxOK σ) (hR : σ.R = ∅)
    (hfl : fl.pending = ∅ ∧ fl.allocs = ∅)
    (hfree : ∀ f, σ.C.flpg = some f → ∀ s ∈ flExt σ.bytes f, W64 (s : Int) ∉ fl.free) :
    flxOK (σ.setFl fl) := by
  obtain ⟨hf1, -⟩ := hfx
  have hnp : ∀ s, s ∉ pendSlots fl := by
    intro s hs
    obtain ⟨t, pd, x, hp, -, -⟩ := (mem_pendSlots_iff _ _).1 hs
    rw [hfl.1] at hp; simp at hp
  refine ⟨fun f hf => ?_, fun k r hr => ?_⟩
  · obtain ⟨hpg, hsl, -⟩ := hf1 f hf
    refine ⟨hpg, fun s hs => ⟨(hsl s hs).1, hfree f hf s hs, ?_, fun h => absurd h (hnp _),
      fun t pd i hp _ => ?_⟩, fun a ha => ?_⟩
    · simp only [StoreSt.setFl]; exact ⟨fun h => absurd h (hnp _), fun h => absurd h (hnp _)⟩
    · simp only [StoreSt.setFl, hfl.1] at hp; simp at hp
    · simp only [StoreSt.setFl, hfl.2] at ha; simp at ha
  · simp only [StoreSt.setFl, hR] at hr; simp at hr

/-! ## Free, publish, rollback, release -/

theorem W64_toNat_self (x : w64) : W64 (x.toNat : Int) = x := by
  apply BitVec.eq_of_toNat_eq; simp only [W64, BitVec.toNat_ofInt]; omega

theorem mem_allIds_of_pend (fl : FLPg) (s : Nat) (hs : s ∈ pendSlots fl) :
    W64 (s : Int) ∈ fl.allIds ∧ s < 2 ^ 64 := by
  obtain ⟨t, pd, x, hp, hx, rfl⟩ := (mem_pendSlots_iff _ _).1 hs
  refine ⟨?_, x.isLt⟩
  rw [W64_toNat_self]
  simp only [FLPg.allIds, FLPg.pendingIds, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩

theorem pend_of_entry (fl : FLPg) (t : w64) (pd : Pending) (i : Nat) (s : Nat) (hs : s < 2 ^ 64)
    (hp : fl.pending !! t = some pd) (hi : pd.ids[i]? = some (W64 (s : Int))) : s ∈ pendSlots fl :=
  (mem_pendSlots_iff _ _).2 ⟨t, pd, _, hp, List.mem_of_getElem? hi, W64_toNat_lt s hs⟩

/-- An entry of the freelist after `Free`: an old entry's id with its allocating transaction, or
an id of the run in the freeing transaction's entry, with the page's. -/
theorem freePages_entry (fl : FLPg) (T id : w64) (n : Nat) (t : w64) (pd : Pending) (i : Nat)
    (x : w64) (hwf : ∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length)
    (h : (fl.freePages T id n).pending !! t = some pd) (hi : pd.ids[i]? = some x) :
    (∃ pd0, fl.pending !! t = some pd0 ∧ pd0.ids[i]? = some x ∧
      pd.alloctx.getD i 0 = pd0.alloctx.getD i 0) ∨
    (t = T ∧ x ∈ runIds id n ∧ pd.alloctx.getD i 0 = (fl.allocs !! id).getD 0) := by
  rcases freePages_pending_lookup fl T id n t pd h with ⟨-, hp⟩ | ⟨rfl, P, hP, rfl⟩
  · exact Or.inl ⟨pd, hp, hi, rfl⟩
  · rcases hq : fl.pending !! t with _ | q
    · rw [hq] at hP; simp only [Option.getD_none] at hP; subst hP
      simp only [List.nil_append] at hi ⊢
      right
      refine ⟨by first | trivial | rfl, List.mem_of_getElem? hi, ?_⟩
      have hlt : i < n := by
        have := (List.getElem?_eq_some_iff.1 hi).1; simpa [runIds] using this
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hlt]; rfl
    · rw [hq] at hP; simp only [Option.getD_some] at hP; subst hP
      have hl := hwf t _ hq
      by_cases hil : i < q.ids.length
      · left
        refine ⟨q, rfl, by rwa [List.getElem?_append_left hil] at hi, ?_⟩
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      · right
        rw [List.getElem?_append_right (by omega)] at hi
        refine ⟨rfl, List.mem_of_getElem? hi, ?_⟩
        have hlt : i - q.ids.length < n := by
          have := (List.getElem?_eq_some_iff.1 hi).1; simpa [runIds] using this
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), List.getElem?_replicate, if_pos (by omega)]
        rfl

theorem flExt_congr (b b' : Nat → List w8) (f : Nat) (h : ∀ s ∈ flExt b f, b' s = b s) :
    flExt b' f = flExt b f ∧ extentBytes b' f = extentBytes b f := by
  have hf : b' f = b f := h f (f_mem_flExt _ _)
  have e : flExt b' f = flExt b f := by unfold flExt; rw [hf]
  refine ⟨e, ?_⟩
  show (flExt b' f).flatMap b' = (flExt b f).flatMap b
  rw [e]
  generalize flExt b f = L at h
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem flxOK_free (σ : StoreSt) (w : Nat) (id : w64) (n : Nat) (pg : Nat → List w8)
    (h : storeOK σ) (hfx : flxOK σ) (hw : σ.wtx = some w) (hpub : σ.pub = false)
    (hcan : σ.fl.canFree (W64 (w : Int)) id n)
    (hpg : ∀ j < n, pg (id.toNat + j) = σ.bytes (id.toNat + j))
    (hcase : (∃ p, σ.C.pages !! id.toNat = some p ∧ 1 + pageOverflow p = n) ∨
      (σ.C.flpg = some id.toNat ∧ n = 1 + pageOverflow (σ.bytes id.toNat))) :
    flxOK (σ.free (W64 (w : Int)) id n pg) := by
  obtain ⟨hf1, hf2⟩ := hfx
  have h5 := h.2.2.2.2.1 w hw
  simp only [hpub, Bool.false_eq_true, ↓reduceIte] at h5
  have hsm : σ.C.txid + 1 < 2 ^ 64 := h.2.2.1.2.2.2.1
  have hwf := h.2.2.2.1.2.2.2.2
  have hT : (W64 (w : Int)).toNat = w := W64_toNat_lt w (by omega)
  obtain ⟨hc2, hcn, hcfresh, hcal, -⟩ := hcan
  have hrun : ∀ x, x ∈ runIds id n ↔ id.toNat ≤ x.toNat ∧ x.toNat < id.toNat + n :=
    runIds_mem_toNat id n hcn
  have hb : ∀ s, s < 2 ^ 64 → (σ.free (W64 (w : Int)) id n pg).bytes s = σ.bytes s := by
    intro s hs
    simp only [StoreSt.free]
    split
    · rename_i hr
      unfold inRun at hr
      rw [W64_toNat_lt s hs] at hr
      have := hpg (s - id.toNat) (by omega)
      rwa [show id.toNat + (s - id.toNat) = s by omega] at this
    · rfl
  have hpend : ∀ s, s ∈ pendSlots (σ.free (W64 (w : Int)) id n pg).fl ↔
      s ∈ pendSlots σ.fl ∨ (id.toNat ≤ s ∧ s < id.toNat + n) := pendSlots_freePages _ _ _ _ hcn
  -- a pending slot is not in the run
  have hpnr : ∀ s, s ∈ pendSlots σ.fl → ¬ (id.toNat ≤ s ∧ s < id.toNat + n) := by
    intro s hs hr
    obtain ⟨ha, hs64⟩ := mem_allIds_of_pend _ _ hs
    exact hcfresh _ ((hrun _).2 (by rw [W64_toNat_lt s hs64]; exact hr)) ha
  -- the current page's slots: in the run (the page's free) or disjoint from it (a tree page's)
  have hcur : ∀ f, σ.C.flpg = some f → (∀ s ∈ flExt σ.bytes f, s < 2 ^ 62) ∧
      ((id.toNat = f ∧ ∀ s, s ∈ flExt σ.bytes f ↔ id.toNat ≤ s ∧ s < id.toNat + n) ∨
       ∀ s ∈ flExt σ.bytes f, ¬ (id.toNat ≤ s ∧ s < id.toNat + n)) := by
    intro f hf
    obtain ⟨hpgok, hsl, -⟩ := hf1 f hf
    have hlen := (hsl f (f_mem_flExt _ _)).1
    have hlt : ∀ s ∈ flExt σ.bytes f, s < 2 ^ 62 := fun s hs => by
      have := flExt_lt_hwm σ.C σ.bytes f hpgok hlen s hs
      have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
    refine ⟨hlt, ?_⟩
    rcases hcase with ⟨p, hp, hpn⟩ | ⟨hfid, hn⟩
    · right
      intro s hs hr
      have hcov : coversSlot σ.C.pages s := ⟨id.toNat, p, hp, hr.1, by omega⟩
      have hov := hpgok.2.2.2.2.2.2.2.1
      rw [pageOverflow_extentBytes _ _ (by omega)] at hov
      exact hov s ((mem_flExt _ _ _).1 hs).1 ((mem_flExt _ _ _).1 hs).2 hcov
    · rw [hf] at hfid; cases hfid
      left
      refine ⟨rfl, fun s => ?_⟩
      rw [mem_flExt, hn]
  refine ⟨fun f hf => ?_, fun k r hr => ?_⟩
  · -- the committed state's page
    obtain ⟨hpgok, hsl, hall⟩ := hf1 f hf
    obtain ⟨hlt, hcase'⟩ := hcur f hf
    have hext := flExt_congr σ.bytes (σ.free (W64 (w : Int)) id n pg).bytes f
      (fun s hs => hb s (by have := hlt s hs; omega))
    have hC : (σ.free (W64 (w : Int)) id n pg).C = σ.C := rfl
    rw [hext.1, hext.2, hC]
    refine ⟨hpgok, fun s hs => ?_, fun a ha => ?_⟩
    · obtain ⟨hl, hnf, hiff, hpo, hat⟩ := hsl s hs
      have hs64 : s < 2 ^ 64 := by have := hlt s hs; omega
      have hf64 : f < 2 ^ 64 := by have := hlt f (f_mem_flExt _ _); omega
      refine ⟨by rw [hb s hs64]; exact hl, hnf, ?_, ?_, ?_⟩
      · rw [hpend, hpend]
        rcases hcase' with ⟨hid, hrs⟩ | hdis
        · exact ⟨fun _ => Or.inr ((hrs f).1 (f_mem_flExt _ _)), fun _ => Or.inr ((hrs s).1 hs)⟩
        · have := hdis s hs; have := hdis f (f_mem_flExt _ _)
          constructor <;> rintro (h' | h') <;> first | exact absurd h' ‹_› | skip
          · exact Or.inl (hiff.1 h')
          · exact Or.inl (hiff.2 h')
      · intro hfp
        refine ⟨hpub, fun t pd hp hx => ?_⟩
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
        rcases freePages_entry σ.fl _ id n t pd i _ hwf hp hi with ⟨pd0, hp0, hi0, -⟩ | ⟨rfl, -, -⟩
        · have hsp : s ∈ pendSlots σ.fl := pend_of_entry _ t pd0 i s hs64 hp0 hi0
          exact (hpo (hiff.1 hsp)).2 t pd0 hp0 (List.mem_of_getElem? hi0)
        · rw [hT]; exact hw
      · intro t pd i hp hi
        rcases freePages_entry σ.fl _ id n t pd i _ hwf hp hi with ⟨pd0, hp0, hi0, he⟩ |
          ⟨rfl, hxr, he⟩
        · rw [he]; exact hat t pd0 i hp0 hi0
        · rw [he]
          rcases hcase' with ⟨hid, -⟩ | hdis
          · rcases hq : σ.fl.allocs !! id with _ | a
            · simp
            · simp only [Option.getD_some]
              apply hall a; rw [← hid, W64_toNat_self]; exact hq
          · exfalso
            have := (hrun _).1 hxr
            rw [W64_toNat_lt s hs64] at this
            exact hdis s hs this
    · simp only [StoreSt.free, FLPg.freePages] at ha
      by_cases he : id = W64 (f : Int)
      · rw [he, GMap.lookup_delete] at ha; cases ha
      · rw [GMap.lookup_delete_ne _ he] at ha; exact hall a ha
  · intro f bs hfb
    obtain ⟨r1, r2, r3, r4⟩ := hf2 k r hr f bs hfb
    have hrtx : r.v.txid ≤ σ.C.txid := (h.2.2.2.2.2.2.1 k r hr).1
    have hlt : ∀ s ∈ flExt σ.bytes f, s < 2 ^ 64 := by
      rcases r4 with ⟨hf, -⟩ | r4
      · intro s hs; have := (hcur f hf).1 s hs; omega
      · intro s hs; exact (mem_allIds_of_pend _ _ (r4 s hs).1).2
    have hext := flExt_congr σ.bytes (σ.free (W64 (w : Int)) id n pg).bytes f
      (fun s hs => hb s (hlt s hs))
    have hC : (σ.free (W64 (w : Int)) id n pg).C = σ.C := rfl
    have hfree : (σ.free (W64 (w : Int)) id n pg).fl.free = σ.fl.free := rfl
    rw [hext.1, hext.2, hC, hfree]
    refine ⟨r1, fun s hs => by rw [hb s (hlt s hs)]; exact r2 s hs, fun a ha => ?_, ?_⟩
    · simp only [StoreSt.free, FLPg.freePages] at ha
      by_cases he : id = W64 (f : Int)
      · rw [he, GMap.lookup_delete] at ha; cases ha
      · rw [GMap.lookup_delete_ne _ he] at ha; exact r3 a ha
    · rcases r4 with ⟨hf, hnp⟩ | r4
      · obtain ⟨-, hcase'⟩ := hcur f hf
        rcases hcase' with ⟨hid, hrs⟩ | hdis
        · right
          intro s hs
          have hs64 := hlt s hs
          refine ⟨(hpend s).2 (Or.inr ((hrs s).1 hs)), ((hf1 f hf).2.1 s hs).2.1,
            fun t pd i hp hi => ?_⟩
          rcases freePages_entry σ.fl _ id n t pd i _ hwf hp hi with ⟨pd0, hp0, hi0, -⟩ |
            ⟨rfl, -, he⟩
          · exact absurd ((hrs s).1 hs) (hpnr s (pend_of_entry _ t pd0 i s hs64 hp0 hi0))
          · rw [he, hT]
            refine ⟨?_, by omega, Or.inr hf⟩
            rcases hq : σ.fl.allocs !! id with _ | a
            · simp
            · simp only [Option.getD_some]
              apply r3 a; rw [← hid, W64_toNat_self]; exact hq
        · left
          refine ⟨hf, fun hp' => ?_⟩
          rcases (hpend f).1 hp' with h' | h'
          · exact hnp h'
          · exact hdis f (f_mem_flExt _ _) h'
      · right
        intro s hs
        obtain ⟨a, b, c⟩ := r4 s hs
        have hs64 := hlt s hs
        refine ⟨(hpend s).2 (Or.inl a), b, fun t pd i hp hi => ?_⟩
        rcases freePages_entry σ.fl _ id n t pd i _ hwf hp hi with ⟨pd0, hp0, hi0, he⟩ |
          ⟨rfl, hxr, -⟩
        · rw [he]; exact c t pd0 i hp0 hi0
        · exfalso
          have := (hrun _).1 hxr
          rw [W64_toNat_lt s hs64] at this
          exact hpnr s a this

theorem flxOK_publish (σ : StoreSt) (w : Nat) (C' : CommitSt) (bs : Nat → List w8)
    (h : storeOK σ) (hfx : flxOK σ) (hw : σ.wtx = some w) (hpub : σ.pub = false)
    (ht : C'.txid = w) (hC' : C'.flpg = none)
    (hfreed : ∀ f, σ.C.flpg = some f → f ∈ pendSlots σ.fl) :
    flxOK (σ.publish C' bs) := by
  obtain ⟨-, hf2⟩ := hfx
  have h5 := h.2.2.2.2.1 w hw
  simp only [hpub, Bool.false_eq_true, ↓reduceIte] at h5
  refine ⟨fun f hf => (by simp only [StoreSt.publish, hC'] at hf; cases hf), fun k r hr => ?_⟩
  simp only [StoreSt.publish] at hr
  intro f bs' hfb
  obtain ⟨r1, r2, r3, r4⟩ := hf2 k r hr f bs' hfb
  rcases r4 with ⟨hf, hnp⟩ | r4
  · exact absurd (hfreed f hf) hnp
  have hb : ∀ s ∈ flExt σ.bytes f, (σ.publish C' bs).bytes s = σ.bytes s := by
    intro s hs
    simp only [StoreSt.publish]
    rw [if_pos (Or.inr (r4 s hs).1)]
  have hext := flExt_congr σ.bytes (σ.publish C' bs).bytes f hb
  have hfl : (σ.publish C' bs).fl = σ.fl := rfl
  have hCe : (σ.publish C' bs).C = C' := rfl
  rw [hext.1, hext.2, hfl, hCe]
  refine ⟨r1, fun s hs => by rw [hb s hs]; exact r2 s hs, r3, Or.inr fun s hs => ?_⟩
  obtain ⟨a, b, c⟩ := r4 s hs
  refine ⟨a, b, fun t pd i hp hi => ?_⟩
  obtain ⟨c1, c2, -⟩ := c t pd i hp hi
  refine ⟨c1, c2, Or.inl ?_⟩
  rcases h.2.2.1.2.2.1 t pd hp with h' | ⟨h', -⟩
  · omega
  · rw [hw] at h'; cases h'; omega

theorem flxOK_rollback (σ : StoreSt) (w : Nat) (h : storeOK σ) (hfx : flxOK σ)
    (hw : σ.wtx = some w) (hpub : σ.pub = false) : flxOK (σ.rollback (W64 (w : Int))) := by
  by_cases hn : σ.fl.pending !! W64 (w : Int) = none
  · have e : σ.rollback (W64 (w : Int)) = σ := by
      unfold StoreSt.rollback FLPg.rollback; rw [if_pos hn]
    rw [e]; exact hfx
  obtain ⟨hf1, hf2⟩ := hfx
  have h5 := h.2.2.2.2.1 w hw
  simp only [hpub, Bool.false_eq_true, ↓reduceIte] at h5
  have hsm : σ.C.txid + 1 < 2 ^ 64 := h.2.2.1.2.2.2.1
  have hT : (W64 (w : Int)).toNat = w := W64_toNat_lt w (by omega)
  have hfl : (σ.rollback (W64 (w : Int))).fl = σ.fl.rollbackEntry (W64 (w : Int)) := by
    simp only [StoreSt.rollback, FLPg.rollback, if_neg hn]
  have hC : (σ.rollback (W64 (w : Int))).C = σ.C := rfl
  have hbt : (σ.rollback (W64 (w : Int))).bytes = σ.bytes := rfl
  have hR : (σ.rollback (W64 (w : Int))).R = σ.R := rfl
  have hfree : (σ.fl.rollbackEntry (W64 (w : Int))).free = σ.fl.free := rfl
  have hpsub : ∀ s, s ∈ pendSlots (σ.fl.rollbackEntry (W64 (w : Int))) → s ∈ pendSlots σ.fl := by
    intro s hs
    obtain ⟨t, pd, x, hp, hx, rfl⟩ := (mem_pendSlots_iff _ _).1 hs
    exact (mem_pendSlots_iff _ _).2 ⟨t, pd, x, (rollbackEntry_pending _ _ t pd hp).2, hx, rfl⟩
  have honly : ∀ s, pendingOnlyFromWriter σ.fl σ.wtx s →
      s ∉ pendSlots (σ.fl.rollbackEntry (W64 (w : Int))) := by
    intro s ho hs
    obtain ⟨t, pd, x, hp, hx, hxs⟩ := (mem_pendSlots_iff _ _).1 hs
    obtain ⟨hne, hp0⟩ := rollbackEntry_pending _ _ t pd hp
    have := ho t pd hp0 (by rw [← hxs, W64_toNat_self]; exact hx)
    rw [hw] at this
    simp only [Option.some.injEq] at this
    exact hne (by rw [this, W64_toNat_self])
  have hcurnp : ∀ f, σ.C.flpg = some f → ∀ s ∈ flExt σ.bytes f,
      s ∉ pendSlots (σ.fl.rollbackEntry (W64 (w : Int))) := by
    intro f hf s hs hs'
    obtain ⟨-, hsl, -⟩ := hf1 f hf
    obtain ⟨-, -, hiff, hpo, -⟩ := hsl s hs
    have hsp := hpsub s hs'
    exact honly s (hpo (hiff.1 hsp)).2 hs'
  unfold flxOK rdFlOK
  rw [hfl, hC, hbt, hR]
  refine ⟨fun f hf => ?_, fun k r hr => ?_⟩
  · obtain ⟨hpgok, hsl, hall⟩ := hf1 f hf
    have hlt : ∀ s ∈ flExt σ.bytes f, s < 2 ^ 64 := fun s hs => by
      have := flExt_lt_hwm σ.C σ.bytes f hpgok (hsl f (f_mem_flExt _ _)).1 s hs
      have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
    refine ⟨hpgok, fun s hs => ?_, fun a ha => ?_⟩
    · obtain ⟨hl, hnf, -, -, -⟩ := hsl s hs
      have h1 := hcurnp f hf s hs
      have h2 := hcurnp f hf f (f_mem_flExt _ _)
      refine ⟨hl, by rw [hfree]; exact hnf, ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩,
        fun h' => absurd h' h2, fun t pd i hp hi => absurd ?_ h1⟩
      exact pend_of_entry _ t pd i s (hlt s hs) hp hi
    · obtain ⟨-, hal⟩ := rollbackEntry_allocs _ _ _ a ha
      rcases hal with hal | ⟨pd, i, hp, hi1, hi2⟩
      · exact hall a hal
      · have := (hsl f (f_mem_flExt _ _)).2.2.2.2 _ pd i hp hi1
        rwa [List.getD_eq_getElem?_getD, hi2] at this
  · intro f bs hfb
    obtain ⟨r1, r2, r3, r4⟩ := hf2 k r hr f bs hfb
    refine ⟨r1, r2, fun a ha => ?_, ?_⟩
    · obtain ⟨-, hal⟩ := rollbackEntry_allocs _ _ _ a ha
      rcases hal with hal | ⟨pd, i, hp, hi1, hi2⟩
      · exact r3 a hal
      · rcases r4 with ⟨hf, hnp⟩ | r4
        · exfalso
          obtain ⟨hpgok, hsl, -⟩ := hf1 f hf
          have hf64 : f < 2 ^ 64 := by
            have := flExt_lt_hwm σ.C σ.bytes f hpgok (hsl f (f_mem_flExt _ _)).1 f
              (f_mem_flExt _ _)
            have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
          exact hnp (pend_of_entry _ _ pd i f hf64 hp hi1)
        · have := ((r4 f (f_mem_flExt _ _)).2.2 _ pd i hp hi1).1
          rwa [List.getD_eq_getElem?_getD, hi2] at this
    · rcases r4 with ⟨hf, hnp⟩ | r4
      · exact Or.inl ⟨hf, fun h' => hnp (hpsub f h')⟩
      · by_cases hcur : σ.C.flpg = some f
        · exact Or.inl ⟨hcur, hcurnp f hcur f (f_mem_flExt _ _)⟩
        · right
          intro s hs
          obtain ⟨a, b, c⟩ := r4 s hs
          obtain ⟨t, pd, x, hp, hx, hxs⟩ := (mem_pendSlots_iff _ _).1 a
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
          have hi' : pd.ids[i]? = some (W64 (s : Int)) := by rw [← hxs, W64_toNat_self]; exact hi
          obtain ⟨-, -, ht⟩ := c t pd i hp hi'
          have htle : t.toNat ≤ σ.C.txid := ht.resolve_right hcur
          have htne : t ≠ W64 (w : Int) := fun e => by rw [e, hT] at htle; omega
          refine ⟨(mem_pendSlots_iff _ _).2 ⟨t, pd, x, ?_, hx, hxs⟩, by rw [hfree]; exact b,
            fun t' pd' i' hp' hi'' => c t' pd' i' (rollbackEntry_pending _ _ t' pd' hp').2 hi''⟩
          simp only [FLPg.rollbackEntry]
          rw [GMap.lookup_delete_ne _ (Ne.symm htne)]; exact hp

theorem flxOK_release (σ : StoreSt) (ro : List w64) (h : storeOK σ) (hfx : flxOK σ)
    (hw : σ.wtx = none) (hro : ∀ k r, σ.R !! k = some r → W64 (r.v.txid : Int) ∈ ro)
    (hro' : ∀ t ∈ ro, t.toNat ≤ σ.C.txid) (hro1 : ∀ t ∈ ro, 1 ≤ t.toNat) :
    flxOK (σ.release ro) := by
  have hfx0 := hfx
  obtain ⟨hf1, hf2⟩ := hfx
  have hsm : σ.C.txid + 1 < 2 ^ 64 := h.2.2.1.2.2.2.1
  obtain ⟨q1, q2, q3, q4⟩ := releasePending_facts σ.fl ro
    (fun t ht => ⟨hro1 t ht, by have := hro' t ht; omega⟩) h.2.2.2.1.2.2.2.2
  have hfl : (σ.release ro).fl = σ.fl.releasePending ro := rfl
  have hC : (σ.release ro).C = σ.C := rfl
  have hbt : (σ.release ro).bytes = σ.bytes := rfl
  have hR : (σ.release ro).R = σ.R := rfl
  have hpsub : ∀ s, s ∈ pendSlots (σ.fl.releasePending ro) → s ∈ pendSlots σ.fl := by
    intro s hs
    obtain ⟨t, pd', x, hp, hx, rfl⟩ := (mem_pendSlots_iff _ _).1 hs
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
    obtain ⟨pd, j, hp0, hj, -⟩ := q3 t pd' i x hp hi
    exact (mem_pendSlots_iff _ _).2 ⟨t, pd, x, hp0, List.mem_of_getElem? hj, rfl⟩
  unfold flxOK rdFlOK
  rw [hfl, hC, hbt, hR]
  refine ⟨fun f hf => ?_, fun k r hr => ?_⟩
  · obtain ⟨hpgok, hsl, hall⟩ := hf1 f hf
    have hfnp := flx_not_pend_none σ h hfx0 hw f hf
    refine ⟨hpgok, fun s hs => ?_, fun a ha => hall a (q1 ▸ ha)⟩
    obtain ⟨hl, hnf, hiff, -, -⟩ := hsl s hs
    have hsnp : s ∉ pendSlots σ.fl := fun h' => hfnp (hiff.1 h')
    have hs64 : s < 2 ^ 64 := by
      have := flExt_lt_hwm σ.C σ.bytes f hpgok (hsl f (f_mem_flExt _ _)).1 s hs
      have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
    refine ⟨hl, fun hx => ?_, ⟨fun h' => absurd (hpsub s h') hsnp,
      fun h' => absurd (hpsub f h') hfnp⟩, fun h' => absurd (hpsub f h') hfnp,
      fun t pd i hp hi => absurd (hpsub s (pend_of_entry _ t pd i s hs64 hp hi)) hsnp⟩
    rcases q2 _ hx with hx | ⟨t, pd, i, hp, hi, -⟩
    · exact hnf hx
    · exact hsnp (pend_of_entry _ t pd i s hs64 hp hi)
  · intro f bs hfb
    obtain ⟨r1, r2, r3, r4⟩ := hf2 k r hr f bs hfb
    have hrtx : r.v.txid ≤ σ.C.txid := (h.2.2.2.2.2.2.1 k r hr).1
    have hT := hro k r hr
    refine ⟨r1, r2, fun a ha => r3 a (q1 ▸ ha), ?_⟩
    rcases r4 with ⟨hf, hnp⟩ | r4
    · exact Or.inl ⟨hf, fun h' => hnp (hpsub f h')⟩
    · right
      intro s hs
      obtain ⟨a, b, c⟩ := r4 s hs
      have hs64 := (mem_allIds_of_pend _ _ a).2
      have hnf : W64 (s : Int) ∉ (σ.fl.releasePending ro).free := by
        intro hx
        rcases q2 _ hx with hx | ⟨t, pd, i, hp, hi, hq⟩
        · exact b hx
        · obtain ⟨c1, c2, -⟩ := c t pd i hp hi
          apply hq _ hT
          rw [W64_toNat_lt _ (by omega)]
          exact ⟨c1, c2⟩
      refine ⟨?_, hnf, fun t pd' i hp hi => ?_⟩
      · have hin : W64 (s : Int) ∈ (σ.fl.releasePending ro).allIds :=
          q4.symm.subset (mem_allIds_of_pend _ _ a).1
        simp only [FLPg.allIds, List.mem_append] at hin
        rcases hin with hin | hin
        · exact absurd hin hnf
        · simp only [FLPg.pendingIds, List.mem_flatMap] at hin
          obtain ⟨⟨t, pd⟩, hkv, hx⟩ := hin
          exact (mem_pendSlots_iff _ _).2 ⟨t, pd, _, (GMap.mem_toList _ _ _).1 hkv, hx,
            W64_toNat_lt s hs64⟩
      · obtain ⟨pd, j, hp0, hj, he⟩ := q3 t pd' i _ hp hi
        rw [← he]; exact c t pd j hp0 hj

theorem pendSlots_releasePending_sub (fl : FLPg) (ro : List w64)
    (hro : ∀ t ∈ ro, 1 ≤ t.toNat ∧ t.toNat + 1 < 2 ^ 64)
    (hwf : ∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length) (s : Nat)
    (hs : s ∈ pendSlots (fl.releasePending ro)) : s ∈ pendSlots fl := by
  obtain ⟨-, -, q3, -⟩ := releasePending_facts fl ro hro hwf
  obtain ⟨t, pd', x, hp, hx, rfl⟩ := (mem_pendSlots_iff _ _).1 hs
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  obtain ⟨pd, j, hp0, hj, -⟩ := q3 t pd' i x hp hi
  exact (mem_pendSlots_iff _ _).2 ⟨t, pd, x, hp0, List.mem_of_getElem? hj, rfl⟩

theorem storeSlots_rollback_sub_pend (fl : FLPg) (T : w64) (s : Nat)
    (h : s ∈ pendSlots (fl.rollback T)) : s ∈ pendSlots fl := by
  unfold FLPg.rollback at h
  split at h
  · exact h
  · obtain ⟨t, pd, x, hp, hx, rfl⟩ := (mem_pendSlots_iff _ _).1 h
    exact (mem_pendSlots_iff _ _).2 ⟨t, pd, x, (rollbackEntry_pending _ _ t pd hp).2, hx, rfl⟩

end storeflok

end bbolt
end EtcdGrove
end Perennial
