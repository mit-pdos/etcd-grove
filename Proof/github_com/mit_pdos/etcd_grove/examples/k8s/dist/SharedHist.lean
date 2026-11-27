/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: the history relation between the search and the cluster

`notes/k8s-dist-k4.md`, "Handoff K4-3", step 2. The search's configuration `s` and the cluster's `c`
(the semantic model's) are related by a renaming `ρ` of the search's **write revisions** `W` (those
after the seeds, `n0`, in order) to the cluster's (`HRel`): `ρ` is the identity up to `n0`, strictly
increasing, no earlier, cuts every write revision like the identity (`CutW`); every store's items carry
a seed's revision or one of `W`; and a search store at `x` and a cluster store at `y` are the same up
to the renaming whenever the same writes are at or before them (`PairW`). Preserved by a foreign
revision of the cluster (`HRel.foreign_c`), one of the search below the cluster's (`HRel.foreign_s`,
`HRel.skipTo`), a step that changes neither store (`HRel.same`), and a write landing on both, at `a + 1`
on the search and `b + 1` on the cluster, cut alike (`HRel.write`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedAnswer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

section go
variable [GooseExts]

/-! ## `histN` -/

theorem histN_snoc_le (l : List GSt) (g : GSt) (r : Nat) (h : r ≤ l.length) :
    histN (l ++ [g]) r = histN l r := by
  unfold histN; rw [List.take_append_of_le_length h]

theorem histN_snoc_top (l : List GSt) (g : GSt) : histN (l ++ [g]) (l.length + 1) = g := by
  unfold histN; rw [List.take_of_length_le (by simp)]; simp

theorem histN_mem (hs : List GSt) (r : Nat) : histN hs r = zSt ∨ histN hs r ∈ hs := by
  unfold histN
  cases h : (hs.take r).getLast? with
  | none => left; rfl
  | some g => right; exact List.mem_of_mem_take (List.mem_of_getLast? h)

/-! ## A step's store -/

theorem setItem_foldl_mem (it : item) (S : List item) :
    ∀ (l : List item) (st : List item × Bool), (∀ e ∈ st.1, e = it ∨ e ∈ S) → (∀ e ∈ l, e ∈ S) →
      ∀ e ∈ (l.foldl (setStepI it) st).1, e = it ∨ e ∈ S
  | [], _, h, _ => h
  | d :: l, st, h, hl => by
    rw [List.foldl_cons]
    refine setItem_foldl_mem it S l _ ?_ (fun e he => hl e (List.mem_cons_of_mem _ he))
    have h1 : ∀ e ∈ (if st.2 = false ∧ go.GoStringLt it.key' d.key' then (st.1 ++ [it], true)
        else st).1, e = it ∨ e ∈ S := by
      split
      · intro e he; rcases List.mem_append.mp he with he | he
        · exact h e he
        · left; simpa using he
      · exact h
    unfold setStepI
    generalize (if st.2 = false ∧ go.GoStringLt it.key' d.key' then (st.1 ++ [it], true) else st) = t at h1 ⊢
    intro e he
    dsimp only at he
    split at he
    · split at he
      · rcases List.mem_append.mp he with he | he
        · exact h1 e he
        · left; simpa using he
      · exact h1 e he
    · rcases List.mem_append.mp he with he | he
      · exact h1 e he
      · right; exact hl e (by simp at he; rw [he]; exact List.mem_cons_self)

/-- `setItemL`'s items: the new one and old ones. -/
theorem setItemL_mem (its : List item) (it e : item) (he : e ∈ setItemL its it) : e = it ∨ e ∈ its := by
  unfold setItemL at he
  have := setItem_foldl_mem it its its ([], false) (by simp) (fun e he => he)
  dsimp only at he
  split at he
  · exact this e he
  · rcases List.mem_append.mp he with he | he
    · exact this e he
    · left; simpa using he

/-- **The shape of a step**: the store unchanged, or a success at the next revision whose items are
old ones or at that revision. -/
def StepShape (st : GSt) (p : GSt × Output) : Prop :=
  p.1 = st ∨ (p.1.rv = st.rv + W64 1 ∧ p.2.Err' = W64 0 ∧ p.2.RV' = st.rv + W64 1 ∧
    ∀ e ∈ p.1.items, e ∈ st.items ∨ e.obj'.ResourceVersion' = st.rv + W64 1)

theorem mstepL_shape (x : Input) (st : GSt) : StepShape st (mstepL x st) := by
  unfold mstepL
  split
  · unfold mcreateL; dsimp only
    split
    · left; rfl
    · right; refine ⟨rfl, rfl, rfl, fun e he => ?_⟩
      rcases setItemL_mem _ _ _ he with rfl | he
      · right; rfl
      · left; exact he
  split
  · unfold mdeleteL; dsimp only
    split
    · left; rfl
    split
    · left; rfl
    split
    · left; rfl
    · right; exact ⟨rfl, rfl, rfl, fun e he => Or.inl (List.mem_filter.mp he).1⟩
  split
  · unfold mupdateL; dsimp only
    repeat' (first | (left; rfl) | split)
    all_goals
      right; refine ⟨rfl, rfl, rfl, fun e he => ?_⟩
      rcases setItemL_mem _ _ _ he with rfl | he
      · right; rfl
      · left; exact he
  · left; rfl

theorem rv_succ_ne (r : w64) : r + W64 1 ≠ r := by
  intro e; have := congrArg (uint.nat ·) e; simp at this; word

/-- **A step's items**: old ones, or one at the next revision. -/
theorem mstepL_mem (x : Input) (st : GSt) (e : item) (he : e ∈ (mstepL x st).1.items) :
    e ∈ st.items ∨ e.obj'.ResourceVersion' = st.rv + W64 1 := by
  rcases mstepL_shape x st with h | h
  · rw [h] at he; exact Or.inl he
  · exact h.2.2.2 e he

/-- **A step that keeps the revision keeps the store.** -/
theorem mstepL_same (x : Input) (st : GSt) (h : (mstepL x st).1.rv = st.rv) : (mstepL x st).1 = st := by
  rcases mstepL_shape x st with h' | h'
  · exact h'
  · exact absurd (h'.1.symm.trans h) (rv_succ_ne _)

/-- **A step that changes the revision answers a success at the new one.** -/
theorem mstepL_changed (x : Input) (st : GSt) (h : (mstepL x st).1.rv ≠ st.rv) :
    (mstepL x st).1.rv = st.rv + W64 1 ∧ (mstepL x st).2.Err' = W64 0 ∧
      (mstepL x st).2.RV' = st.rv + W64 1 := by
  rcases mstepL_shape x st with h' | h'
  · exact absurd (by rw [h']) h
  · exact ⟨h'.1, h'.2.1, h'.2.2.1⟩

/-- A step that is no write keeps the configuration's store and history. -/
theorem kstepL_nonwrite (x : Input) (h : HSt) (hw : isWriteL x = false) : (kstepL x h).1 = h := by
  unfold kstepL
  split
  · rfl
  · have h0 : x.Kind' ≠ W64 0 := by intro e; simp [isWriteL, e] at hw
    have h1 : x.Kind' ≠ W64 1 := by intro e; simp [isWriteL, e] at hw
    have h2 : x.Kind' ≠ W64 2 := by intro e; simp [isWriteL, e] at hw
    simp only [mstepL, h0, h1, h2, if_false, advanceL, ne_eq, not_true_eq_false]

/-! ## The relation -/

/-- **The same writes are at or before the search's `x` and the cluster's `y`** (and below the seeds'
revision, `x = y`). -/
def PairW (n0 : Nat) (ρ : Nat → Nat) (W : List Nat) (x y : Nat) : Prop :=
  (x < n0 ∨ y < n0 → x = y) ∧ ∀ w ∈ W, (w ≤ x ↔ ρ w ≤ y)

/-- A stored revision: a seed's, or a search write's. -/
def StoredRv (n0 : Nat) (W : List Nat) (r : Nat) : Prop := r ≤ n0 ∨ r ∈ W

/-- **The history relation** (`notes/k8s-dist-k4.md`, "Handoff K4-3", step 2) between the search's
store and history `s` and the cluster's `c`, from seeds at `n0`, the search's write revisions `W`
renamed by `ρ`. -/
structure HRel (A : List Nat) (n0 : Nat) (ρ : Nat → Nat) (W : List Nat) (s c : HSt) : Prop where
  n0_le : n0 ≤ uint.nat s.st.rv
  le : uint.nat s.st.rv ≤ uint.nat c.st.rv
  slen : s.hist.length = uint.nat s.st.rv
  clen : c.hist.length = uint.nat c.st.rv
  slast : histN s.hist (uint.nat s.st.rv) = s.st
  clast : histN c.hist (uint.nat c.st.rv) = c.st
  shrv : ∀ x, n0 < x → x ≤ uint.nat s.st.rv → (histN s.hist x).rv = W64 (x : Int)
  chrv : ∀ y, n0 < y → y ≤ uint.nat c.st.rv → (histN c.hist y).rv = W64 (y : Int)
  W_in : ∀ w ∈ W, n0 < w ∧ w ≤ uint.nat s.st.rv
  ρ_id : ∀ r ≤ n0, ρ r = r
  ρ_W : ∀ w ∈ W, w ≤ ρ w ∧ ρ w ≤ uint.nat c.st.rv
  ρ_mono : ∀ w ∈ W, ∀ w' ∈ W, w < w' → ρ w < ρ w'
  cut : ∀ w ∈ W, CutW A ρ w
  stored : ∀ x ≤ uint.nat s.st.rv, ∀ it ∈ (histN s.hist x).items,
    StoredRv n0 W (uint.nat it.obj'.ResourceVersion')
  hist : ∀ x ≤ uint.nat s.st.rv, ∀ y ≤ uint.nat c.st.rv, PairW n0 ρ W x y →
    (histN c.hist y).items = (histN s.hist x).items.map (renItem ρ)
  seed : ∀ x ≤ n0, histN s.hist x = histN c.hist x

section rel
variable {A : List Nat} {n0 : Nat} {ρ : Nat → Nat} {W : List Nat} {s c : HSt}

/-- The current stores are a pair. -/
theorem HRel.pair_top (h : HRel A n0 ρ W s c) : PairW n0 ρ W (uint.nat s.st.rv) (uint.nat c.st.rv) := by
  have := h.n0_le; have := h.le
  refine ⟨fun h' => by omega, fun w hw => ?_⟩
  have := h.W_in w hw; have := h.ρ_W w hw
  constructor <;> intro <;> omega

/-- **The current stores are the same up to the renaming.** -/
theorem HRel.cur (h : HRel A n0 ρ W s c) : c.st.items = s.st.items.map (renItem ρ) := by
  have := h.hist _ (Nat.le_refl _) _ (Nat.le_refl _) h.pair_top
  rwa [h.slast, h.clast] at this

/-- The current store's items carry stored revisions. -/
theorem HRel.stored_cur (h : HRel A n0 ρ W s c) (it : item) (hi : it ∈ s.st.items) :
    StoredRv n0 W (uint.nat it.obj'.ResourceVersion') :=
  h.stored _ (Nat.le_refl _) it (by rw [h.slast]; exact hi)

/-- A stored revision is cut like the identity, and renamed to one at most the cluster's. -/
theorem HRel.stored_cut (h : HRel A n0 ρ W s c) (r : Nat) (hr : StoredRv n0 W r) :
    CutW A ρ r ∧ ρ r ≤ max r (uint.nat c.st.rv) := by
  rcases hr with hr | hr
  · have e := h.ρ_id r hr
    exact ⟨fun v _ => by rw [e]; exact ⟨Iff.rfl, Iff.rfl⟩, by rw [e]; exact Nat.le_max_left _ _⟩
  · exact ⟨h.cut r hr, Nat.le_trans (h.ρ_W r hr).2 (Nat.le_max_right _ _)⟩

/-- The renaming is injective on stored revisions. -/
theorem HRel.inj (h : HRel A n0 ρ W s c) (r r' : Nat) (hr : StoredRv n0 W r) (hr' : StoredRv n0 W r')
    (he : ρ r = ρ r') : r = r' := by
  rcases hr with hr | hr <;> rcases hr' with hr' | hr'
  · rwa [h.ρ_id r hr, h.ρ_id r' hr'] at he
  · have := (h.ρ_W r' hr').1; have := (h.W_in r' hr').1; rw [h.ρ_id r hr] at he; omega
  · have := (h.ρ_W r hr).1; have := (h.W_in r hr).1; rw [h.ρ_id r' hr'] at he; omega
  · rcases Nat.lt_trichotomy r r' with hl | hl | hl
    · have := h.ρ_mono r hr r' hr' hl; omega
    · exact hl
    · have := h.ρ_mono r' hr' r hr hl; omega

/-- **The start**: the seeded store on both sides, no write, the identity. -/
theorem HRel.init (h0 : HSt) (hlen : h0.hist.length = uint.nat h0.st.rv)
    (hlast : h0.hist.getLast? = some h0.st)
    (hseed : ∀ g ∈ h0.hist, ∀ it ∈ g.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat h0.st.rv) :
    HRel A (uint.nat h0.st.rv) id [] h0 h0 := by
  have hl : histN h0.hist (uint.nat h0.st.rv) = h0.st := by
    unfold histN; rw [List.take_of_length_le (by omega), hlast]; rfl
  have hid : ∀ l : List item, l.map (renItem id) = l := fun l => by
    have : renItem id = id := by
      funext it; simp only [renItem, renObj, id]
      rw [show (W64 (uint.nat it.obj'.ResourceVersion' : Int)) = it.obj'.ResourceVersion' by word]
    rw [this, List.map_id]
  refine ⟨Nat.le_refl _, Nat.le_refl _, hlen, hlen, hl, hl, fun x h1 h2 => by omega,
    fun x h1 h2 => by omega, by simp, fun _ _ => rfl, by simp, by simp, by simp, ?_, ?_, ?_⟩
  · intro x _ it hi
    left
    rcases histN_mem h0.hist x with he | he
    · rw [he] at hi; simp [zSt] at hi
    · exact hseed _ he it hi
  · intro x hx y hy hp
    have : x = y := by
      by_cases e : x < uint.nat h0.st.rv ∨ y < uint.nat h0.st.rv
      · exact hp.1 e
      · omega
    subst this; rw [hid]
  · intro _ _; rfl

/-- **A foreign revision of the cluster.** -/
theorem HRel.foreign_c (h : HRel A n0 ρ W s c) (hw : uint.nat c.st.rv + 1 < 2 ^ 64) :
    HRel A n0 ρ W s (foreignL c) := by
  have hrv : uint.nat (foreignL c).st.rv = uint.nat c.st.rv + 1 := foreignL_rv c hw
  have hh : (foreignL c).hist = c.hist ++ [⟨c.st.items, c.st.rv + W64 1⟩] := rfl
  have hlen := h.clen
  have htop : histN (foreignL c).hist (uint.nat (foreignL c).st.rv) = (foreignL c).st := by
    rw [hh, hrv, ← hlen, histN_snoc_top]; rfl
  have hlow : ∀ y ≤ uint.nat c.st.rv, histN (foreignL c).hist y = histN c.hist y := fun y hy => by
    rw [hh, histN_snoc_le _ _ _ (by omega)]
  refine ⟨h.n0_le, by rw [hrv]; exact Nat.le_succ_of_le h.le, h.slen, by rw [hh, hrv]; simp [hlen],
    h.slast, htop, h.shrv, fun y h1 h2 => ?_, h.W_in, h.ρ_id,
    fun w hw' => by rw [hrv]; exact ⟨(h.ρ_W w hw').1, Nat.le_succ_of_le (h.ρ_W w hw').2⟩,
    h.ρ_mono, h.cut, h.stored, fun x hx y hy hp => ?_,
    fun x hx => by have := h.n0_le; have := h.le; rw [hlow x (by omega)]; exact h.seed x hx⟩
  · rw [hrv] at h2
    rcases Nat.lt_or_eq_of_le h2 with h2 | h2
    · rw [hlow y (by omega)]; exact h.chrv y h1 (by omega)
    · rw [← hrv] at h2; subst h2; rw [htop]; simp only [foreignL]; word
  · rw [hrv] at hy
    rcases Nat.lt_or_eq_of_le hy with hy | hy
    · rw [hlow y (by omega)]; exact h.hist x hx y (by omega) hp
    · subst hy
      rw [← hrv, htop]
      have hp' : PairW n0 ρ W x (uint.nat c.st.rv) := by
        have := h.n0_le; have := h.le
        refine ⟨fun e => ?_, fun w hw' => ?_⟩
        · have := hp.1 (by omega); omega
        · have := hp.2 w hw'; have := (h.ρ_W w hw').2; constructor <;> intro <;> omega
      have := h.hist x hx _ (Nat.le_refl _) hp'
      rw [h.clast] at this
      exact this

/-- **A foreign revision of the search**, below the cluster's revision. -/
theorem HRel.foreign_s (h : HRel A n0 ρ W s c) (hlt : uint.nat s.st.rv < uint.nat c.st.rv)
    (hw : uint.nat s.st.rv + 1 < 2 ^ 64) : HRel A n0 ρ W (foreignL s) c := by
  have hrv : uint.nat (foreignL s).st.rv = uint.nat s.st.rv + 1 := foreignL_rv s hw
  have hh : (foreignL s).hist = s.hist ++ [⟨s.st.items, s.st.rv + W64 1⟩] := rfl
  have hlen := h.slen
  have htop : histN (foreignL s).hist (uint.nat (foreignL s).st.rv) = (foreignL s).st := by
    rw [hh, hrv, ← hlen, histN_snoc_top]; rfl
  have hlow : ∀ x ≤ uint.nat s.st.rv, histN (foreignL s).hist x = histN s.hist x := fun x hx => by
    rw [hh, histN_snoc_le _ _ _ (by omega)]
  have hn0 := h.n0_le
  -- the new top pairs like the old one
  have hpair : ∀ y, PairW n0 ρ W (uint.nat s.st.rv + 1) y → PairW n0 ρ W (uint.nat s.st.rv) y :=
    fun y hp => by
      refine ⟨fun e => ?_, fun w hw' => ?_⟩
      · have := hp.1 (by omega); omega
      · have := hp.2 w hw'; have := (h.W_in w hw').2; constructor <;> intro <;> omega
  refine ⟨by rw [hrv]; omega, by rw [hrv]; omega, by rw [hh, hrv]; simp [hlen], h.clen, htop, h.clast,
    fun x h1 h2 => ?_, h.chrv, fun w hw' => by rw [hrv]; exact ⟨(h.W_in w hw').1,
      Nat.le_succ_of_le (h.W_in w hw').2⟩, h.ρ_id, h.ρ_W, h.ρ_mono, h.cut, fun x hx it hi => ?_,
    fun x hx y hy hp => ?_, fun x hx => by rw [hlow x (by omega)]; exact h.seed x hx⟩
  · rw [hrv] at h2
    rcases Nat.lt_or_eq_of_le h2 with h2 | h2
    · rw [hlow x (by omega)]; exact h.shrv x h1 (by omega)
    · rw [← hrv] at h2; subst h2; rw [htop]; simp only [foreignL]; word
  · rw [hrv] at hx
    rcases Nat.lt_or_eq_of_le hx with hx | hx
    · rw [hlow x (by omega)] at hi; exact h.stored x (by omega) it hi
    · subst hx; rw [← hrv, htop] at hi; exact h.stored_cur it hi
  · rw [hrv] at hx
    rcases Nat.lt_or_eq_of_le hx with hx | hx
    · rw [hlow x (by omega)]; exact h.hist x (by omega) y hy hp
    · subst hx
      rw [← hrv, htop]
      have := h.hist _ (Nat.le_refl _) y hy (hpair y hp)
      rw [h.slast] at this
      exact this

theorem HRel.repeat_foreign (h : HRel A n0 ρ W s c) :
    ∀ n, uint.nat s.st.rv + n ≤ uint.nat c.st.rv → HRel A n0 ρ W (Nat.repeat foreignL n s) c
  | 0, _ => h
  | n + 1, hn => by
    simp only [Nat.repeat]
    have hc : uint.nat c.st.rv < 2 ^ 64 := by word
    have hr := repeat_foreignL_rv n s (by omega)
    exact (h.repeat_foreign n (by omega)).foreign_s (by rw [hr]; omega) (by rw [hr]; omega)

/-- **`skipToL` on the search**, to at most the cluster's revision. -/
theorem HRel.skipTo (h : HRel A n0 ρ W s c) (t : Nat) (ht : t ≤ uint.nat c.st.rv) :
    HRel A n0 ρ W (skipToL s t) c :=
  h.repeat_foreign _ (by have := h.le; omega)

/-! ## A write on both sides -/

/-- The renaming with the search's new write revision `a + 1` taken to the cluster's `b + 1`. -/
def extR (ρ : Nat → Nat) (a b : Nat) (r : Nat) : Nat := if r = a + 1 then b + 1 else ρ r

theorem extR_old (ρ : Nat → Nat) (a b r : Nat) (h : r ≤ a) : extR ρ a b r = ρ r := by
  unfold extR; rw [if_neg (by omega)]

theorem extR_new (ρ : Nat → Nat) (a b : Nat) : extR ρ a b (a + 1) = b + 1 := by simp [extR]

/-- A stored revision is at most the search's. -/
theorem HRel.stored_le (h : HRel A n0 ρ W s c) (r : Nat) (hr : StoredRv n0 W r) :
    r ≤ uint.nat s.st.rv := by
  rcases hr with hr | hr
  · exact Nat.le_trans hr h.n0_le
  · exact (h.W_in r hr).2

/-- Renaming a store at or below the search's with the extended renaming is renaming it with `ρ`. -/
theorem HRel.map_ext (h : HRel A n0 ρ W s c) (b x : Nat) (hx : x ≤ uint.nat s.st.rv) :
    (histN s.hist x).items.map (renItem (extR ρ (uint.nat s.st.rv) b)) =
      (histN s.hist x).items.map (renItem ρ) := by
  refine List.map_congr_left fun it hi => ?_
  simp only [renItem, renObj, extR_old ρ _ b _ (h.stored_le _ (h.stored x hx it hi))]

/-- **The write step on both current stores**, under the extended renaming. -/
theorem HRel.writeRen (h : HRel A n0 ρ W s c) (x : Input)
    (hpre : x.HasPreRV' = true → ∀ r, parseRVD x.PreRV' = some r → uint.nat r ∈ A)
    (hb : uint.nat c.st.rv + 1 < 2 ^ 64) :
    WriteRen (extR ρ (uint.nat s.st.rv) (uint.nat c.st.rv)) x s.st.items s.st.rv c.st.rv := by
  have hle := h.le; have hn0 := h.n0_le
  refine ⟨by rw [extR_old _ _ _ _ (Nat.zero_le _)]; exact h.ρ_id 0 (Nat.zero_le _), extR_new _ _ _,
    by omega, hb, fun it hi => ?_, fun hp r hr it hi => ?_⟩
  · have hs := h.stored_cur it hi
    rw [extR_old _ _ _ _ (h.stored_le _ hs)]
    have := (h.stored_cut _ hs).2
    have : uint.nat it.obj'.ResourceVersion' < 2 ^ 64 := by word
    omega
  · have hs := h.stored_cur it hi
    rw [extR_old _ _ _ _ (h.stored_le _ hs)]
    exact (h.stored_cut _ hs).1.eq_iff (hpre hp r hr)

/-- The cluster's current items, renamed with the extended renaming. -/
theorem HRel.cur_ext (h : HRel A n0 ρ W s c) (b : Nat) :
    c.st.items = s.st.items.map (renItem (extR ρ (uint.nat s.st.rv) b)) := by
  have := h.map_ext b _ (Nat.le_refl _)
  rw [h.slast] at this
  rw [this]; exact h.cur

/-- **A write's step on both sides**: the cluster's changes its store iff the search's does, and
the stores stay renamed. -/
theorem HRel.stepRen (h : HRel A n0 ρ W s c) (x : Input)
    (hpre : x.HasPreRV' = true → ∀ r, parseRVD x.PreRV' = some r → uint.nat r ∈ A)
    (hb : uint.nat c.st.rv + 1 < 2 ^ 64) :
    StepRen (extR ρ (uint.nat s.st.rv) (uint.nat c.st.rv)) s.st c.st (mstepL x s.st).1 (mstepL x c.st).1 := by
  have := mstepL_ren _ x s.st.items s.st.rv c.st.rv (h.writeRen x hpre hb)
  rw [← h.cur_ext] at this
  exact this

theorem advanceL_same (h : HSt) (st : GSt) (e : st = h.st) : advanceL h st = h := by
  subst e; unfold advanceL; simp

theorem advanceL_new (h : HSt) (st : GSt) (e : st.rv ≠ h.st.rv) : advanceL h st = ⟨st, h.hist ++ [st]⟩ := by
  unfold advanceL; rw [if_pos e]

/-- **A write landing on both sides**: at `a + 1` on the search's store at `a`, at `b + 1` on the
cluster's at `b`, the two cut alike by every anchor (`canonL_cut`); `a + 1` joins the write
revisions, renamed to `b + 1`. -/
theorem HRel.write (h : HRel A n0 ρ W s c) (x : Input)
    (hpre : x.HasPreRV' = true → ∀ r, parseRVD x.PreRV' = some r → uint.nat r ∈ A)
    (hb : uint.nat c.st.rv + 1 < 2 ^ 64)
    (hch : (mstepL x s.st).1.rv ≠ s.st.rv)
    (hcut : CutW A (fun _ => uint.nat c.st.rv + 1) (uint.nat s.st.rv + 1)) :
    HRel A n0 (extR ρ (uint.nat s.st.rv) (uint.nat c.st.rv)) (W ++ [uint.nat s.st.rv + 1])
      (advanceL s (mstepL x s.st).1) (advanceL c (mstepL x c.st).1) := by
  obtain ⟨hitems, hrv⟩ := h.stepRen x hpre hb
  have hS := (mstepL_changed x s.st hch).1
  have hC : (mstepL x c.st).1.rv = c.st.rv + W64 1 := by
    rcases hrv with ⟨e, _⟩ | ⟨_, e⟩
    · exact absurd e hch
    · exact e
  have hC' : (mstepL x c.st).1.rv ≠ c.st.rv := by rw [hC]; exact rv_succ_ne _
  rw [advanceL_new _ _ hch, advanceL_new _ _ hC']
  generalize hρ' : extR ρ (uint.nat s.st.rv) (uint.nat c.st.rv) = ρ' at hitems
  have hle := h.le; have hn0 := h.n0_le
  have ha : uint.nat (mstepL x s.st).1.rv = uint.nat s.st.rv + 1 := by rw [hS]; word
  have hb' : uint.nat (mstepL x c.st).1.rv = uint.nat c.st.rv + 1 := by rw [hC]; word
  have hsl := h.slen; have hcl := h.clen
  have hstop : histN (s.hist ++ [(mstepL x s.st).1]) (uint.nat s.st.rv + 1) = (mstepL x s.st).1 := by
    rw [← hsl, histN_snoc_top]
  have hctop : histN (c.hist ++ [(mstepL x c.st).1]) (uint.nat c.st.rv + 1) = (mstepL x c.st).1 := by
    rw [← hcl, histN_snoc_top]
  have hρold : ∀ r ≤ uint.nat s.st.rv, ρ' r = ρ r := fun r hr => by rw [← hρ', extR_old _ _ _ _ hr]
  have hρnew : ρ' (uint.nat s.st.rv + 1) = uint.nat c.st.rv + 1 := by rw [← hρ', extR_new]
  have hmap : ∀ x' ≤ uint.nat s.st.rv, (histN s.hist x').items.map (renItem ρ') =
      (histN s.hist x').items.map (renItem ρ) := fun x' hx' => by
    rw [← hρ']; exact h.map_ext _ x' hx'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x' hx' => ?_⟩
  · simp only; omega
  · simp only; omega
  · simp only [List.length_append, List.length_singleton]; omega
  · simp only [List.length_append, List.length_singleton]; omega
  · simp only; rw [ha]; exact hstop
  · simp only; rw [hb']; exact hctop
  · intro x' h1 h2; simp only at h2 ⊢; rw [ha] at h2
    rcases Nat.lt_or_eq_of_le h2 with h2 | h2
    · rw [histN_snoc_le _ _ _ (by omega)]; exact h.shrv x' h1 (by omega)
    · subst h2; rw [hstop, hS]; word
  · intro y h1 h2; simp only at h2 ⊢; rw [hb'] at h2
    rcases Nat.lt_or_eq_of_le h2 with h2 | h2
    · rw [histN_snoc_le _ _ _ (by omega)]; exact h.chrv y h1 (by omega)
    · subst h2; rw [hctop, hC]; word
  · intro w hw; simp only; rw [ha]
    rcases List.mem_append.mp hw with hw | hw
    · have := h.W_in w hw; omega
    · simp at hw; omega
  · intro r hr; rw [hρold r (by omega)]; exact h.ρ_id r hr
  · intro w hw; simp only; rw [hb']
    rcases List.mem_append.mp hw with hw | hw
    · have := h.W_in w hw; have := h.ρ_W w hw; rw [hρold w (by omega)]; omega
    · simp at hw; subst hw; rw [hρnew]; omega
  · intro w hw w' hw' hlt
    rcases List.mem_append.mp hw with hw | hw <;> rcases List.mem_append.mp hw' with hw' | hw'
    · have := h.W_in w hw; have := h.W_in w' hw'
      rw [hρold w (by omega), hρold w' (by omega)]; exact h.ρ_mono w hw w' hw' hlt
    · simp at hw'; subst hw'; have := h.W_in w hw; have := h.ρ_W w hw
      rw [hρold w (by omega), hρnew]; omega
    · simp at hw; subst hw; have := h.W_in w' hw'; omega
    · simp at hw hw'; omega
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · have := h.W_in w hw
      intro v hv; rw [hρold w (by omega)]; exact h.cut w hw v hv
    · simp at hw; subst hw; intro v hv; rw [hρnew]; exact hcut v hv
  · intro x' hx' it hi; simp only at hx' hi; rw [ha] at hx'
    rcases Nat.lt_or_eq_of_le hx' with hx' | hx'
    · rw [histN_snoc_le _ _ _ (by omega)] at hi
      rcases h.stored x' (by omega) it hi with e | e
      · exact Or.inl e
      · exact Or.inr (List.mem_append_left _ e)
    · subst hx'; rw [hstop] at hi
      rcases mstepL_mem x s.st it hi with e | e
      · rcases h.stored_cur it e with e | e
        · exact Or.inl e
        · exact Or.inr (List.mem_append_left _ e)
      · right; apply List.mem_append_right; simp only [List.mem_singleton]; rw [e]; word
  · intro x' hx' y hy hp; simp only at hx' hy ⊢; rw [ha] at hx'; rw [hb'] at hy
    have hlast := hp.2 (uint.nat s.st.rv + 1) (by simp)
    rw [hρnew] at hlast
    rcases Nat.lt_or_eq_of_le hx' with hx' | hx' <;> rcases Nat.lt_or_eq_of_le hy with hy | hy
    · rw [histN_snoc_le _ _ _ (by omega), histN_snoc_le _ _ _ (by omega), hmap x' (by omega)]
      refine h.hist x' (by omega) y (by omega) ⟨hp.1, fun w hw => ?_⟩
      have hq := hp.2 w (List.mem_append_left _ hw); have := h.W_in w hw
      rwa [hρold w (by omega)] at hq
    · omega
    · omega
    · subst hx' hy; rw [hstop, hctop]; exact hitems
  · simp only
    rw [histN_snoc_le _ _ _ (by omega), histN_snoc_le _ _ _ (by omega)]; exact h.seed x' hx'

end rel

end go

end k8s_dist
end EtcdGrove
end Perennial
