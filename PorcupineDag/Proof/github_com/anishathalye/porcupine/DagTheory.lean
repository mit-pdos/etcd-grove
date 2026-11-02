/-
Lean-first (no Rocq counterpart).

# The DAG search, in pure terms (2026-11-02)

Porcupine PR #46's `checkSingle` (`dag.go`) searches for a linearization by depth-first search
over *candidates*: an operation not yet linearized all of whose real-time predecessors are
(`Cand`). The candidates are kept in the *frontier*, sorted by `KeyGt` (later call first, then
larger client id: `addToFrontier`); the search lifts the candidates from the end of the frontier
down (`chains.lift`, from the cursor `liftFrom`), and when none can be lifted it pops the newest
frame and resumes below the position that frame was lifted from (`frontierIdx - 1`).

This file is the search's correctness argument, independent of the heap and of the chains (how
the code finds the candidates: `Chains.lean`): the frontier is a sorted list of the candidates
(`CandList`), hence a function of the set of operations linearized (`candList_unique`), so the
list the search resumes in after a pop is the one the popped frame was lifted from. The
invariant is split as in v1.3.1 (`Theory.lean`, `Soundness.lean`): `Struct` holds in every
branch, a cancelled step included; `Bad` (the candidates already tried lead nowhere, and the
cache is sound) is lost on a cancelled step (`StepContext` may refuse a step the model allows
once its context is done), and is carried as `⌜Bad⌝ ∨ □ Done`.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Theory

@[expose] public section

namespace Perennial
namespace github_com.anishathalye.porcupine
namespace Theory

variable {σ α : Type}

/-- Every operation's call is at most its return (`HistOk`'s second part). -/
def CallLeRet (h : List (Op α)) : Prop := ∀ o ∈ h, o.call ≤ o.ret

/-- An operation's call time (`0` past the end). -/
def callOf (h : List (Op α)) (y : Nat) : Int := ((h[y]?).map Op.call).getD 0

/-- The client whose chain holds `y` (the chains' count past them). -/
def clientOf (cs : List (List Nat)) (y : Nat) : Nat := cs.findIdx (fun c => decide (y ∈ c))

/-- `y` may be linearized after the operations `B`: it is not linearized, and every operation
that precedes it in real time is. -/
def Cand (h : List (Op α)) (B : List Nat) (y : Nat) : Prop :=
  y < h.length ∧ y ∉ B ∧ ∀ z, Prec h z y → z ∈ B

/-- The frontier's order (`addToFrontier`): a later call first, then a larger client. -/
def KeyGt (h : List (Op α)) (cs : List (List Nat)) (y z : Nat) : Prop :=
  callOf h z < callOf h y ∨ (callOf h y = callOf h z ∧ clientOf cs z < clientOf cs y)

theorem keyGt_asymm {h : List (Op α)} {cs : List (List Nat)} {y z : Nat}
    (h1 : KeyGt h cs y z) (h2 : KeyGt h cs z y) : False := by
  unfold KeyGt at h1 h2; omega

/-- `l` is the candidates of `B`, sorted by `KeyGt`. -/
def CandList (h : List (Op α)) (cs : List (List Nat)) (B : List Nat) (l : List Nat) : Prop :=
  l.Pairwise (KeyGt h cs) ∧ ∀ y, y ∈ l ↔ Cand h B y

/-- Two lists sorted by an asymmetric relation with the same members are equal. -/
theorem pairwise_eq_of_mem {R : Nat → Nat → Prop} (hR : ∀ a b, R a b → R b a → False) :
    ∀ {l l' : List Nat}, l.Pairwise R → l'.Pairwise R → (∀ y, y ∈ l ↔ y ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, hm => absurd ((hm b).mpr (List.mem_cons_self ..)) (List.not_mem_nil)
  | a :: _, [], _, _, hm => absurd ((hm a).mp (List.mem_cons_self ..)) (List.not_mem_nil)
  | a :: t, b :: t', hp, hp', hm => by
    have hirr : ∀ x, ¬ R x x := fun x hx => hR x x hx hx
    rw [List.pairwise_cons] at hp hp'
    have hab : a = b := by
      refine Classical.byContradiction fun hne => ?_
      have ha : a ∈ t' := ((List.mem_cons.mp ((hm a).mp (List.mem_cons_self ..))).resolve_left hne)
      have hb : b ∈ t := ((List.mem_cons.mp ((hm b).mpr (List.mem_cons_self ..))).resolve_left
        (Ne.symm hne))
      exact hR a b (hp.1 b hb) (hp'.1 a ha)
    subst hab
    have hna : a ∉ t := fun h => hirr a (hp.1 a h)
    have hna' : a ∉ t' := fun h => hirr a (hp'.1 a h)
    congr 1
    refine pairwise_eq_of_mem hR hp.2 hp'.2 fun y => ?_
    constructor
    · intro hy
      have := (hm y).mp (List.mem_cons_of_mem _ hy)
      rcases List.mem_cons.mp this with rfl | h
      · exact absurd hy hna
      · exact h
    · intro hy
      have := (hm y).mpr (List.mem_cons_of_mem _ hy)
      rcases List.mem_cons.mp this with rfl | h
      · exact absurd hy hna'
      · exact h

/-- The candidate list is a function of the set of operations linearized. -/
theorem candList_unique {h : List (Op α)} {cs : List (List Nat)} {B B' l l' : List Nat}
    (hl : CandList h cs B l) (hl' : CandList h cs B' l') (hB : ∀ y, y ∈ B ↔ y ∈ B') : l = l' := by
  refine pairwise_eq_of_mem (fun a b => keyGt_asymm) hl.1 hl'.1 fun y => ?_
  rw [hl.2 y, hl'.2 y]
  unfold Cand
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun h => h2 ((hB y).mpr h), fun z hz => (hB z).mp (h3 z hz)⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun h => h2 ((hB y).mp h), fun z hz => (hB z).mpr (h3 z hz)⟩

/-- No operation precedes itself (its call is at most its return). -/
theorem prec_irrefl {h : List (Op α)} (hwf : CallLeRet h) (y : Nat) : ¬ Prec h y y := by
  rintro ⟨o, o', ho, ho', hlt⟩
  rw [ho] at ho'; cases ho'
  have := hwf o (List.mem_of_getElem? ho)
  omega

/-- Two candidates are unrelated in real time. -/
theorem cand_not_prec {h : List (Op α)} {B : List Nat} {y z : Nat}
    (hy : Cand h B y) (hz : Cand h B z) : ¬ Prec h y z :=
  fun hp => hy.2.1 (hz.2.2 y hp)

/-! ## The search's invariant -/

/-- Lifting the candidates at positions above `p` (`p = -1`: all) leads only to configurations
without completion. -/
def PrefixBad (M : SeqModel σ α) (h : List (Op α)) (B : List Nat) (t : σ) (fr : List Nat)
    (p : Int) : Prop :=
  ∀ (q : Nat) y, p < q → fr[q]? = some y → SuccBad M h B t y

/-- Each frame lifted the candidate at `pos` of the candidate list below it (kept in every
branch). -/
def FramesStruct (h : List (Op α)) (cs : List (List Nat)) : List (Frame σ) → Prop
  | [] => True
  | f :: fs => FramesStruct h cs fs ∧ CandList h cs (ids fs) f.fr ∧ f.fr[f.pos]? = some f.id

/-- Each frame was lifted after the candidates above its position were tried. -/
def FramesBad (M : SeqModel σ α) (h : List (Op α)) : List (Frame σ) → Prop
  | [] => True
  | f :: fs => FramesBad M h fs ∧ PrefixBad M h (ids fs) f.pre f.fr f.pos

/-- The search's structure: the stack is a chain of model steps to `s`, each frame lifted a
candidate, `fr` is the current candidate list and the cursor `p` is in `[-1, |fr|)`. -/
def Struct (M : SeqModel σ α) (h : List (Op α)) (cs : List (List Nat)) (fs : List (Frame σ))
    (s : σ) (fr : List Nat) (p : Int) : Prop :=
  Chain M h fs s ∧ FramesStruct h cs fs ∧ CandList h cs (ids fs) fr ∧ -1 ≤ p ∧ p < fr.length

/-- The completeness invariant: the candidates tried lead nowhere, at every frame and at the
cursor, and the cache is sound. -/
def Bad (M : SeqModel σ α) (h : List (Op α)) (fs : List (Frame σ)) (s : σ) (fr : List Nat)
    (p : Int) (cache : List ((Nat → Prop) × σ)) : Prop :=
  FramesBad M h fs ∧ PrefixBad M h (ids fs) s fr p ∧ CacheOk M h fs cache

theorem struct_init {M : SeqModel σ α} {h : List (Op α)} {cs : List (List Nat)} {fr : List Nat}
    (hfr : CandList h cs [] fr) : Struct M h cs [] M.init fr ((fr.length : Int) - 1) :=
  ⟨rfl, trivial, hfr, by omega, by omega⟩

theorem prefixBad_top {M : SeqModel σ α} {h : List (Op α)} {B : List Nat} {t : σ}
    {fr : List Nat} : PrefixBad M h B t fr ((fr.length : Int) - 1) := by
  intro q y hq hy
  have := (List.getElem?_eq_some_iff.mp hy).1
  omega

theorem bad_init {M : SeqModel σ α} {h : List (Op α)} {s : σ} {fr : List Nat} :
    Bad M h [] s fr ((fr.length : Int) - 1) [] :=
  ⟨trivial, prefixBad_top, fun _ hc => by cases hc⟩

/-- A refused step leads nowhere. -/
theorem succBad_of_none {M : SeqModel σ α} {h : List (Op α)} {B : List Nat} {t : σ} {y : Nat}
    (hst : ∀ o, h[y]? = some o → M.step t o.val = none) : SuccBad M h B t y := by
  intro o t' ho hs
  rw [hst o ho] at hs; cases hs

/-- A step to a cached configuration, with the candidate not on the stack, leads nowhere. -/
theorem succBad_of_cached {M : SeqModel σ α} {h : List (Op α)} {fs : List (Frame σ)} {t : σ}
    {cache : List ((Nat → Prop) × σ)} {y : Nat} (hc : CacheOk M h fs cache) (hy : y ∉ ids fs)
    (hcached : ∀ o t', h[y]? = some o → M.step t o.val = some t' →
      ∃ c ∈ cache, (∀ i, c.1 i ↔ i ∈ y :: ids fs) ∧ c.2 = t') :
    SuccBad M h (ids fs) t y := by
  intro o t' ho hst hg
  obtain ⟨c, hcm, hset, hst'⟩ := hcached o t' ho hst
  rcases hc c hcm with ⟨fs', hsuf, hids, _⟩ | hbad
  · exact hy (ids_suffix hsuf ((hids y).mp ((hset y).mpr (List.mem_cons_self ..))))
  · exact hbad (hst' ▸ good_congr (fun i => (hset i).symm) hg)

/-- The cursor moves down past a candidate that leads nowhere. -/
theorem prefixBad_down {M : SeqModel σ α} {h : List (Op α)} {B : List Nat} {t : σ}
    {fr : List Nat} {p : Nat} {y : Nat} (hb : PrefixBad M h B t fr p) (hy : fr[p]? = some y)
    (hs : SuccBad M h B t y) : PrefixBad M h B t fr ((p : Int) - 1) := by
  intro q z hq hz
  rcases Nat.lt_or_ge p q with h1 | h1
  · exact hb q z (by omega) hz
  · have : q = p := by omega
    subst this; rw [hy] at hz; cases hz; exact hs

theorem bad_down {M : SeqModel σ α} {h : List (Op α)} {fs : List (Frame σ)} {s : σ}
    {fr : List Nat} {p : Nat} {cache : List ((Nat → Prop) × σ)} {y : Nat}
    (hb : Bad M h fs s fr p cache) (hy : fr[p]? = some y) (hs : SuccBad M h (ids fs) s y) :
    Bad M h fs s fr ((p : Int) - 1) cache :=
  ⟨hb.1, prefixBad_down hb.2.1 hy hs, hb.2.2⟩

theorem struct_down {M : SeqModel σ α} {h : List (Op α)} {cs : List (List Nat)}
    {fs : List (Frame σ)} {s : σ} {fr : List Nat} {p : Nat}
    (hs : Struct M h cs fs s fr p) : Struct M h cs fs s fr ((p : Int) - 1) :=
  ⟨hs.1, hs.2.1, hs.2.2.1, by omega, by have := hs.2.2.2.2; omega⟩

/-- A candidate lifted: the frame records the position and the list; the new cursor is the new
list's top. -/
theorem struct_push {M : SeqModel σ α} {h : List (Op α)} {cs : List (List Nat)}
    {fs : List (Frame σ)} {s t' : σ} {fr fr' : List Nat} {p : Int} {q y : Nat} {o : Op α}
    (hs : Struct M h cs fs s fr p) (hy : fr[q]? = some y) (ho : h[y]? = some o)
    (hst : M.step s o.val = some t') (hfr' : CandList h cs (y :: ids fs) fr') :
    Struct M h cs (⟨y, s, q, fr⟩ :: fs) t' fr' ((fr'.length : Int) - 1) :=
  ⟨⟨hs.1, o, ho, hst⟩, ⟨hs.2.1, hs.2.2.1, hy⟩, hfr', by omega, by omega⟩

theorem bad_push {M : SeqModel σ α} {h : List (Op α)} {cs : List (List Nat)}
    {fs : List (Frame σ)} {s t' : σ} {fr fr' : List Nat} {p : Int} {q y : Nat} {o : Op α}
    {cache : List ((Nat → Prop) × σ)}
    (hs : Struct M h cs fs s fr p) (hb : Bad M h fs s fr q cache) (ho : h[y]? = some o)
    (hst : M.step s o.val = some t') :
    Bad M h (⟨y, s, q, fr⟩ :: fs) t' fr' ((fr'.length : Int) - 1)
      ((fun i => i ∈ y :: ids fs, t') :: cache) := by
  have hch' : Chain M h (⟨y, s, q, fr⟩ :: fs) t' := ⟨hs.1, o, ho, hst⟩
  refine ⟨⟨hb.1, hb.2.1⟩, prefixBad_top, ?_⟩
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact Or.inl ⟨_, List.suffix_refl _, fun i => Iff.rfl, hch'⟩
  · rcases hb.2.2 c hc with ⟨fs', hsuf, hids, hch2⟩ | hbad
    · exact Or.inl ⟨fs', hsuf.trans (List.suffix_cons _ _), hids, hch2⟩
    · exact Or.inr hbad

/-- Every candidate tried, and some operation not linearized: no completion. -/
theorem bad_here {M : SeqModel σ α} {h : List (Op α)} {cs : List (List Nat)} {B : List Nat}
    {s : σ} {fr : List Nat} (hwf : CallLeRet h) (hfr : CandList h cs B fr)
    (hall : PrefixBad M h B s fr (-1)) (hinc : ∃ y, y < h.length ∧ y ∉ B) :
    ¬ Good M h (· ∈ B) s := by
  rintro ⟨π, hnd, hmem, hrun, hpw⟩
  cases π with
  | nil =>
    obtain ⟨y, hy, hyB⟩ := hinc
    exact absurd ((hmem y).mpr ⟨hy, hyB⟩) (List.not_mem_nil)
  | cons x π' =>
    have hx := (hmem x).mp (List.mem_cons_self ..)
    obtain ⟨o, ho⟩ : ∃ o, h[x]? = some o := ⟨h[x], List.getElem?_eq_getElem hx.1⟩
    have hvals : vals h (x :: π') = o.val :: vals h π' := by
      simp only [vals, List.filterMap_cons, ho, Option.map_some]
    rw [hvals] at hrun
    simp only [run] at hrun
    obtain ⟨t', hst, hrun'⟩ : ∃ t', M.step s o.val = some t' ∧ (run M t' (vals h π')).isSome := by
      revert hrun
      cases M.step s o.val with
      | none => simp
      | some t' => intro hr; exact ⟨t', rfl, hr⟩
    have hgood' : Good M h (· ∈ x :: B) t' := by
      refine ⟨π', (List.nodup_cons.mp hnd).2, fun k => ?_, hrun', (List.pairwise_cons.mp hpw).2⟩
      have hk := hmem k
      constructor
      · intro hk'
        have hkx : k ≠ x := fun h' => (List.nodup_cons.mp hnd).1 (h' ▸ hk')
        obtain ⟨h1, h2⟩ := hk.mp (List.mem_cons_of_mem _ hk')
        exact ⟨h1, fun h3 => (List.mem_cons.mp h3).elim hkx h2⟩
      · rintro ⟨h1, h2⟩
        have hkx : k ≠ x := fun h' => h2 (h' ▸ List.mem_cons_self ..)
        have := hk.mpr ⟨h1, fun h3 => h2 (List.mem_cons_of_mem _ h3)⟩
        exact (List.mem_cons.mp this).resolve_left hkx
    -- `x` is a candidate: its predecessors not in `B` would be later in `π`
    have hcand : Cand h B x := by
      refine ⟨hx.1, hx.2, fun z hz => ?_⟩
      refine Classical.byContradiction fun hzB => ?_
      obtain ⟨oz, ox, hoz, hox, _⟩ := id hz
      have hzlt : z < h.length := (List.getElem?_eq_some_iff.mp hoz).1
      have hzπ := (hmem z).mpr ⟨hzlt, hzB⟩
      have hzx : z ≠ x := by
        rintro rfl; exact prec_irrefl hwf z hz
      exact (List.pairwise_cons.mp hpw).1 z ((List.mem_cons.mp hzπ).resolve_left hzx) hz
    obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem ((hfr.2 x).mpr hcand)
    exact hall q x (by omega) (by rw [List.getElem?_eq_getElem hq, hqe]) o t' ho hst hgood'

/-- Backtracking: the frame's configuration had no completion; the search resumes in the frame's
list, below its position. -/
theorem struct_pop {M : SeqModel σ α} {h : List (Op α)} {cs : List (List Nat)} {f : Frame σ}
    {fs : List (Frame σ)} {s : σ} {fr : List Nat} {p : Int}
    (hs : Struct M h cs (f :: fs) s fr p) : Struct M h cs fs f.pre f.fr ((f.pos : Int) - 1) := by
  obtain ⟨⟨hch, _⟩, ⟨hfs, hfr, hpos⟩, _⟩ := hs
  exact ⟨hch, hfs, hfr, by omega, by have := (List.getElem?_eq_some_iff.mp hpos).1; omega⟩

theorem bad_pop {M : SeqModel σ α} {h : List (Op α)} {cs : List (List Nat)} {f : Frame σ}
    {fs : List (Frame σ)} {s : σ} {fr : List Nat} {p : Int} {cache : List ((Nat → Prop) × σ)}
    (hwf : CallLeRet h) (hs : Struct M h cs (f :: fs) s fr p)
    (hb : Bad M h (f :: fs) s fr (-1) cache) (hinc : ∃ y, y < h.length ∧ y ∉ ids (f :: fs)) :
    Bad M h fs f.pre f.fr ((f.pos : Int) - 1) cache := by
  have hbad := bad_here hwf hs.2.2.1 hb.2.1 hinc
  obtain ⟨⟨hch, o, ho, hst⟩, ⟨_, _, hpos⟩, _⟩ := hs
  obtain ⟨⟨hfb, hpre⟩, _, hcache⟩ := hb
  refine ⟨hfb, prefixBad_down hpre hpos ?_, fun c hc => ?_⟩
  · intro o' t' ho' hst'
    rw [ho] at ho'; cases ho'; rw [hst] at hst'; cases hst'
    exact hbad
  · rcases hcache c hc with ⟨fs', hsuf, hids, hch2⟩ | hb'
    · rcases List.suffix_cons_iff.mp hsuf with rfl | hsuf
      · have := chain_det hch2 ⟨hch, o, ho, hst⟩
        exact Or.inr fun hg => hbad (good_congr hids (this ▸ hg))
      · exact Or.inl ⟨fs', hsuf, hids, hch2⟩
    · exact Or.inr hb'

/-- Nothing to backtrack: the history is not linearizable. -/
theorem bad_fail {M : SeqModel σ α} {h : List (Op α)} {cs : List (List Nat)} {s : σ}
    {fr : List Nat} {p : Int} {cache : List ((Nat → Prop) × σ)} (hwf : CallLeRet h)
    (hs : Struct M h cs [] s fr p) (hb : Bad M h [] s fr (-1) cache)
    (hinc : ∃ y, y < h.length) : ¬ Linearizable M h := by
  have hbad := bad_here hwf hs.2.2.1 hb.2.1 (by
    obtain ⟨y, hy⟩ := hinc; exact ⟨y, hy, List.not_mem_nil⟩)
  have hs0 : s = M.init := hs.1
  subst hs0
  exact fun hl => hbad (good_congr (fun i => by simp [ids]) hl)

/-! ## Soundness -/

theorem framesStruct_cand {h : List (Op α)} {cs : List (List Nat)} :
    ∀ {f : Frame σ} {fs'}, FramesStruct h cs (f :: fs') → Cand h (ids fs') f.id
  | _, _, ⟨_, hfr, hpos⟩ => (hfr.2 _).mp (List.mem_of_getElem? hpos)

theorem framesStruct_nodup {h : List (Op α)} {cs : List (List Nat)} :
    ∀ {fs : List (Frame σ)}, FramesStruct h cs fs → (ids fs).Nodup
  | [], _ => List.nodup_nil
  | f :: fs, hfs => by
    have hc : Cand h (ids fs) f.id := framesStruct_cand hfs
    exact List.nodup_cons.mpr ⟨hc.2.1, framesStruct_nodup hfs.1⟩

theorem framesStruct_lt {h : List (Op α)} {cs : List (List Nat)} :
    ∀ {fs : List (Frame σ)}, FramesStruct h cs fs → ∀ y ∈ ids fs, y < h.length
  | [], _, _, hy => by cases hy
  | f :: fs, hfs, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (framesStruct_cand hfs).1
    · exact framesStruct_lt hfs.1 y hy

/-- The frames' order (oldest first) respects real time: a later frame's operation does not
precede an earlier one's. -/
theorem framesStruct_pairwise {h : List (Op α)} {cs : List (List Nat)} :
    ∀ {fs : List (Frame σ)}, FramesStruct h cs fs →
      (ids fs).reverse.Pairwise (fun a b => ¬ Prec h b a)
  | [], _ => List.Pairwise.nil
  | f :: fs, hfs => by
    have hc : Cand h (ids fs) f.id := framesStruct_cand hfs
    simp only [ids, List.map_cons, List.reverse_cons]
    refine List.pairwise_append.mpr ⟨framesStruct_pairwise hfs.1, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb hp
    rw [List.mem_singleton] at hb
    subst hb
    rw [List.mem_reverse] at ha
    -- `a` is below `f`; `f.id` preceding `a` would put `f.id` below `a`, so among `ids fs`
    exact hc.2.1 (framesStruct_below hfs.1 a ha f.id hp)
where
  /-- An operation preceding one on the stack is below it on the stack. -/
  framesStruct_below : ∀ {fs : List (Frame σ)}, FramesStruct h cs fs →
      ∀ a ∈ ids fs, ∀ z, Prec h z a → z ∈ ids fs
    | [], _, _, ha, _, _ => by cases ha
    | g :: gs, hgs, a, ha, z, hz => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_cons_of_mem _ ((framesStruct_cand hgs).2.2 z hz)
      · exact List.mem_cons_of_mem _ (framesStruct_below hgs.1 a ha z hz)

theorem run_append (M : SeqModel σ α) :
    ∀ (s : σ) (l1 l2 : List α), run M s (l1 ++ l2) = (run M s l1).bind (fun t => run M t l2)
  | _, [], _ => rfl
  | s, a :: l1, l2 => by
    cases hst : M.step s a with
    | none => simp [run, hst]
    | some s' => simp only [List.cons_append, run, hst]; exact run_append M s' l1 l2

/-- The stack, oldest first, runs on the model from its initial state to the current state. -/
theorem chain_run {M : SeqModel σ α} {h : List (Op α)} :
    ∀ {fs : List (Frame σ)} {s : σ}, Chain M h fs s → run M M.init (vals h (ids fs).reverse) = some s
  | [], _, hc => by simp only [Chain] at hc; subst hc; rfl
  | f :: fs, _, ⟨hc, o, ho, hst⟩ => by
    have hv : vals h (ids (f :: fs)).reverse = vals h (ids fs).reverse ++ [o.val] := by
      simp [ids, vals, List.filterMap_append, ho]
    rw [hv, run_append, chain_run hc]
    simp [run, hst]

/-- Every operation lifted: the stack, oldest first, is a linearization. -/
theorem sound_done {M : SeqModel σ α} {h : List (Op α)} {cs : List (List Nat)}
    {fs : List (Frame σ)} {s : σ} {fr : List Nat} {p : Int}
    (hs : Struct M h cs fs s fr p) (hall : ∀ y, y < h.length → y ∈ ids fs) :
    Linearizable M h := by
  refine ⟨(ids fs).reverse, List.pairwise_reverse.mpr ((framesStruct_nodup hs.2.1).imp fun h e => h e.symm), fun k => ?_,
    ?_, framesStruct_pairwise hs.2.1⟩
  · rw [List.mem_reverse]
    exact ⟨fun hk => ⟨framesStruct_lt hs.2.1 k hk, fun h => h⟩, fun ⟨hk, _⟩ => hall k hk⟩
  · rw [chain_run hs.1]; rfl

end Theory
end github_com.anishathalye.porcupine
end Perennial
