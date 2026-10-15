/-
Lean-first (no Rocq counterpart).

# Porcupine's search, in pure terms (2026-10-14)

Porcupine (`checker.go`, `checkSingle`) decides linearizability of a history by the
depth-first search of Wing & Gong with Lowe's memoization: the history's call and return
entries, sorted by time (`makeEntries`), are a doubly-linked list; the search *lifts* a call
(and its return) out of the list when the model can take its step from the current state,
and backtracks (*unlifts* the most recent one) when it reaches a return whose call is not
lifted; a configuration (the set of lifted operations, the model's state) already in the
cache is not explored again.

This file is the search's correctness argument, independent of the heap: what a history
and its linearizability are (`Linearizable`, porcupine's definition: closed intervals, an
operation precedes another iff it returns strictly before the other is called), the
search's abstract state (`Frame`s for the stack `calls`, the cursor `p` into the list of
entries not lifted, `rem es (ids fs)`, the cache as a list of configurations), and the
invariant `Inv` with one lemma per branch of the loop. What the checker needs for
*completeness* (a linearizable history is accepted):

- `inv_fail`: when the loop reaches a return with nothing to backtrack, the history is not
  linearizable;
- `inv_pop`: when it reaches a return with something to backtrack, the configuration it
  leaves had no completion (`Good`), and the invariant holds where it resumes;
- `inv_skip`, `inv_push`: the call branches.

The cache is sound for any hash function: a cached configuration is on the stack or has no
completion (`CacheOk`), whichever bucket it is in; a missed hit only re-explores.
-/
module

@[expose] public section

namespace Perennial
namespace github_com.anishathalye.porcupine
namespace Theory

/-- An operation of a history: what it did (`val`: its input and output) and its interval
(`call`, `ret`: porcupine's `Operation.Call` and `Return`, closed). -/
structure Op (α : Type) where
  val : α
  call : Int
  ret : Int

/-- A deterministic sequential specification (porcupine's `Model`): from a state, an
operation either is allowed and leads to one state, or is not allowed. -/
structure SeqModel (σ α : Type) where
  init : σ
  step : σ → α → Option σ

variable {σ α : Type}

/-- The state after a sequence of operations, if the model allows them. -/
def run (M : SeqModel σ α) : σ → List α → Option σ
  | s, [] => some s
  | s, a :: l =>
    match M.step s a with
    | some s' => run M s' l
    | none => none

/-- Operation `a` of history `h` precedes operation `b` in real time: it returned before `b`
was called (porcupine's intervals are closed). -/
def Prec (h : List (Op α)) (a b : Nat) : Prop :=
  ∃ oa ob, h[a]? = some oa ∧ h[b]? = some ob ∧ oa.ret < ob.call

/-- The operations of `h` at indices `π`, in that order. -/
def vals (h : List (Op α)) (π : List Nat) : List α :=
  π.filterMap fun k => (h[k]?).map Op.val

/-- `π` orders the operations of `h` outside `S` so that the model can run them from `t`, and
no operation of `π` precedes in real time one earlier in `π`. -/
def Completes (M : SeqModel σ α) (h : List (Op α)) (S : Nat → Prop) (t : σ) (π : List Nat) :
    Prop :=
  π.Nodup ∧ (∀ k, k ∈ π ↔ k < h.length ∧ ¬ S k) ∧ (run M t (vals h π)).isSome ∧
    π.Pairwise fun a b => ¬ Prec h b a

/-- A configuration of the search (the operations `S` linearized, the model's state `t`) has
a completion. -/
def Good (M : SeqModel σ α) (h : List (Op α)) (S : Nat → Prop) (t : σ) : Prop :=
  ∃ π, Completes M h S t π

/-- Porcupine's linearizability: some order of all of `h`'s operations is allowed by the
model from its initial state and respects real time. -/
def Linearizable (M : SeqModel σ α) (h : List (Op α)) : Prop :=
  Good M h (fun _ => False) M.init

theorem good_congr {M : SeqModel σ α} {h : List (Op α)} {S S' : Nat → Prop} {t : σ}
    (hS : ∀ i, S i ↔ S' i) (hg : Good M h S t) : Good M h S' t := by
  obtain ⟨π, hnd, hmem, hrun, hpw⟩ := hg
  exact ⟨π, hnd, fun k => by rw [hmem k, hS k], hrun, hpw⟩

/-! ## The entries -/

/-- An entry of the sorted list: the call (`isRet = false`) or the return of operation `id`. -/
structure Entry where
  isRet : Bool
  id : Nat
  deriving DecidableEq

/-- An entry's time: its operation's call or return time. -/
def timeOf (h : List (Op α)) (e : Entry) : Int :=
  match h[e.id]? with
  | some o => if e.isRet then o.ret else o.call
  | none => 0

/-- `byTime.Less`: earlier, or at the same time a call before a return. -/
def Less (h : List (Op α)) (a b : Entry) : Prop :=
  timeOf h a < timeOf h b ∨ (timeOf h a = timeOf h b ∧ a.isRet = false ∧ b.isRet = true)

/-- What `makeEntries` returns: every operation's call and return, once each, sorted by
`Less` (`sort.Sort`: no entry is `Less` than an earlier one); and every operation's call is
at most its return. -/
def EntriesOk (h : List (Op α)) (es : List Entry) : Prop :=
  es.Pairwise (fun a b => ¬ Less h b a) ∧ (∀ e, e ∈ es ↔ e.id < h.length) ∧
    ∀ o ∈ h, o.call ≤ o.ret

/-- The entries not lifted: of the operations outside `B`. -/
def rem (es : List Entry) (B : List Nat) : List Entry :=
  es.filter fun e => decide (e.id ∉ B)

theorem rem_get_not_mem {es : List Entry} {B : List Nat} {p : Nat} {e : Entry}
    (he : (rem es B)[p]? = some e) : e.id ∉ B := by
  have hm := List.mem_of_getElem? he
  simp only [rem, List.mem_filter, decide_eq_true_eq] at hm
  exact hm.2

theorem rem_get_mem {es : List Entry} {B : List Nat} {p : Nat} {e : Entry}
    (he : (rem es B)[p]? = some e) : e ∈ es := by
  have hm := List.mem_of_getElem? he
  simp only [rem, List.mem_filter] at hm
  exact hm.1

theorem mem_rem {es : List Entry} {B : List Nat} {e : Entry} (he : e ∈ es) (hB : e.id ∉ B) :
    e ∈ rem es B := by
  simp only [rem, List.mem_filter, decide_eq_true_eq]
  exact ⟨he, hB⟩

theorem rem_pairwise {h : List (Op α)} {es : List Entry} (B : List Nat)
    (hes : EntriesOk h es) : (rem es B).Pairwise (fun a b => ¬ Less h b a) :=
  hes.1.sublist (List.filter_sublist)

/-- In `rem es B`, an entry at a later index is not `Less` than one at an earlier index. -/
theorem rem_not_less {h : List (Op α)} {es : List Entry} {B : List Nat} {p q : Nat}
    {a b : Entry} (hes : EntriesOk h es) (hpq : p < q) (ha : (rem es B)[p]? = some a)
    (hb : (rem es B)[q]? = some b) : ¬ Less h b a := by
  have hpw := List.pairwise_iff_getElem.mp (rem_pairwise B hes)
  obtain ⟨hq, rfl⟩ := List.getElem?_eq_some_iff.mp hb
  obtain ⟨hp, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  exact hpw p q hp hq hpq

/-- A call's return is later in `rem es B`: the cursor never runs off the list while it is at
a call. -/
theorem rem_call_has_ret {h : List (Op α)} {es : List Entry} {B : List Nat} {p y : Nat}
    (hes : EntriesOk h es) (hp : (rem es B)[p]? = some ⟨false, y⟩) :
    ∃ q, p < q ∧ (rem es B)[q]? = some ⟨true, y⟩ := by
  have hy := rem_get_not_mem hp
  have hlt : y < h.length := (hes.2.1 ⟨false, y⟩).mp (rem_get_mem hp)
  have hmem : (⟨true, y⟩ : Entry) ∈ rem es B := mem_rem ((hes.2.1 _).mpr hlt) hy
  obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem hmem
  have hq' : (rem es B)[q]? = some ⟨true, y⟩ := by rw [List.getElem?_eq_getElem hq, hqe]
  refine ⟨q, ?_, hq'⟩
  rcases Nat.lt_trichotomy p q with h1 | h1 | h1
  · exact h1
  · subst h1; rw [hp] at hq'; cases hq'
  · exfalso
    have hnl := rem_not_less hes h1 hq' hp
    obtain ⟨o, ho⟩ : ∃ o, h[y]? = some o := ⟨h[y], List.getElem?_eq_getElem hlt⟩
    have hwf := hes.2.2 o (List.mem_of_getElem? ho)
    apply hnl
    simp only [Less, timeOf, ho]
    simp only [Bool.false_eq_true, ↓reduceIte, and_true]
    omega

/-! ## The search's abstract state -/

/-- A frame of the stack `calls`: the operation lifted, the state before it (`callsEntry.state`)
and where its call was in the list it was lifted from (where the search resumes). -/
structure Frame (σ : Type) where
  id : Nat
  pre : σ
  pos : Nat

/-- The operations lifted (newest first). -/
def ids (fs : List (Frame σ)) : List Nat := fs.map Frame.id

/-- The frames are steps of the model from its initial state, to `s`. -/
def Chain (M : SeqModel σ α) (h : List (Op α)) : List (Frame σ) → σ → Prop
  | [], s => s = M.init
  | f :: fs, s => Chain M h fs f.pre ∧ ∃ o, h[f.id]? = some o ∧ M.step f.pre o.val = some s

theorem chain_det {M : SeqModel σ α} {h : List (Op α)} :
    ∀ {fs : List (Frame σ)} {s s' : σ}, Chain M h fs s → Chain M h fs s' → s = s'
  | [], _, _, h1, h2 => by simp only [Chain] at h1 h2; rw [h1, h2]
  | f :: fs, _, _, ⟨_, o, ho, hs⟩, ⟨_, o', ho', hs'⟩ => by
    rw [ho] at ho'; cases ho'; rw [hs] at hs'; cases hs'; rfl

/-- Lifting `y` from `(B, t)` leads only to configurations without completion. -/
def SuccBad (M : SeqModel σ α) (h : List (Op α)) (B : List Nat) (t : σ) (y : Nat) : Prop :=
  ∀ o t', h[y]? = some o → M.step t o.val = some t' → ¬ Good M h (· ∈ y :: B) t'

/-- The entries before the cursor `p` are calls, each tried. -/
def PrefixBad (M : SeqModel σ α) (h : List (Op α)) (es : List Entry) (B : List Nat) (t : σ)
    (p : Nat) : Prop :=
  ∀ q, q < p → ∃ e, (rem es B)[q]? = some e ∧ e.isRet = false ∧ SuccBad M h B t e.id

/-- Each frame was lifted at a call of the list below it, after trying the calls before it. -/
def FramesOk (M : SeqModel σ α) (h : List (Op α)) (es : List Entry) : List (Frame σ) → Prop
  | [] => True
  | f :: fs => FramesOk M h es fs ∧ PrefixBad M h es (ids fs) f.pre f.pos ∧
      (rem es (ids fs))[f.pos]? = some ⟨false, f.id⟩

/-- A cached configuration is one of the stack's. -/
def OnStack (M : SeqModel σ α) (h : List (Op α)) (fs : List (Frame σ))
    (c : (Nat → Prop) × σ) : Prop :=
  ∃ fs', fs' <:+ fs ∧ (∀ i, c.1 i ↔ i ∈ ids fs') ∧ Chain M h fs' c.2

/-- Every cached configuration is on the stack or has no completion. -/
def CacheOk (M : SeqModel σ α) (h : List (Op α)) (fs : List (Frame σ))
    (cache : List ((Nat → Prop) × σ)) : Prop :=
  ∀ c ∈ cache, OnStack M h fs c ∨ ¬ Good M h c.1 c.2

/-- The loop invariant of `checkSingle`: the stack `fs` leads to the current state `s`, its
frames were lifted as the search lifts, the cursor `p` is past calls already tried, and the
cache is sound. -/
def Inv (M : SeqModel σ α) (h : List (Op α)) (es : List Entry) (fs : List (Frame σ)) (s : σ)
    (p : Nat) (cache : List ((Nat → Prop) × σ)) : Prop :=
  Chain M h fs s ∧ FramesOk M h es fs ∧ PrefixBad M h es (ids fs) s p ∧ CacheOk M h fs cache

theorem inv_init (M : SeqModel σ α) (h : List (Op α)) (es : List Entry) :
    Inv M h es [] M.init 0 [] :=
  ⟨rfl, trivial, fun _ hq => absurd hq (Nat.not_lt_zero _), fun _ hc => by cases hc⟩

theorem ids_suffix {fs fs' : List (Frame σ)} (hs : fs' <:+ fs) {i : Nat} (hi : i ∈ ids fs') :
    i ∈ ids fs :=
  (hs.map Frame.id).subset hi

/-- The branch at a call that is not lifted: the model refuses it, or the configuration it
leads to is in the cache (`cacheContains`). The cursor moves on. -/
theorem inv_skip {M : SeqModel σ α} {h : List (Op α)} {es : List Entry} {fs : List (Frame σ)}
    {s : σ} {p : Nat} {cache : List ((Nat → Prop) × σ)} {y : Nat}
    (hinv : Inv M h es fs s p cache) (hp : (rem es (ids fs))[p]? = some ⟨false, y⟩)
    (hcached : ∀ o t', h[y]? = some o → M.step s o.val = some t' →
      ∃ c ∈ cache, (∀ i, c.1 i ↔ i ∈ y :: ids fs) ∧ c.2 = t') :
    Inv M h es fs s (p + 1) cache := by
  obtain ⟨hch, hfr, hpre, hcache⟩ := hinv
  refine ⟨hch, hfr, fun q hq => ?_, hcache⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
  · exact hpre q hq
  · refine ⟨⟨false, y⟩, hp, rfl, fun o t' ho hst hg => ?_⟩
    obtain ⟨c, hc, hset, hst'⟩ := hcached o t' ho hst
    rcases hcache c hc with ⟨fs', hsuf, hids, _⟩ | hbad
    · have : y ∈ ids fs := ids_suffix hsuf ((hids y).mp ((hset y).mpr (List.mem_cons_self ..)))
      exact rem_get_not_mem hp this
    · exact hbad (hst' ▸ good_congr (fun i => (hset i).symm) hg)

/-- The branch at a call that is lifted: the model takes its step, and the configuration is
not in the cache; it is cached, pushed, and the cursor goes back to the list's head. -/
theorem inv_push {M : SeqModel σ α} {h : List (Op α)} {es : List Entry} {fs : List (Frame σ)}
    {s : σ} {p : Nat} {cache : List ((Nat → Prop) × σ)} {y : Nat} {o : Op α} {t' : σ}
    (hinv : Inv M h es fs s p cache) (hp : (rem es (ids fs))[p]? = some ⟨false, y⟩)
    (ho : h[y]? = some o) (hst : M.step s o.val = some t') :
    Inv M h es (⟨y, s, p⟩ :: fs) t' 0 ((fun i => i ∈ y :: ids fs, t') :: cache) := by
  obtain ⟨hch, hfr, hpre, hcache⟩ := hinv
  have hch' : Chain M h (⟨y, s, p⟩ :: fs) t' := ⟨hch, o, ho, hst⟩
  refine ⟨hch', ⟨hfr, hpre, hp⟩, fun _ hq => absurd hq (Nat.not_lt_zero _), ?_⟩
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact Or.inl ⟨_, List.suffix_refl _, fun i => Iff.rfl, hch'⟩
  · rcases hcache c hc with ⟨fs', hsuf, hids, hch2⟩ | hbad
    · exact Or.inl ⟨fs', hsuf.trans (List.suffix_cons _ _), hids, hch2⟩
    · exact Or.inr hbad

/-- A configuration whose cursor is at a return, past calls all tried, has no completion. -/
theorem bad_here {M : SeqModel σ α} {h : List (Op α)} {es : List Entry} {fs : List (Frame σ)}
    {s : σ} {p : Nat} {cache : List ((Nat → Prop) × σ)} {e : Entry}
    (hes : EntriesOk h es) (hinv : Inv M h es fs s p cache)
    (hp : (rem es (ids fs))[p]? = some e) (hret : e.isRet = true) :
    ¬ Good M h (· ∈ ids fs) s := by
  obtain ⟨_, _, hpre, _⟩ := hinv
  rintro ⟨π, hnd, hmem, hrun, hpw⟩
  have hd := rem_get_not_mem hp
  have hdlt : e.id < h.length := (hes.2.1 e).mp (rem_get_mem hp)
  cases π with
  | nil => exact absurd ((hmem e.id).mpr ⟨hdlt, hd⟩) (List.not_mem_nil)
  | cons x π' =>
    have hx := (hmem x).mp (List.mem_cons_self ..)
    obtain ⟨o, ho⟩ : ∃ o, h[x]? = some o := ⟨h[x], List.getElem?_eq_getElem hx.1⟩
    -- the successor of `x`
    have hvals : vals h (x :: π') = o.val :: vals h π' := by
      simp only [vals, List.filterMap_cons, ho, Option.map_some]
    rw [hvals] at hrun
    simp only [run] at hrun
    obtain ⟨t', hst, hrun'⟩ : ∃ t', M.step s o.val = some t' ∧ (run M t' (vals h π')).isSome := by
      revert hrun
      cases M.step s o.val with
      | none => simp
      | some t' => intro hr; exact ⟨t', rfl, hr⟩
    have hgood' : Good M h (· ∈ x :: ids fs) t' := by
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
    -- where `x`'s call is
    have hcm : (⟨false, x⟩ : Entry) ∈ rem es (ids fs) := mem_rem ((hes.2.1 _).mpr hx.1) hx.2
    obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem hcm
    have hq' : (rem es (ids fs))[q]? = some ⟨false, x⟩ := by
      rw [List.getElem?_eq_getElem hq, hqe]
    rcases Nat.lt_trichotomy q p with h1 | h1 | h1
    · obtain ⟨e', he', _, hbad⟩ := hpre q h1
      rw [hq'] at he'; cases he'
      exact hbad o t' ho hst hgood'
    · subst h1; rw [hq'] at hp; cases hp; cases hret
    · -- `e`, a return, is before `x`'s call: its operation precedes `x`
      have hnl := rem_not_less hes h1 hp hq'
      obtain ⟨od, hod⟩ : ∃ od, h[e.id]? = some od := ⟨h[e.id], List.getElem?_eq_getElem hdlt⟩
      have hlt : od.ret < o.call := by
        simp only [Less, timeOf, hod, ho, hret] at hnl
        simp only [Bool.false_eq_true, ↓reduceIte, and_true] at hnl
        omega
      have hdπ := (hmem e.id).mpr ⟨hdlt, hd⟩
      have hdx : e.id ≠ x := by
        intro hdx
        rw [hdx, ho] at hod; cases hod
        have := hes.2.2 o (List.mem_of_getElem? ho)
        omega
      have hdπ' := (List.mem_cons.mp hdπ).resolve_left hdx
      exact (List.pairwise_cons.mp hpw).1 e.id hdπ' ⟨od, o, hod, ho, hlt⟩

/-- The branch at a return with a frame to backtrack: the frame's configuration has no
completion; the search resumes after the frame's call, in the configuration below. -/
theorem inv_pop {M : SeqModel σ α} {h : List (Op α)} {es : List Entry} {f : Frame σ}
    {fs : List (Frame σ)} {s : σ} {p : Nat} {cache : List ((Nat → Prop) × σ)} {e : Entry}
    (hes : EntriesOk h es) (hinv : Inv M h es (f :: fs) s p cache)
    (hp : (rem es (ids (f :: fs)))[p]? = some e) (hret : e.isRet = true) :
    Inv M h es fs f.pre (f.pos + 1) cache := by
  have hbad := bad_here hes hinv hp hret
  obtain ⟨⟨hch, o, ho, hst⟩, ⟨hfr, hpre, hpos⟩, _, hcache⟩ := hinv
  refine ⟨hch, hfr, fun q hq => ?_, fun c hc => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · exact hpre q hq
    · refine ⟨⟨false, f.id⟩, hpos, rfl, fun o' t' ho' hst' => ?_⟩
      rw [ho] at ho'; cases ho'; rw [hst] at hst'; cases hst'
      exact hbad
  · rcases hcache c hc with ⟨fs', hsuf, hids, hch2⟩ | hb
    · rcases List.suffix_cons_iff.mp hsuf with rfl | hsuf
      · have := chain_det hch2 ⟨hch, o, ho, hst⟩
        exact Or.inr fun hg => hbad (good_congr hids (this ▸ hg))
      · exact Or.inl ⟨fs', hsuf, hids, hch2⟩
    · exact Or.inr hb

/-- The branch at a return with no frame to backtrack: the history is not linearizable. -/
theorem inv_fail {M : SeqModel σ α} {h : List (Op α)} {es : List Entry} {s : σ} {p : Nat}
    {cache : List ((Nat → Prop) × σ)} {e : Entry}
    (hes : EntriesOk h es) (hinv : Inv M h es [] s p cache)
    (hp : (rem es [])[p]? = some e) (hret : e.isRet = true) :
    ¬ Linearizable M h := by
  have hbad := bad_here hes hinv hp hret
  have hs : s = M.init := hinv.1
  subst hs
  exact fun hl => hbad (good_congr (fun i => by simp [ids]) hl)

end Theory
end github_com.anishathalye.porcupine
end Perennial
