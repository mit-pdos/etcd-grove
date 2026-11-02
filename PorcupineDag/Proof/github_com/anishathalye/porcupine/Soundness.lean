/-
Lean-first (no Rocq counterpart).

# Porcupine: soundness of the search, and the result law (2026-11-02)

`Sound` (pure, over `Theory`'s abstract search): what every branch of `checkSingle`'s loop keeps,
including after the context is done; `sound_done`: at the exit with the list empty, the history
is linearizable. And `checkResult_complete`, the `Check*` specs' result read by a caller that
knows the history is linearizable.

A module of its own, not part of `Theory`/`Defs`, which most of the repository imports: only
`checkSingle`'s proof and the callers of the law import it.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

namespace Perennial
namespace github_com.anishathalye.porcupine
namespace Theory

variable {σ α : Type}

/-! ## Soundness: an accepted history is linearizable

`Sound` is what every branch of the search keeps, including after the context is done (when
`StepContext` may refuse a step the model allows, and `Inv`'s `PrefixBad` is lost): the stack is
a chain of model steps, each frame lifted a call with only calls before it in the list below it,
and the cursor is past calls only. When the list is empty, the stack, oldest first, is a
linearization (`sound_done`). -/

/-- The entries before the cursor `p` in `rem es B` are calls. -/
def PrefixCalls (es : List Entry) (B : List Nat) (p : Nat) : Prop :=
  ∀ q, q < p → ∃ e, (rem es B)[q]? = some e ∧ e.isRet = false

/-- Each frame lifted a call at `pos` of the list below it, with only calls before it. -/
def FramesCalls (es : List Entry) : List (Frame σ) → Prop
  | [] => True
  | f :: fs => FramesCalls es fs ∧ (rem es (ids fs))[f.pos]? = some ⟨false, f.id⟩ ∧
      PrefixCalls es (ids fs) f.pos

/-- What survives every branch of the search (see the section header). -/
def Sound (M : SeqModel σ α) (h : List (Op α)) (es : List Entry) (fs : List (Frame σ)) (s : σ)
    (p : Nat) : Prop :=
  Chain M h fs s ∧ FramesCalls es fs ∧ PrefixCalls es (ids fs) p

theorem sound_init (M : SeqModel σ α) (h : List (Op α)) (es : List Entry) :
    Sound M h es [] M.init 0 :=
  ⟨rfl, trivial, fun _ hq => absurd hq (Nat.not_lt_zero _)⟩

theorem prefixCalls_succ {es : List Entry} {B : List Nat} {p y : Nat}
    (hpre : PrefixCalls es B p) (hp : (rem es B)[p]? = some ⟨false, y⟩) :
    PrefixCalls es B (p + 1) := by
  intro q hq
  rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
  · exact hpre q hq
  · exact ⟨_, hp, rfl⟩

/-- A call not lifted (refused, or cached): the cursor moves past it. -/
theorem sound_skip {M : SeqModel σ α} {h : List (Op α)} {es : List Entry} {fs : List (Frame σ)}
    {s : σ} {p y : Nat} (hs : Sound M h es fs s p) (hp : (rem es (ids fs))[p]? = some ⟨false, y⟩) :
    Sound M h es fs s (p + 1) :=
  ⟨hs.1, hs.2.1, prefixCalls_succ hs.2.2 hp⟩

/-- A call lifted: the model took its step. -/
theorem sound_push {M : SeqModel σ α} {h : List (Op α)} {es : List Entry} {fs : List (Frame σ)}
    {s : σ} {p y : Nat} {o : Op α} {t' : σ} (hs : Sound M h es fs s p)
    (hp : (rem es (ids fs))[p]? = some ⟨false, y⟩) (ho : h[y]? = some o)
    (hst : M.step s o.val = some t') :
    Sound M h es (⟨y, s, p⟩ :: fs) t' 0 :=
  ⟨⟨hs.1, o, ho, hst⟩, ⟨hs.2.1, hp, hs.2.2⟩, fun _ hq => absurd hq (Nat.not_lt_zero _)⟩

/-- A frame popped: the search resumes after its call. -/
theorem sound_pop {M : SeqModel σ α} {h : List (Op α)} {es : List Entry} {f : Frame σ}
    {fs : List (Frame σ)} {s : σ} {p : Nat} (hs : Sound M h es (f :: fs) s p) :
    Sound M h es fs f.pre (f.pos + 1) :=
  ⟨hs.1.1, hs.2.1.1, prefixCalls_succ hs.2.1.2.2 hs.2.1.2.1⟩

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

theorem framesCalls_nodup {es : List Entry} :
    ∀ {fs : List (Frame σ)}, FramesCalls es fs → (ids fs).Nodup
  | [], _ => List.nodup_nil
  | _ :: _, ⟨hfr, hpos, _⟩ => List.nodup_cons.mpr ⟨rem_get_not_mem hpos, framesCalls_nodup hfr⟩

theorem framesCalls_lt {h : List (Op α)} {es : List Entry} (hes : EntriesOk h es) :
    ∀ {fs : List (Frame σ)}, FramesCalls es fs → ∀ i ∈ ids fs, i < h.length
  | [], _, i, hi => by simp [ids] at hi
  | g :: gs, ⟨hfr, hpos, _⟩, i, hi => by
    rcases (show i = g.id ∨ i ∈ ids gs by simpa [ids] using hi) with rfl | hi
    · exact (hes.2.1 _).mp (rem_get_mem hpos)
    · exact framesCalls_lt hes hfr i hi

/-- An operation `y` not yet lifted when the frames were does not precede any of them in real
time: its return is in each frame's list, after the frame's call (before it there are only
calls). -/
theorem framesCalls_not_prec {h : List (Op α)} {es : List Entry} (hes : EntriesOk h es) :
    ∀ {fs : List (Frame σ)}, FramesCalls es fs → ∀ y, y ∉ ids fs → y < h.length →
      ∀ b ∈ ids fs, ¬ Prec h y b
  | [], _, _, _, _, b, hb => by simp [ids] at hb
  | g :: gs, ⟨hfr, hpos, hpre⟩, y, hy, hyl, b, hb => by
    have hy' : y ∉ ids gs := fun h' => hy (by simp only [ids, List.map_cons, List.mem_cons] at h' ⊢; exact Or.inr h')
    rcases (show b = g.id ∨ b ∈ ids gs by simpa [ids] using hb) with rfl | hb
    · have hmem : (⟨true, y⟩ : Entry) ∈ rem es (ids gs) := mem_rem ((hes.2.1 _).mpr hyl) hy'
      obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem hmem
      have hq' : (rem es (ids gs))[q]? = some ⟨true, y⟩ := by
        rw [List.getElem?_eq_getElem hq, hqe]
      rintro ⟨oy, ob, hoy, hob, hlt⟩
      rcases Nat.lt_trichotomy q g.pos with h1 | h1 | h1
      · obtain ⟨e, he, hret⟩ := hpre q h1
        rw [hq'] at he; cases he; cases hret
      · subst h1; rw [hq'] at hpos; cases hpos
      · apply rem_not_less hes h1 hpos hq'
        left
        simp [timeOf, hoy, hob, hlt]
    · exact framesCalls_not_prec hes hfr y hy' hyl b hb

theorem framesCalls_pairwise {h : List (Op α)} {es : List Entry} (hes : EntriesOk h es) :
    ∀ {fs : List (Frame σ)}, FramesCalls es fs → (ids fs).Pairwise (fun a b => ¬ Prec h a b)
  | [], _ => List.Pairwise.nil
  | g :: gs, ⟨hfr, hpos, _⟩ =>
    List.pairwise_cons.mpr ⟨fun b hb => framesCalls_not_prec hes hfr g.id (rem_get_not_mem hpos)
      ((hes.2.1 _).mp (rem_get_mem hpos)) b hb, framesCalls_pairwise hes (fs := gs) hfr⟩

/-- The exit with the list empty: every operation is on the stack, which, oldest first,
linearizes the history. -/
theorem sound_done {M : SeqModel σ α} {h : List (Op α)} {es : List Entry} {fs : List (Frame σ)}
    {s : σ} {p : Nat} (hes : EntriesOk h es) (hs : Sound M h es fs s p)
    (hrem : rem es (ids fs) = []) : Linearizable M h := by
  obtain ⟨hch, hfr, -⟩ := hs
  refine ⟨(ids fs).reverse, List.pairwise_reverse.mpr ((framesCalls_nodup hfr).imp fun hne heq => hne heq.symm), fun k => ?_, ?_,
    List.pairwise_reverse.mpr (framesCalls_pairwise hes hfr)⟩
  · rw [List.mem_reverse]
    constructor
    · intro hk; exact ⟨framesCalls_lt hes hfr k hk, fun h => h⟩
    · rintro ⟨hk, -⟩
      refine Classical.byContradiction fun hn => ?_
      have := mem_rem (B := ids fs) ((hes.2.1 ⟨false, k⟩).mpr hk) hn
      rw [hrem] at this; simp at this
  · rw [chain_run hch]; rfl


end Theory

/-- What the `Check*` specs' result (`Ok` and linearizable, `Illegal` and not, or `Unknown` with
a timeout) gives a caller that knows the history is linearizable (`L`): `Ok`, or `Unknown`
with a timeout. -/
theorem checkResult_complete {r : GoString} {L : Prop} {dur : w64}
    (hr : (r = go!"Ok" ∧ L) ∨ (r = go!"Illegal" ∧ ¬ L) ∨ (r = go!"Unknown" ∧ 0 < sint.Z dur))
    (hL : L) : r = go!"Ok" ∨ (r = go!"Unknown" ∧ 0 < sint.Z dur) := by
  rcases hr with ⟨h1, -⟩ | ⟨-, h2⟩ | h3
  · exact Or.inl h1
  · exact absurd hL h2
  · exact Or.inr h3

end github_com.anishathalye.porcupine
end Perennial
