/-
**`path.Join(["/", p])` of a clean absolute path `p` is `p`** (2026-10-24, the merge of the rafthttp
work into `lean`): k8s's `etcd3.New` joins its prefix that way (`path.PathCleanAbs`,
`Spec/path/Defs.lean`). Derived from `path.Join`'s spec over the model (`Proof/path/Model.lean`):
such a `p` is a rooted path of clean segments (`cleanSeg`), which `Clean` leaves as it is. Lean-first.
-/
module

public import Proof.path.Segs
public import Spec.path.Join
public import Spec.path.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace path

section
variable [FfiSyntax]

theorem lit_slashslash : (go!"//" : List w8) = [slash, slash] := by decide
theorem lit_slash : (go!"/" : List w8) = [slash] := by decide
theorem lit_sds : (go!"/./" : List w8) = [slash, dot, slash] := by decide
theorem lit_sd : (go!"/." : List w8) = [slash, dot] := by decide
theorem lit_sdds : (go!"/../" : List w8) = [slash, dot, dot, slash] := by decide
theorem lit_sdd : (go!"/.." : List w8) = [slash, dot, dot] := by decide

theorem pred_of_mem_takeWhile (f : w8 → Bool) : ∀ (l : List w8) (x : w8), x ∈ l.takeWhile f → f x = true
  | [], _, h => by simp at h
  | c :: l, x, h => by
    rw [List.takeWhile_cons] at h
    split at h
    · next hc =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact hc
      · exact pred_of_mem_takeWhile f l x h
    · simp at h

/-- The segments of the rest `q` of a clean absolute path `p = pre ++ "/" ++ q`. -/
theorem segs_of_suffix (p : List w8) (hp : PathCleanAbs p) :
    ∀ (n : Nat) (pre q : List w8), q.length ≤ n → p = pre ++ slash :: q → q ≠ [] →
      ∃ segs, segs ≠ [] ∧ (∀ s ∈ segs, cleanSeg s) ∧ slash :: q = segsPath segs := by
  obtain ⟨-, -, hss, hsl, hds, hdd, -⟩ := hp
  have hss' : ¬ [slash, slash] <:+: p := by rw [← lit_slashslash]; exact hss
  have hsl' : ¬ [slash] <:+ p := by rw [← lit_slash]; exact hsl
  unfold k8s.dotSeg at hds; unfold k8s.dotDot at hdd
  simp only [decide_eq_false_iff_not, not_or] at hds hdd
  have hsds : ¬ [slash, dot, slash] <:+: p := by rw [← lit_sds]; exact hds.2.2.2
  have hsd : ¬ [slash, dot] <:+ p := by rw [← lit_sd]; exact hds.2.2.1
  have hsdds : ¬ [slash, dot, dot, slash] <:+: p := by rw [← lit_sdds]; exact hdd.2.2.2
  have hsdd : ¬ [slash, dot, dot] <:+ p := by rw [← lit_sdd]; exact hdd.2.2.1
  intro n
  induction n with
  | zero => intro pre q hq _ hne; cases q with | nil => exact absurd rfl hne | cons _ _ => simp at hq
  | succ n ih =>
    intro pre q hq hpq hne
    let s := q.takeWhile (fun c => c != slash)
    let rest := q.dropWhile (fun c => c != slash)
    have hsr : s ++ rest = q := List.takeWhile_append_dropWhile
    have hsns : ∀ c ∈ s, c ≠ slash := by
      intro c hc
      have := pred_of_mem_takeWhile _ q c hc
      simpa using this
    -- the segment is not empty: no `//`
    have hsne : s ≠ [] := by
      intro h0
      cases q with
      | nil => exact hne rfl
      | cons c q' =>
        have hc : c = slash := by
          by_cases hc : c = slash
          · exact hc
          exfalso
          have : s = c :: (q'.takeWhile (fun c => c != slash)) := by
            simp [s, List.takeWhile_cons]; exact hc
          rw [this] at h0; simp at h0
        exact hss' ⟨pre, q', by rw [hpq, hc]; simp⟩
    rcases hrest : rest with _ | ⟨x, q'⟩
    · -- the last segment
      have hq : q = s := by rw [← hsr, hrest, List.append_nil]
      refine ⟨[s], by simp, ?_, by simp [segsPath, hq]⟩
      intro s' hs'
      simp only [List.mem_singleton] at hs'
      subst hs'
      refine ⟨hsne, hsns, ?_, ?_⟩
      · intro h1; exact hsd ⟨pre, by rw [hpq, hq, h1]⟩
      · intro h2; exact hsdd ⟨pre, by rw [hpq, hq, h2]⟩
    · -- a segment, then `/`
      have hx : x = slash := by
        have hw : q.dropWhile (fun c => c != slash) ≠ [] := by
          rw [show q.dropWhile (fun c => c != slash) = rest from rfl, hrest]; simp
        have := List.head_dropWhile_not (fun c => c != slash) hw
        simp only [show q.dropWhile (fun c => c != slash) = rest from rfl, hrest, List.head_cons] at this
        simpa using this
      subst hx
      have hq : q = s ++ slash :: q' := by rw [← hsr, hrest]
      have hq'ne : q' ≠ [] := by
        rintro rfl
        exact hsl' ⟨pre ++ slash :: s, by rw [hpq, hq]; simp⟩
      have hlen : q'.length ≤ n := by
        have : q.length = s.length + 1 + q'.length := by rw [hq]; simp; omega
        have := List.length_pos_iff.2 hsne
        omega
      obtain ⟨segs, hsne', hsc, hseq⟩ := ih (pre ++ slash :: s) q' hlen (by rw [hpq, hq]; simp) hq'ne
      refine ⟨s :: segs, by simp, ?_, ?_⟩
      · intro s' hs'
        simp only [List.mem_cons] at hs'
        rcases hs' with rfl | hs'
        · refine ⟨hsne, hsns, ?_, ?_⟩
          · intro h1
            exact hsds ⟨pre, q', by rw [hpq, hq, h1]; simp⟩
          · intro h2
            exact hsdds ⟨pre, q', by rw [hpq, hq, h2]; simp⟩
        · exact hsc s' hs'
      · rw [segsPath_cons, ← hseq, hq]; simp

/-- A clean absolute path is a rooted path of clean segments. -/
theorem segs_of_cleanAbs (p : List w8) (hp : PathCleanAbs p) :
    ∃ segs, segs ≠ [] ∧ (∀ s ∈ segs, cleanSeg s) ∧ p = segsPath segs := by
  have hp' := hp
  obtain ⟨hpre, hne1, -⟩ := hp'
  rw [lit_slash] at hpre hne1
  obtain ⟨q, rfl⟩ := hpre
  have hq : q ≠ [] := by rintro rfl; exact hne1 rfl
  exact segs_of_suffix ([slash] ++ q) hp q.length [] q (Nat.le_refl _) (by simp) hq

/-- **`Join(["/", p])` of a clean absolute path** (the model): `p`. -/
theorem joinModel_slash_cleanAbs (p : List w8) (hp : PathCleanAbs p) :
    joinModel [go!"/", p] = p := by
  obtain ⟨segs, hne, hcs, rfl⟩ := segs_of_cleanAbs p hp
  obtain ⟨s1, b, rfl⟩ : ∃ s1 b, segs = s1 :: b := by
    cases segs with | nil => exact absurd rfl hne | cons s1 b => exact ⟨s1, b, rfl⟩
  have hs1 := hcs s1 (by simp)
  have hb : ∀ s ∈ b, cleanSeg s := fun x hx => hcs x (by simp [hx])
  rw [lit_slash]
  have hP : segsPath (s1 :: b) = [slash] ++ s1 ++ segsPath b := segsPath_cons s1 b
  have hbuf : joinBuf [[slash], segsPath (s1 :: b)] [] = [slash, slash] ++ segsPath (s1 :: b) := by
    simp [joinBuf]
  have hsum : ([[slash], segsPath (s1 :: b)].map List.length).sum ≠ 0 := by simp
  unfold joinModel
  rw [if_neg hsum, hbuf]
  -- `Clean("//" ++ p)`: two `/`s skipped, then the segments copied
  have hP3 : [slash, slash] ++ segsPath (s1 :: b) = [slash, slash, slash] ++ s1 ++ segsPath b := by
    rw [hP]; simp
  unfold cleanModel
  rw [if_neg (by simp)]
  have hhead : ([slash, slash] ++ segsPath (s1 :: b)).getD 0 0 = slash := by simp
  simp only [hhead, decide_true, ↓reduceIte]
  rw [cleanLoop_slash _ _ _ _ _ (by rw [hP3]; simp) (by rw [hP3]; simp),
    cleanLoop_slash _ _ _ _ _ (by rw [hP3]; simp) (by rw [hP3]; simp)]
  have hseg := cleanLoop_seg [slash, slash, slash] s1 (segsPath b) [slash] hs1
    (segsPath_tail b [] (Or.inl rfl) |>.imp (fun h => by simpa using h) (fun h => by simpa using h))
  rw [← hP3] at hseg
  simp only [List.length_cons, List.length_nil, List.length_singleton, ne_eq,
    not_true_eq_false, ↓reduceIte] at hseg
  rw [show (1 + 1 + 1 : Nat) = 3 from rfl] at hseg
  rw [hseg]
  have hall := cleanLoop_segs_pre [slash, slash] [s1] b [] (by simp) (by simpa using hs1) hb
    (Or.inl rfl)
  simp only [List.append_nil, List.singleton_append] at hall
  have e1 : [slash] ++ s1 = segsPath [s1] := by simp [segsPath]
  have e2 : 0 + 1 + 1 + 1 + s1.length = [slash, slash].length + (segsPath [s1]).length := by
    rw [← e1]; simp; omega
  rw [e1, show 3 + s1.length = [slash, slash].length + (segsPath [s1]).length by rw [← e1]; simp; omega,
    hall]
  rw [cleanLoop_stop _ _ _ _ _ (by simp; omega)]
  rw [if_neg (by rw [segsPath_cons]; simp)]

end

section spec
open Iris Iris.BI Iris.ProofMode
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`path.Join(["/", p])` of a clean absolute path returns `p`** (k8s's `etcd3.New`; until the
merge of the rafthttp work, 2026-10-24, the statement of a trust-boundary axiom on the names-only
`path`): from `path.Join`'s spec. -/
theorem Join_cleanAbs (hJ : path.Join.spec (GF := GF) (hG := hG)) (elems : GoSlice) (dq : DFrac)
    (p : GoString) (hp : PathCleanAbs p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.path ∗ elems ↦*{dq} [go!"/", p] }}
      (App (Val (@! _root_.Perennial.path.Join)) (Val #elems))
    {{ RET #p; elems ↦*{dq} [go!"/", p] }} := by
  have hl := hp.2.2.2.2.2.2
  have hb : ([go!"/", p].map List.length).sum + [go!"/", p].length < 2 ^ 62 := by
    rw [lit_slash]; simp; omega
  iintro %Φ ⟨#Hpkg, Hs⟩ HΦ
  wp_apply hJ elems [go!"/", p] dq hb $$ [Hs] as %r ⟨%Hr, Hs⟩
  · iframe
  rw [Hr, joinModel_slash_cleanAbs p hp]
  iapply HΦ $$ Hs

end spec

end path
end EtcdGrove
end Perennial
