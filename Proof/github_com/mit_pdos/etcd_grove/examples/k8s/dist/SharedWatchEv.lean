/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: a watch's events on related histories (first layer)

`notes/k8s-dist-k4.md`, "Handoff K4-3", step 4. The change between two renamed stores is the renamed
change (`changeAtL_ren`, the renaming injective on the stores' revisions), and so is its event
(`toEventL_ren`, a deletion's event at the change's revision renamed with it): the event at a
cluster revision `ρ r` is the search's at `r`, renamed (`evAtL_ren`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedList

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

/-- An event with its object renamed. -/
def renEv (ρ : Nat → Nat) (e : WEv) : WEv := ⟨e.t, renObj ρ e.o⟩

/-- A change with its objects renamed, at the revision `r'`. -/
def renChg (ρ : Nat → Nat) (r' : Nat) (ch : Chg) : Chg :=
  ⟨ch.key, ch.prev.map (renObj ρ), ch.cur.map (renObj ρ), r'⟩

theorem changeAtL_rv' : ∀ (p q : List item) (r : Nat) (ch : Chg), changeAtL p q r = some ch → ch.rv = r
  | [], [], _, _, h => by simp [changeAtL] at h
  | _ :: _, [], _, _, h => by simp only [changeAtL, Option.some.injEq] at h; subst h; rfl
  | [], _ :: _, _, _, h => by simp only [changeAtL, Option.some.injEq] at h; subst h; rfl
  | p :: ps, q :: qs, r, ch, h => by
    simp only [changeAtL] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    split at h
    · exact changeAtL_rv' ps qs r ch h
    · simp only [Option.some.injEq] at h; subst h; rfl

/-- **The change between renamed stores is the renamed change**, when the renaming tells their items
apart. -/
theorem changeAtL_ren (ρ : Nat → Nat) (r r' : Nat) :
    ∀ (P Q : List item), (∀ p ∈ P, ∀ q ∈ Q, renItem ρ p = renItem ρ q → p = q) →
      changeAtL (P.map (renItem ρ)) (Q.map (renItem ρ)) r' = (changeAtL P Q r).map (renChg ρ r')
  | [], [], _ => rfl
  | _ :: _, [], _ => rfl
  | [], _ :: _, _ => rfl
  | p :: ps, q :: qs, hinj => by
    simp only [List.map_cons, changeAtL, renItem_key]
    by_cases h1 : go.GoStringLt p.key' q.key'
    · simp only [h1, decide_true, if_true, Option.map_some]; rfl
    by_cases h2 : go.GoStringLt q.key' p.key'
    · simp only [h1, h2, decide_true, decide_false, if_true, if_false, Bool.false_eq_true,
        Option.map_some]; rfl
    simp only [h1, h2, decide_false, Bool.false_eq_true, if_false]
    by_cases h3 : p = q
    · subst h3
      simp only [decide_true, if_true]
      exact changeAtL_ren ρ r r' ps qs fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb)
    · have h4 : renItem ρ p ≠ renItem ρ q := fun e => h3 (hinj p List.mem_cons_self q List.mem_cons_self e)
      simp only [h3, h4, decide_false, Bool.false_eq_true, if_false, Option.map_some]; rfl

/-- An object at the revision `r` renamed is at `ρ r`. -/
theorem renObj_at (ρ : Nat → Nat) (o : Obj) (r : Nat) (hr : r < 2 ^ 64) :
    renObj ρ { o with ResourceVersion' := W64 (r : Int) } = { o with ResourceVersion' := W64 (ρ r : Int) } := by
  simp only [renObj]
  rw [show uint.nat (W64 (r : Int)) = r by word]

/-- **A renamed change's event is the renamed event.** -/
theorem toEventL_ren (ρ : Nat → Nat) (x : Input) (ch : Chg) (r' : Nat) (hr : ch.rv < 2 ^ 64)
    (hρ : ρ ch.rv = r') : toEventL x (renChg ρ r' ch) = (toEventL x ch).map (renEv ρ) := by
  obtain ⟨k, prev, cur, rv⟩ := ch
  simp only at hr hρ
  subst hρ
  have fin : ∀ o : Obj, renObj ρ { o with ResourceVersion' := W64 (rv : Int) } =
      { o with ResourceVersion' := W64 (ρ rv : Int) } := fun o => renObj_at ρ o rv hr
  cases prev with
  | none =>
    cases cur with
    | none => rfl
    | some b => by_cases hb : selOkL x b = true <;> simp [toEventL, renChg, renEv, selOkL_ren, hb]
  | some a =>
    cases cur with
    | none =>
      by_cases ha : selOkL x a = true
      · simp only [toEventL, renChg, Option.map_some, Option.map_none, Option.any_some, Option.any_none,
          selOkL_ren, ha, Bool.false_and, Bool.false_eq_true, if_false, if_true, renEv, renObj_with_rv, fin]
      · simp [toEventL, renChg, selOkL_ren, ha]
    | some b =>
      by_cases ha : selOkL x a = true <;> by_cases hb : selOkL x b = true <;>
        simp only [toEventL, renChg, Option.map_some, Option.map_none, Option.any_some, Option.any_none,
          selOkL_ren, ha, hb, Bool.false_and, Bool.and_false, Bool.and_true, Bool.false_eq_true, if_false,
          if_true, renEv, renObj_with_rv, fin, Bool.not_eq_true]

/-- **The event at a cluster revision is the search's, renamed**, when the stores before and at it
are renamed and the renaming tells their items apart. -/
theorem evAtL_ren (ρ : Nat → Nat) (x : Input) (hs hc : List GSt) (r r' : Nat) (hr : 2 ≤ r)
    (hr' : 2 ≤ r') (hlt : r < 2 ^ 64) (hρ : ρ r = r')
    (h1 : (histN hc (r' - 1)).items = (histN hs (r - 1)).items.map (renItem ρ))
    (h2 : (histN hc r').items = (histN hs r).items.map (renItem ρ))
    (hinj : ∀ p ∈ (histN hs (r - 1)).items, ∀ q ∈ (histN hs r).items, renItem ρ p = renItem ρ q → p = q) :
    evAtL x hc r' = (evAtL x hs r).map (renEv ρ) := by
  unfold evAtL
  rw [if_pos hr, if_pos hr', h1, h2, changeAtL_ren ρ r r' _ _ hinj]
  cases hch : changeAtL (histN hs (r - 1)).items (histN hs r).items r with
  | none => rfl
  | some ch =>
    have hrv := changeAtL_rv' _ _ _ _ hch
    simp only [Option.map_some, Option.bind_some, renChg]
    split
    · exact toEventL_ren ρ x ch r' (by rw [hrv]; exact hlt) (by rw [hrv]; exact hρ)
    · rfl

/-- The renaming of items is injective where it is on their revisions. -/
theorem renItem_inj (ρ : Nat → Nat) (p q : item) (hp : ρ (uint.nat p.obj'.ResourceVersion') < 2 ^ 64)
    (hq : ρ (uint.nat q.obj'.ResourceVersion') < 2 ^ 64)
    (hi : ρ (uint.nat p.obj'.ResourceVersion') = ρ (uint.nat q.obj'.ResourceVersion') →
      uint.nat p.obj'.ResourceVersion' = uint.nat q.obj'.ResourceVersion')
    (h : renItem ρ p = renItem ρ q) : p = q := by
  obtain ⟨pk, ⟨a1, a2, a3, a4, a5, a6, prv, a8⟩, pc⟩ := p
  obtain ⟨qk, ⟨b1, b2, b3, b4, b5, b6, qrv, b8⟩, qc⟩ := q
  simp only [renItem, renObj, item.mk.injEq, Obj.mk.injEq] at h ⊢
  obtain ⟨hk, ⟨e1, e2, e3, e4, e5, e6, erv, e8⟩, hc⟩ := h
  refine ⟨hk, ⟨e1, e2, e3, e4, e5, e6, ?_, e8⟩, hc⟩
  have : ρ (uint.nat prv) = ρ (uint.nat qrv) := by
    have := congrArg (uint.nat ·) erv; word
  have := hi this
  word

end go

end k8s_dist
end EtcdGrove
end Perennial
