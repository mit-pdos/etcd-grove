/-
A sorter seen through a map of its elements (`sorterSpec_map`): `sort.Stable`'s proof
(`Proof/sort/Stable.lean`) runs `stable`'s model on the sorter's list tagged with the positions
(`List.zipIdx`), whose first components are the list.
-/
module

public import Spec.sort.Sort
public import Proof.sort.StableCorrect

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A sorter of a list `l.map f` is a sorter of `l`, comparing by `lt` on the images. -/
theorem sorterSpec_map {E E' : Type} (x : GoInterfaceOk) (R : List E → IProp GF)
    (lt : E → E → Bool) (f : E' → E) :
    sorterSpec x R lt ⊢ sorterSpec x (fun l => R (l.map f)) (fun a b => lt (f a) (f b)) := by
  unfold sorterSpec
  iintro #⟨#HLen, #HLess, #HSwap⟩
  isplitr
  · iintro !> %l %Φ !> Hl HΦ
    iapply HLen $$ %(l.map f) Hl
    rw [List.length_map]
    iexact HΦ
  isplitr
  · iintro !> %l %i %j %a %b %Hij %Φ !> Hl HΦ
    iapply HLess $$ %(l.map f) %i %j %(f a) %(f b) [] Hl HΦ
    ipureintro
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    exact ⟨hi, hj, by simp [ha], by simp [hb]⟩
  · iintro !> %l %i %j %a %b %Hij %Φ !> Hl HΦ
    iapply HSwap $$ %(l.map f) %i %j %(f a) %(f b) [] Hl
    · ipureintro
      obtain ⟨hi, hj, ha, hb⟩ := Hij
      exact ⟨hi, hj, by simp [ha], by simp [hb]⟩
    rw [← List.map_set, ← List.map_set]
    iexact HΦ

/-- Perennial's strict weak order, on Booleans (`stableModel.SWO`). -/
theorem swo_of_strictWeakOrder {E : Type} (lt : E → E → Bool)
    (h : slices.StrictWeakOrder (fun a b => lt a b = true)) : stableModel.SWO lt := by
  refine ⟨fun x => ?_, fun x y z => h.strict_weak_order_trans x y z, fun x y z hxy hyz => ?_⟩
  · cases hx : lt x x
    · rfl
    · exact absurd hx (h.strict_weak_order_irrefl x)
  · cases hxz : lt x z
    · rfl
    · exfalso
      cases hyx : lt y x
      · cases hzy : lt z y
        · have e1 : ¬ lt x y = true ∧ ¬ lt y x = true := by simp [hxy, hyx]
          have e2 : ¬ lt y z = true ∧ ¬ lt z y = true := by simp [hyz, hzy]
          have e3 := h.strict_weak_order_equiv.trans e1 e2
          exact e3.1 hxz
        · have := h.strict_weak_order_trans x z y hxz hzy
          rw [hxy] at this; cases this
      · have := h.strict_weak_order_trans y x z hyx hxz
        rw [hyz] at this; cases this

end defs

end EtcdGrove
end Perennial
