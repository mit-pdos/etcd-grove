/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/Alloc.lean`, run `rabia-r1wake-1`.)

`ServerInit`'s ghost allocations (internal to the server's proof): a ghost map with a list of
fresh keys' elements, the proxy's receipts of its clients' requests (`pRcpt`), and families of
ghost names indexed by the servers (`push X`, `rcpt X`).
-/
module

public import Dsverify.Proof.rabia.Core.Chans

@[expose] public section

noncomputable section

namespace Perennial.rabia

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

set_option linter.unusedSectionVars false

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- Insert a list of fresh keys into a ghost map, with their elements. -/
theorem ghostMap_insert_list {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (γ : GName) (v : V) :
    ∀ (L : List K) (m : GMap K V), L.Nodup → (∀ x ∈ L, m.lookup x = none) →
      (ghostMapAuth γ 1 m : IProp GF) ⊢ |==> ∃ m' : GMap K V, ghostMapAuth γ 1 m' ∗
        [∗list] x ∈ L, ghostMapElem γ x (DFrac.own 1) v
  | [], m, _, _ => by
    iintro H
    imodintro
    iexists m
    iframe H
    iapply BigSepL.bigSepL_nil.2; iempintro
  | x :: L, m, hnd, hfr => by
    iintro H
    imod ghost_map_insert x v (hfr x (List.mem_cons_self ..)) $$ H with ⟨H, Hx⟩
    have hnd' := List.nodup_cons.1 hnd
    imod ghostMap_insert_list γ v L (m.insert x v) hnd'.2 (fun y hy => by
      rw [GMap.lookup_insert_ne m v (by rintro rfl; exact hnd'.1 hy)]
      exact hfr y (List.mem_cons_of_mem _ hy)) $$ H with ⟨%m', H, HL⟩
    imodintro
    iexists m'
    iframe H
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- A fresh ghost map holding the elements of `L` (its authority dropped). -/
theorem ghostMap_alloc_list {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (v : V) (L : List K) (hnd : L.Nodup) :
    ⊢ |==> ∃ γ, ([∗list] x ∈ L, ghostMapElem γ x (DFrac.own 1) v : IProp GF) := by
  imod ghost_map_alloc_empty (GF := GF) (K := K) (V := V) with ⟨%γ, H⟩
  imod ghostMap_insert_list γ v L ∅ hnd (fun _ _ => rfl) $$ H with ⟨%m', -, HL⟩
  imodintro
  iexists γ
  iexact HL

theorem nodup_pairs (B : Nat) :
    ∀ cs : List Nat, cs.Nodup → (cs.flatMap (fun c => (List.range B).map (fun n => (c, n)))).Nodup
  | [], _ => by simp
  | c :: cs, h => by
    rw [List.flatMap_cons, List.nodup_append]
    obtain ⟨hc, hcs⟩ := List.nodup_cons.1 h
    refine ⟨?_, nodup_pairs B cs hcs, ?_⟩
    · unfold List.Nodup
      rw [List.pairwise_map]
      exact List.nodup_range.imp (fun h e => h (Prod.mk.inj e).2)
    · intro a ha b hb e
      subst e
      simp only [List.mem_map, List.mem_range] at ha
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hb
      obtain ⟨n, _, rfl⟩ := ha
      obtain ⟨c', hc', n', _, e⟩ := hb
      exact hc ((Prod.mk.inj e).1 ▸ hc')

/-- The proxy's receipts of every request of every client (`pRcpt`'s ghost map). -/
theorem prc_alloc_gen (C B : Nat) :
    ⊢ |==> ∃ γ, ([∗list] c ∈ List.range C, [∗list] n ∈ List.range B,
      ghostMapElem γ (c, n) (DFrac.own 1) () : IProp GF) := by
  have hnd := nodup_pairs B (List.range C) List.nodup_range
  imod ghostMap_alloc_list (GF := GF) () _ hnd with ⟨%γ, H⟩
  imodintro
  iexists γ
  rw [BigSepL.bigSepL_flatMap]
  iapply BigSepL.bigSepL_mono_of_forall ?_ $$ H
  intro _ c
  rw [BigSepL.bigSepL_map]

theorem prc_alloc :
    ⊢ |==> ∃ γ, ([∗list] c ∈ List.range nC, [∗list] n ∈ List.range opBudget,
      ghostMapElem γ (c, n) (DFrac.own 1) () : IProp GF) :=
  prc_alloc_gen nC opBudget

omit [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] go_gctx sem in
/-- A family of ghost names over the servers, each allocated by `alloc`. -/
theorem family_alloc (P : Nat → GName → IProp GF) (alloc : ∀ X, ⊢ |==> ∃ g, P X g) :
    ∀ n, ⊢ |==> ∃ f : Nat → GName, [∗list] X ∈ List.range n, P X (f X)
  | 0 => by
    imodintro
    iexists fun _ => default
    simp only [List.range_zero]
    iapply BigSepL.bigSepL_nil.2; iempintro
  | n + 1 => by
    imod family_alloc P alloc n with ⟨%f, H⟩
    imod alloc n with ⟨%g, Hg⟩
    imodintro
    iexists fun X => if X = n then g else f X
    rw [List.range_succ]
    iapply BigSepL.bigSepL_snoc.2
    isplitl [H]
    · iapply BigSepL.bigSepL_mono ?_ $$ H
      intro i X hX
      have : X < n := List.mem_range.1 (List.mem_of_getElem? hX)
      dsimp only
      rw [ite_eq_right_iff.2 (fun h => absurd h (by omega))]
    · simp only [List.length_range, ↓reduceIte]
      iexact Hg

instance isSrvKeys_persistent (γ : Names) (k : Nat) (γl : SrvNames) :
    Persistent (isSrvKeys (GF := GF) γ k γl) := by
  unfold isSrvKeys; infer_instance

/-- `prc_alloc`'s elements are the receipts of `γl` (its `prc` name). -/
theorem prc_of (γl : SrvNames) (g : GName) (h : γl.prc = g) :
    ([∗list] c ∈ List.range nC, [∗list] n ∈ List.range opBudget,
      ghostMapElem g (c, n) (DFrac.own 1) () : IProp GF) ⊢
      [∗list] c ∈ List.range nC, [∗list] n ∈ List.range opBudget, pRcpt γl c n := by
  subst h; unfold pRcpt; exact .rfl

/-- An empty mono-list's authority. -/
theorem monoList_alloc_nil (A : Type) [Pos.Countable A] :
    ⊢ |==> ∃ g, (monoListAuthOwn g 1 ([] : List A) : IProp GF) := by
  imod mono_list_own_alloc (GF := GF) ([] : List A) with ⟨%g, H, -⟩
  imodintro
  iexists g
  iexact H

end alloc

end Perennial.rabia
