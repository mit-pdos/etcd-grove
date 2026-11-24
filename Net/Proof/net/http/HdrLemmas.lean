/-
Lemmas of the header vocabulary (`hdrOwn`, `hdrVals`, `Net/Proof/net/http/Defs.lean`): what a reader of a
header map the model built (`modelReadMIMEHeader`'s `hdrOwn m hb`) has of it, for `readTransfer`'s and
`fixPragmaCacheControl`'s specs: the map, the absent names, and the values of its `"Connection"` slice;
and the lines up to a `"\n"` of a prefix of a head (`prefix_nl`, `prefix_no_nl`).
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace net.http

section pure

/-- A line up to a `"\n"` of `s ++ "\n" ++ t` (`s` without one) is `s`. -/
theorem prefix_nl {l s t : List w8} (hl : W8 10 ∉ l) (hs : W8 10 ∉ s)
    (h : l ++ [W8 10] <+: s ++ W8 10 :: t) : l = s := by
  induction l generalizing s with
  | nil =>
    cases s with
    | nil => rfl
    | cons x s =>
      obtain ⟨u, hu⟩ := h
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at hu
      exact absurd (hu.1 ▸ List.mem_cons_self) hs
  | cons y l ih =>
    cases s with
    | nil =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hu
      exact absurd (hu.1 ▸ List.mem_cons_self) hl
    | cons x s =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at hu
      have hxy : y = x := hu.1
      subst hxy
      have := ih (fun h => hl (List.mem_cons_of_mem _ h)) (fun h => hs (List.mem_cons_of_mem _ h))
        ⟨u, by rw [List.append_assoc]; exact hu.2⟩
      rw [this]

/-- A prefix of `s ++ "\n" ++ t` without a `"\n"` is a prefix of `s` (`s` without one). -/
theorem prefix_no_nl {l s t : List w8} (hl : W8 10 ∉ l) (hs : W8 10 ∉ s)
    (h : l <+: s ++ W8 10 :: t) : l <+: s := by
  induction l generalizing s with
  | nil => exact List.nil_prefix
  | cons y l ih =>
    cases s with
    | nil =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hu
      exact absurd (hu.1 ▸ List.mem_cons_self) hl
    | cons x s =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.cons.injEq] at hu
      have hxy : y = x := hu.1
      subst hxy
      exact List.prefix_cons_inj _ |>.mpr
        (ih (fun h => hl (List.mem_cons_of_mem _ h)) (fun h => hs (List.mem_cons_of_mem _ h))
          ⟨u, hu.2⟩)

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The map of a header block: a name not in it is absent, and the values of `"Connection"`'s
slice are owned. -/
theorem hdrOwn_open (m : Loc) (hb : List HdrLine) :
    hdrOwn (GF := GF) m hb ⊢ ∃ ms : GMap GoString GoSlice, m ↦$ ms ∗ hdrVals ms go!"Connection" ∗
      ⌜∀ k, k ∉ hb.map Prod.fst → ms !! k = none⌝ := by
  iintro Hh
  iunfold hdrOwn at Hh
  icases Hh with ⟨%ms, Hm, %Hdom, Hels⟩
  iexists ms
  iframe Hm
  isplitl [Hels]
  · unfold hdrVals
    cases hc : ms !! go!"Connection" with
    | none => simp only []; itrivial
    | some s =>
      simp only []
      have hmem : go!"Connection" ∈ hb.map Prod.fst := by
        have := Hdom go!"Connection"
        rw [hc] at this
        simpa using this.symm
      obtain ⟨kv, hkv, hk⟩ := List.mem_map.1 hmem
      ihave Hx := BigSepL.bigSepL_mem
        (Φ := fun (kv : HdrLine) => iprop(∃ s : GoSlice, ⌜ms !! kv.1 = some s⌝ ∗
          s ↦* ([kv.2] : List GoString))) hkv $$ Hels
      icases Hx with ⟨%s', %Hs', Hs⟩
      rw [hk, hc] at Hs'
      cases Hs'
      iexists [kv.2]
      iexact Hs
  · ipureintro
    intro k hk
    have := Hdom k
    rw [decide_eq_false hk] at this
    cases h : ms !! k with
    | none => rfl
    | some _ => rw [h] at this; cases this

/-- The values of a name the map has not. -/
theorem hdrVals_none (ms : GMap GoString GoSlice) (k : GoString) (h : ms !! k = none) :
    ⊢ hdrVals (GF := GF) ms k := by
  unfold hdrVals
  rw [h]
  iintro; itrivial

end lemmas

end net.http
end Perennial
