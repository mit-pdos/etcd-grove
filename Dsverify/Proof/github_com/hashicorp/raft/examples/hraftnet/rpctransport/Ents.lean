/-
Log entries across the hraft kit transport (notes/dsv-hraft.md, S4): the sender's read-only raft
entries (`aeReq`'s `logPtr`s) as the contents a conversion copies (`logsOwn`, `entsMatch`), and the
receiver's fresh copies (`logsOwn` of a decoded request's conversion) as read-only raft entries again.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Trans

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet.rpctransport

open github_com.hashicorp.raft github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The sender's induction: read-only `logPtr`s at indexes `prev+1..` as read-only contents. -/
theorem logPtrs_core (ptrs : List Loc) : ∀ (prev : Nat) (ents : RLog),
    ([∗list] j ↦ p ∈ ptrs, ∃ e, ⌜ents[j]? = some e⌝ ∗ logPtr (GF := GF) p (prev + 1 + j) e) ⊢
    ∃ vs : List EntV, ([∗list] p;v ∈ ptrs;vs, logOwn (GF := GF) p DfracDiscarded v) ∗
      ⌜vs.length = ptrs.length ∧ ∀ j v e, vs[j]? = some v → ents[j]? = some e →
        uint.nat v.index = prev + 1 + j ∧ uint.nat v.term = e.term ∧ uint.nat v.ty = e.kind ∧
        v.data = e.data⌝ := by
  induction ptrs with
  | nil =>
    intro prev ents
    iintro -
    iexists []
    isplitl
    · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
      iempintro
    · ipureintro
      refine ⟨rfl, ?_⟩
      intro j v e hv
      simp at hv
  | cons p ptrs ih =>
    intro prev ents
    cases ents with
    | nil =>
      iintro ⟨⟨%e, %he, -⟩, -⟩
      simp at he
    | cons e0 ents' =>
      have hmono : ∀ {k : Nat} {y : Loc}, ptrs[k]? = some y →
          (iprop(∃ e, ⌜(e0 :: ents')[k + 1]? = some e⌝ ∗ logPtr (GF := GF) y (prev + 1 + (k + 1)) e)) ⊢
          iprop(∃ e, ⌜ents'[k]? = some e⌝ ∗ logPtr (GF := GF) y (prev + 1 + 1 + k) e) := by
        intro k y _
        rw [show prev + 1 + (k + 1) = prev + 1 + 1 + k by omega]
        simp only [List.getElem?_cons_succ]
        iintro H
        iexact H
      iintro H
      icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H with ⟨⟨%e, %he, Hl⟩, Ht⟩
      ihave Ht2 := (BigSepL.bigSepL_mono (PROP := IProp GF)
        (Φ := fun k y => iprop(∃ e, ⌜(e0 :: ents')[k + 1]? = some e⌝ ∗
          logPtr (GF := GF) y (prev + 1 + (k + 1)) e))
        (Ψ := fun k y => iprop(∃ e, ⌜ents'[k]? = some e⌝ ∗ logPtr (GF := GF) y (prev + 1 + 1 + k) e))
        hmono) $$ Ht
      icases ih (prev + 1) ents' $$ Ht2 with ⟨%vs, Hvs, %Hm⟩
      iunfold logPtr at Hl
      icases Hl with ⟨%lv, #Hp, #Hlv⟩
      iunfold logIs at Hlv
      icases Hlv with ⟨%Hlv, #Hd, %x, #Hx⟩
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      iexists (⟨lv.Index', lv.Term', lv.Type', e0.data, x⟩ :: vs)
      isplitl
      · iapply (BigSepL2.bigSepL2_cons (PROP := IProp GF)).2
        isplitr
        · unfold logOwn logOwnV
          iexists lv
          iframe Hp Hd Hx
          ipureintro
          exact ⟨rfl, rfl, rfl⟩
        · iexact Hvs
      · ipureintro
        obtain ⟨hlen, hm⟩ := Hm
        obtain ⟨hi, ht, hk⟩ := Hlv
        refine ⟨by simp [hlen], ?_⟩
        intro j v e' hv he'
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hv he'
          subst hv he'
          exact ⟨hi, ht, hk, rfl⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hv he'
          obtain ⟨a, b, c, d⟩ := hm j v e' hv he'
          exact ⟨by omega, b, c, d⟩

/-- The sender: `aeReq`'s entries (read-only `logPtr`s at indexes `prev+1..`) are read-only contents
`vs` matching `ents`. -/
theorem logPtrs_logsOwn (sl : GoSlice) (ptrs : List Loc) (prev : Nat) (ents : RLog) :
    sl ↦*□ ptrs ∗ ⌜ptrs.length = ents.length⌝ ∗
      ([∗list] j ↦ p ∈ ptrs, ∃ e, ⌜ents[j]? = some e⌝ ∗ logPtr p (prev + 1 + j) e) ⊢
    ∃ vs : List EntV, logsOwn (GF := GF) sl DfracDiscarded vs ∗ ⌜entsMatch vs prev ents⌝ := by
  iintro ⟨#Hsl, %Hlen, Hl⟩
  icases logPtrs_core ptrs prev ents $$ Hl with ⟨%vs, Hvs, %Hm⟩
  iexists vs
  isplitl
  · unfold logsOwn
    iexists ptrs
    iframe Hsl Hvs
  · ipureintro
    obtain ⟨h1, h2⟩ := Hm
    exact ⟨by omega, h2⟩

/-- The receiver's induction: owned contents matching `ents` become read-only `logPtr`s. -/
theorem logsOwn_core (ps : List Loc) : ∀ (vs : List EntV) (prev : Nat) (ents : RLog),
    entsMatch vs prev ents →
    ([∗list] p;v ∈ ps;vs, logOwn (GF := GF) p (DFrac.own 1) v) ⊢ |==>
      (⌜ps.length = ents.length⌝ ∗
       [∗list] j ↦ p ∈ ps, ∃ e, ⌜ents[j]? = some e⌝ ∗ logPtr (GF := GF) p (prev + 1 + j) e) := by
  induction ps with
  | nil =>
    intro vs prev ents hm
    iintro H
    ihave %hv := (BigSepL2.bigSepL2_nil_inv_left (PROP := IProp GF)) $$ H
    subst hv
    imodintro
    isplitl
    · ipureintro
      have := hm.1
      simp at this
      simp [this]
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
  | cons p ps ih =>
    intro vs prev ents hm
    iintro H
    icases (BigSepL2.bigSepL2_cons_inv_left (PROP := IProp GF)).1 $$ H with ⟨%v, %vs', %hvs, Hh, Ht⟩
    subst hvs
    obtain ⟨hlen, hm'⟩ := hm
    cases ents with
    | nil => simp at hlen
    | cons e0 ents' =>
      have htail : entsMatch vs' (prev + 1) ents' := by
        refine ⟨by simp at hlen; omega, ?_⟩
        intro j v' e' h1 h2
        obtain ⟨a, b, c, d⟩ := hm' (j + 1) v' e' (by simpa using h1) (by simpa using h2)
        exact ⟨by omega, b, c, d⟩
      obtain ⟨a0, b0, c0, d0⟩ := hm' 0 v e0 rfl rfl
      have hmono : ∀ {k : Nat} {y : Loc}, ps[k]? = some y →
          (iprop(∃ e, ⌜ents'[k]? = some e⌝ ∗ logPtr (GF := GF) y (prev + 1 + 1 + k) e)) ⊢
          iprop(∃ e, ⌜(e0 :: ents')[k + 1]? = some e⌝ ∗ logPtr (GF := GF) y (prev + 1 + (k + 1)) e) := by
        intro k y _
        rw [show prev + 1 + (k + 1) = prev + 1 + 1 + k by omega]
        simp only [List.getElem?_cons_succ]
        iintro H
        iexact H
      ihave Ht2 := ih vs' (prev + 1) ents' htail $$ Ht
      imod Ht2 with ⟨%hl, Ht2⟩
      ihave Ht3 := (BigSepL.bigSepL_mono (PROP := IProp GF)
        (Φ := fun k y => iprop(∃ e, ⌜ents'[k]? = some e⌝ ∗ logPtr (GF := GF) y (prev + 1 + 1 + k) e))
        (Ψ := fun k y => iprop(∃ e, ⌜(e0 :: ents')[k + 1]? = some e⌝ ∗
          logPtr (GF := GF) y (prev + 1 + (k + 1)) e))
        hmono) $$ Ht2
      iunfold logOwn at Hh
      icases Hh with ⟨%lv, Hp, Hv⟩
      iunfold logOwnV at Hv
      icases Hv with ⟨%Hlv, Hd, Hx⟩
      ipersist Hp
      ipersist Hd
      ipersist Hx
      imodintro
      isplitr [Ht3]
      · ipureintro; simp [hl]
      iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      isplitr [Ht3]
      · iexists e0
        isplitr
        · ipureintro; rfl
        unfold logPtr logIs
        iexists lv
        iframe Hp
        rw [← d0]
        iframe Hd
        isplitr
        · ipureintro
          obtain ⟨h1, h2, h3⟩ := Hlv
          rw [h1, h2, h3]
          exact ⟨a0, b0, c0⟩
        · iexists v.ext
          iexact Hx
      · iexact Ht3

/-- The receiver: fresh entries (`fromAppendReq`'s, owned) matching `ents` become read-only
`logPtr`s, as `aeReq` asks. -/
theorem logsOwn_logPtrs (sl : GoSlice) (vs : List EntV) (prev : Nat) (ents : RLog)
    (h : entsMatch vs prev ents) :
    logsOwn (GF := GF) sl (DFrac.own 1) vs ⊢ |==> ∃ ptrs : List Loc, sl ↦*□ ptrs ∗
      ⌜ptrs.length = ents.length⌝ ∗
      ([∗list] j ↦ p ∈ ptrs, ∃ e, ⌜ents[j]? = some e⌝ ∗ logPtr p (prev + 1 + j) e) := by
  iintro Hl
  iunfold logsOwn at Hl
  icases Hl with ⟨%ps, Hsl, Hps⟩
  ihave Hb := logsOwn_core ps vs prev ents h $$ Hps
  imod Hb with ⟨%hl, Hb⟩
  ipersist Hsl
  imodintro
  iexists ps
  iframe Hsl Hb
  ipureintro; exact hl

end lemmas

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

end Perennial
