/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/hook/OptCondF.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`hook.OptCondF` (hook/cond.go, after the fork's SWB-6 fix 2c16fdc): a condition `cond` and the
functions stored while it was false (`funs[:funs_num]`). The replica group's internal specs
(not frozen); SwiftPaxos's descriptors use one as `afterPropagate` (the leader's acks wait for
the proposal: `cond` is `desc.propose != nil`).

* `hook.ocf.ownOcf cf cond fs`: the object, its condition `cond`, the stored functions `fs`.
* `hook.ocf.condOk cond Pc`: the condition reads a state `Pc v` and returns `v`.
* `hook.ocf.chain fs Q`: running `fs` in order ends with `Q` (each function's WP, nested).
* `Call(f)`: `cond` true: the stored functions then `f` run (`chain (fs ++ [f]) Q`), the store
  is empty after; false: `f` is stored.
* `Recall()`: with stored functions and `cond` true they run and the store is empty; else
  nothing.
* `NewOptCondF(cond)`, `ReinitCondF(cond)`: an empty store with `cond`.

The object is given back (empty) **before** the functions run: since SWB-8's fix (fork 67d211b)
`Call`/`Recall` copy the stored functions into a private slice and touch neither the object nor
its array afterwards, so a function may retire the object's owner and hand the object on.
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.hook
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace hook.ocf

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [hook.Assumptions]

/-- The `*OptCondF` at `cf`: condition `cond`, stored functions `fs` (a prefix of its slice). -/
def ownOcf (cf : Loc) (cond : GoFunc) (fs : List GoFunc) : IProp netDistGF :=
  iprop(∃ (sl : GoSlice) (L : List GoFunc), cf ↦ hook.OptCondF.mk cond sl (W64 fs.length) ∗
    sl ↦* L ∗ ownSliceCap GoFunc sl (DFrac.own 1) ∗ ⌜fs <+: L ∧ fs.length < 2 ^ 62⌝)

/-- The condition: on the state `Pc v` it returns `v`. -/
def condOk (cond : GoFunc) (Pc : Bool → IProp netDistGF) : IProp netDistGF :=
  iprop(∀ (v : Bool), {{ Pc v }} (App (Val #cond) (Val #())) {{ RET #v; Pc v }})

/-- Running `fs` in order ends with `Q`. -/
def chain : List GoFunc → IProp netDistGF → IProp netDistGF
  | [], Q => Q
  | g :: gs, Q => iprop(WP (App (Val #g) (Val #())) {{ fun rv => iprop(⌜rv = #()⌝ ∗ chain gs Q) }})

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [hook.Assumptions]

/-- `NewOptCondF(cond)`. -/
abbrev NewOptCondF.specI : Prop :=
  ∀ (cond : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.hook }}
    (App (Val (@! hook.NewOptCondF)) (Val #cond))
  {{ (cf : Loc), RET #cf; ownOcf cf cond [] }}

/-- `cf.ReinitCondF(cond)`: `cf` itself (any store before) or, for `nil`, a new one. -/
abbrev OptCondF.ReinitCondF.specI : Prop :=
  ∀ (cf : Loc) (cond0 : GoFunc) (fs : List GoFunc) (cond : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.hook ∗
      (⌜cf = null⌝ ∨ ownOcf cf cond0 fs) }}
    (App (Val (cf @!! go.GoType.PointerType hook.OptCondF.ty @!! go!"ReinitCondF")) (Val #cond))
  {{ (cf' : Loc), RET #cf'; ownOcf cf' cond [] }}

/-- `cf.Call(f)` with the condition's state `Pc v`: `v` true: the stored functions and `f` run
(`chain`, given the condition's state back first), the store is empty; `v` false: `f` stored
(premise: the store is not huge). -/
abbrev OptCondF.Call.specI : Prop :=
  ∀ (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (f : GoFunc) (Pc : Bool → IProp netDistGF)
    (v : Bool) (Q : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.hook ∗
      ownOcf cf cond fs ∗ □ condOk cond Pc ∗ Pc v ∗ ⌜fs.length + 1 < 2 ^ 62⌝ ∗
      (if v then iprop(Pc v -∗ ownOcf cf cond [] -∗ chain (fs ++ [f]) Q) else iprop(True)) }}
    (App (Val (cf @!! go.GoType.PointerType hook.OptCondF.ty @!! go!"Call")) (Val #f))
  {{ (b : Bool), RET #b; ⌜b = v⌝ ∗
      (if v then Q else iprop(ownOcf cf cond (fs ++ [f]) ∗ Pc v)) }}

/-- `cf.Recall()` with the condition's state `Pc v`: with stored functions and `v` true they run
(`chain`) and the store is empty; else nothing (the condition's state back; its `cond` is
read only when the store is not empty). -/
abbrev OptCondF.Recall.specI : Prop :=
  ∀ (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (Pc : Bool → IProp netDistGF) (v : Bool)
    (Q : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.hook ∗
      ownOcf cf cond fs ∗ □ condOk cond Pc ∗ Pc v ∗
      (if v && !fs.isEmpty then iprop(Pc v -∗ ownOcf cf cond [] -∗ chain fs Q) else iprop(True)) }}
    (App (Val (cf @!! go.GoType.PointerType hook.OptCondF.ty @!! go!"Recall")) (Val #()))
  {{ (b : Bool), RET #b; ⌜b = (v && !fs.isEmpty)⌝ ∗
      (if v && !fs.isEmpty then Q else iprop(ownOcf cf cond fs ∗ Pc v)) }}

end specs

end hook.ocf

namespace hook.ocf

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [hook.Assumptions]

set_option goose.wp.extras true

theorem NewOptCondF.wp_proof : NewOptCondF.specI (hG := hG) := by
  intro cond
  wp_start
  wp_auto
  iapply HΦ
  unfold ownOcf
  iexists slice.nil, []
  iframe
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  ipureintro; exact ⟨List.nil_prefix, by decide⟩

theorem OptCondF.Recall.wp_proof : OptCondF.Recall.specI (hG := hG) := by
  intro cf cond fs Pc v Q
  wp_start as ⟨Hown, #Hcond, HPc, Hch⟩
  unfold ownOcf
  icases Hown with ⟨%sl, %L, Hcf, Hsl, Hcap, %Hpre⟩
  have hlen : sint.Z (W64 fs.length) = fs.length := by
    have := Hpre.2; word
  by_cases hfs : fs = []
  · subst hfs
    wp_auto
    iapply HΦ
    simp only [List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
    isplitr
    · ipureintro; trivial
    iframe
    ipureintro; exact Hpre
  have hpos : 0 < fs.length := List.length_pos_iff.mpr hfs
  wp_auto
  rw [decide_eq_true (show sint.Z (W64 0) < sint.Z (W64 fs.length) by rw [hlen]; simp; omega)]
  wp_auto
  ihave Hc := Hcond
  iunfold condOk at Hc
  ispecialize Hc $$ %v
  dsimp only
  wp_bind (App (Val #cond) (Val #()))
  iapply Hc $$ [HPc]
  · iexact HPc
  inext
  iintro HPc
  have hne : fs.isEmpty = false := by cases fs <;> simp_all
  cases v
  · wp_auto
    iapply HΦ
    simp only [Bool.false_and, Bool.false_eq_true, ite_false]
    isplitr
    · ipureintro; trivial
    iframe
    ipureintro; exact Hpre
  simp only [hne, Bool.not_false, Bool.and_self, ite_true] at *
  ihave Hch := Hch $$ HPc
  wp_auto
  wp_apply (wp_slice_make2 (V := GoFunc) (W64 fs.length)) as %tsl ⟨Htsl, Htcap⟩
  · ipureintro; rw [hlen]; omega
  try wp_auto
  ihave %HLl := ownSlice_len _ _ _ $$ Hsl
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  have hfL : fs.length ≤ L.length := by
    obtain ⟨u, hu⟩ := Hpre.1; rw [← hu, List.length_append]; omega
  have e1 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 fs.length) ∧
      sint.Z (W64 fs.length) ≤ sint.Z sl.len := by
    rw [hlen]; refine ⟨by decide, by simp, by omega⟩
  rw [ite_eq_left ⟨hb.1, hb.2.1, by omega⟩]
  ihave ⟨Hs0, Hsm, Hs2⟩ := (ownSlice_slice (W64 0) (W64 fs.length) sl _ L hb).1 $$ Hsl
  try wp_auto
  wp_apply wp_slice_copy $$ [$Htsl $Hsm] as %cn ⟨-, Htsl, Hsm⟩
  ihave Hsl := (ownSlice_slice (W64 0) (W64 fs.length) sl _ L hb).2 $$ [Hs0 Hsm Hs2]
  · iframe Hs0 Hs2; iExactEq Hsm; rfl
  have hfl : sint.nat (W64 fs.length) = fs.length := by word
  have hsub : subslice 0 (sint.nat (W64 fs.length)) L = fs := by
    unfold subslice
    rw [hfl, List.drop_zero]
    obtain ⟨u, hu⟩ := Hpre.1; rw [← hu, List.take_left' rfl]
  try wp_auto
  ihave Hch := Hch $$ [Hcf Hsl Hcap]
  · iexists sl, L
    iframe Hsl Hcap
    isplitl [Hcf]
    · iExactEq Hcf; rfl
    · ipureintro; exact ⟨List.nil_prefix, by simp⟩
  ihave Htsl : tsl ↦* fs $$ [Htsl]
  · iExactEq Htsl
    rw [hsub, List.length_replicate, hfl, List.take_length, List.drop_eq_nil_of_le (by simp),
      List.append_nil]
  ihave HL : (∃ (i : Nat),
      "i" ∷ i_ptr ↦ W64 i ∗ "Hsl" ∷ tsl ↦* fs ∗
      "Hch" ∷ chain (fs.drop i) Q ∗ "%Hi" ∷ ⌜i ≤ fs.length⌝ : IProp netDistGF)
    $$ [i Htsl Hch]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for HL
  have hi62 : i < 2 ^ 62 := by have := Hpre.2; omega
  have hiz : sint.Z (W64 i) = i := by word
  wp_if_destruct
  · have hlt : i < fs.length := by
      first
      | (rw [hiz, hlen] at Hif; omega)
      | (have h := of_decide_eq_true (go.intoVal_inj Hif); rw [hiz, hlen] at h; omega)
    have hgL : fs[i]? = some fs[i] := List.getElem?_eq_getElem hlt
    ihave %HTl := ownSlice_len _ _ _ $$ Hsl
    have e2 : sint.nat tsl.len = (sint.Z tsl.len).toNat := rfl
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 i) ∧ sint.Z (W64 i) < sint.Z tsl.len by
      rw [hiz]; constructor <;> omega)]
    wp_apply wp_load_slice_index (t := go.FunctionType (go.Signature [] false [])) tsl (sint.Z (W64 i))
      fs _ fs[i] (by omega) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rw [hiz]; simpa using hgL
    rw [List.drop_eq_getElem_cons hlt]
    simp only [chain]
    wp_bind (App (Val #fs[i]) (Val #()))
    iapply wp_wand $$ Hch
    iintro %rv ⟨%hrv, Hch⟩
    subst hrv
    wp_auto
    wp_for_post
    iframe
    iexists i + 1
    iframe
    isplitl [i]
    · iExactEq i; congr 1; word
    ipureintro; omega
  · have hge : fs.length ≤ i := by
      first
      | (rw [hiz, hlen] at Hif; omega)
      | (have h := of_decide_eq_false (go.intoVal_inj Hif); rw [hiz, hlen] at h; omega)
      | (simp only [hiz, hlen] at Hif; omega)
    rw [List.drop_of_length_le hge]
    simp only [chain]
    try wp_auto
    iapply HΦ
    isplitr
    · ipureintro; trivial
    iexact Hch


theorem prefix_set_snoc {α : Type} (fs L : List α) (f : α) (h : fs <+: L) (hl : fs.length < L.length) :
    fs ++ [f] <+: L.set fs.length f := by
  obtain ⟨u, rfl⟩ := h
  cases u with
  | nil => simp at hl
  | cons a u =>
    refine ⟨u, ?_⟩
    rw [List.set_append_right _ _ (Nat.le_refl _)]
    simp

theorem OptCondF.Call.wp_proof : OptCondF.Call.specI (hG := hG) := by
  intro cf cond fs f Pc v Q
  wp_start as ⟨Hown, #Hcond, HPc, %Hfl, Hch⟩
  unfold ownOcf
  icases Hown with ⟨%sl, %L, Hcf, Hsl, Hcap, %Hpre⟩
  have hlen : sint.Z (W64 fs.length) = fs.length := by
    have := Hpre.2; word
  ihave %HLl := ownSlice_len _ _ _ $$ Hsl
  have e1 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
  have hfL : fs.length ≤ L.length := by
    obtain ⟨u, hu⟩ := Hpre.1; rw [← hu, List.length_append]; omega
  wp_auto
  ihave Hc := Hcond
  iunfold condOk at Hc
  ispecialize Hc $$ %v
  dsimp only
  wp_bind (App (Val #cond) (Val #()))
  iapply Hc $$ [HPc]
  · iexact HPc
  inext
  iintro HPc
  cases v
  · -- stored
    wp_auto
    wp_if_destruct
    · -- append
      have hfeq : fs.length = L.length := by
        have : sint.Z sl.len ≤ sint.Z (W64 fs.length) := by
          simp_all
        rw [hlen] at this; omega
      wp_apply wp_slice_literal (V := GoFunc) [f]
      isplitr
      · ipureintro; rfl
      iintro %s1 ⟨Hs1, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [Hsl Hcap Hs1] as %nsl ⟨Hsl, Hcap, -⟩
      · iframe
      wp_auto
      iapply HΦ
      isplitr
      · ipureintro; trivial
      iframe
      isplitl [Hcf]
      · iExactEq Hcf; congr 2; simp only [List.length_append, List.length_singleton]; word
      ipureintro
      refine ⟨?_, by simp only [List.length_append, List.length_singleton]; omega⟩
      have : fs = L := List.IsPrefix.eq_of_length Hpre.1 hfeq
      rw [this]; exact List.prefix_refl _
    · have hlt : fs.length < L.length := by
        have : ¬ sint.Z sl.len ≤ sint.Z (W64 fs.length) := by simp_all
        rw [hlen] at this; omega
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 fs.length) ∧ sint.Z (W64 fs.length) < sint.Z sl.len by
        rw [hlen]; constructor <;> omega)]
      wp_apply (wp_store_slice_index (t := go.FunctionType (go.Signature [] false [])) sl
        (sint.Z (W64 fs.length)) L f) $$ [Hsl] as Hsl
      · iframe Hsl; ipureintro; rw [hlen]; omega
      try wp_auto
      iapply HΦ
      isplitr
      · ipureintro; trivial
      iframe HPc
      iexists sl, L.set fs.length f
      iframe Hcap
      isplitl [Hcf]
      · iExactEq Hcf; congr 2; simp only [List.length_append, List.length_singleton]; word
      isplitl [Hsl]
      · iExactEq Hsl; rw [hlen]; simp
      ipureintro
      exact ⟨prefix_set_snoc fs L f Hpre.1 hlt, by
        simp only [List.length_append, List.length_singleton]; omega⟩
  simp only [ite_true]
  ihave Hch := Hch $$ HPc
  wp_auto
  wp_apply (wp_slice_make2 (V := GoFunc) (W64 fs.length)) as %tsl ⟨Htsl, Htcap⟩
  · ipureintro; rw [hlen]; omega
  try wp_auto
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 fs.length) ∧
      sint.Z (W64 fs.length) ≤ sint.Z sl.len := by
    rw [hlen]; refine ⟨by decide, by simp, by omega⟩
  rw [ite_eq_left ⟨hb.1, hb.2.1, by omega⟩]
  ihave ⟨Hs0, Hsm, Hs2⟩ := (ownSlice_slice (W64 0) (W64 fs.length) sl _ L hb).1 $$ Hsl
  try wp_auto
  wp_apply wp_slice_copy $$ [$Htsl $Hsm] as %cn ⟨-, Htsl, Hsm⟩
  ihave Hsl := (ownSlice_slice (W64 0) (W64 fs.length) sl _ L hb).2 $$ [Hs0 Hsm Hs2]
  · iframe Hs0 Hs2; iExactEq Hsm; rfl
  have hfl : sint.nat (W64 fs.length) = fs.length := by word
  have hsub : subslice 0 (sint.nat (W64 fs.length)) L = fs := by
    unfold subslice
    rw [hfl, List.drop_zero]
    obtain ⟨u, hu⟩ := Hpre.1; rw [← hu, List.take_left' rfl]
  try wp_auto
  ihave Hch := Hch $$ [Hcf Hsl Hcap]
  · iexists sl, L
    iframe Hsl Hcap
    isplitl [Hcf]
    · iExactEq Hcf; rfl
    · ipureintro; exact ⟨List.nil_prefix, by simp⟩
  ihave Htsl : tsl ↦* fs $$ [Htsl]
  · iExactEq Htsl
    rw [hsub, List.length_replicate, hfl, List.take_length, List.drop_eq_nil_of_le (by simp),
      List.append_nil]
  ihave HL : (∃ (i : Nat),
      "i" ∷ i_ptr ↦ W64 i ∗ "Hsl" ∷ tsl ↦* fs ∗
      "Hch" ∷ chain (fs.drop i ++ [f]) Q ∗ "%Hi" ∷ ⌜i ≤ fs.length⌝ : IProp netDistGF)
    $$ [i Htsl Hch]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for HL
  have hi62 : i < 2 ^ 62 := by have := Hpre.2; omega
  have hiz : sint.Z (W64 i) = i := by word
  wp_if_destruct
  · have hlt : i < fs.length := by
      first
      | (rw [hiz, hlen] at Hif; omega)
      | (have h := of_decide_eq_true (go.intoVal_inj Hif); rw [hiz, hlen] at h; omega)
    have hgL : fs[i]? = some fs[i] := List.getElem?_eq_getElem hlt
    ihave %HTl := ownSlice_len _ _ _ $$ Hsl
    have e2 : sint.nat tsl.len = (sint.Z tsl.len).toNat := rfl
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 i) ∧ sint.Z (W64 i) < sint.Z tsl.len by
      rw [hiz]; constructor <;> omega)]
    wp_apply wp_load_slice_index (t := go.FunctionType (go.Signature [] false [])) tsl (sint.Z (W64 i))
      fs _ fs[i] (by omega) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rw [hiz]; simpa using hgL
    rw [List.drop_eq_getElem_cons hlt]
    simp only [List.cons_append, chain]
    wp_bind (App (Val #fs[i]) (Val #()))
    iapply wp_wand $$ Hch
    iintro %rv ⟨%hrv, Hch⟩
    subst hrv
    wp_auto
    wp_for_post
    iframe
    iexists i + 1
    iframe
    isplitl [i]
    · iExactEq i; congr 1; word
    ipureintro; omega
  · have hge : fs.length ≤ i := by
      first
      | (rw [hiz, hlen] at Hif; omega)
      | (have h := of_decide_eq_false (go.intoVal_inj Hif); rw [hiz, hlen] at h; omega)
      | (simp only [hiz, hlen] at Hif; omega)
    rw [List.drop_of_length_le hge]
    simp only [List.nil_append, chain]
    wp_bind (App (Val #f) (Val #()))
    iapply wp_wand $$ Hch
    iintro %rv ⟨%hrv, HQ⟩
    subst hrv
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; trivial
    iexact HQ

theorem OptCondF.ReinitCondF.wp_proof (wp_New : NewOptCondF.specI (hG := hG)) :
    OptCondF.ReinitCondF.specI (hG := hG) := by
  intro cf cond0 fs cond
  wp_start as Hown
  wp_auto
  icases Hown with (%Hnil | Hown)
  · subst Hnil
    wp_auto
    wp_apply wp_New as %cf' Hcf'
    iapply HΦ
    iexact Hcf'
  · unfold ownOcf
    icases Hown with ⟨%sl, %L, Hcf, Hsl, Hcap, %Hpre⟩
    ihave ⟨Hcf, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hcf
    rw [decide_eq_false Hnn]
    wp_auto
    iapply HΦ
    iframe
    ipureintro; exact ⟨List.nil_prefix, by simp⟩

end proofs

end hook.ocf

end Perennial.github_com.imdea_software.swiftpaxos
