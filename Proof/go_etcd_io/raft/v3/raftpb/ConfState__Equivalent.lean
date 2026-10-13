/-
Proof of `Spec/ConfState__Equivalent.lean`.

Until 2026-10-08 this file was `axiom raftpb.ConfState.Equivalent.wp_proof` (the Rocq
`proof_ConfState__Equivalent.v`'s `Axiom`): `raftpb` was types-only. `Equivalent`
(confstate.go, hand-written) is now translated and proved; what remains assumed is
`reflect.DeepEqual` on two `ConfState` values (`Spec/reflect_DeepEqual.lean`), Go
reflection being outside what Goose models. The statement is unchanged.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__Equivalent
public import Spec.slices.Sort
public import Spec.reflect.DeepEqual

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The body of `Equivalent`'s closure `s := func(sl *[]uint64) { *sl = append([]uint64(nil),
*sl...); slices.Sort(*sl) }`, copied from the translation (`ConfState.Equivalent.impl`,
`Code/go_etcd_io/raft/v3/raftpb.lean`) so that its triple can be stated once. -/
noncomputable abbrev sortCopyBody [FfiSyntax] [GoGlobalContext] : Expr :=
  (App (Val exceptionDo)
    (Let "sl" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType (go.GoType.SliceType go.uint64))))) (Var "sl"))
    (App (App (Val exceptionSeq) (Lam BAnon
    (App (Val doReturn)
    (Val #()))))
    (Let "$r0" (Let "$a0" (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.SliceType go.uint64)))) (Val UntypedNil))
    (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.uint64)))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.SliceType go.uint64))))) (Var "sl")))
    (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType go.uint64)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
    (App (App (Val exceptionSeq) (Lam BAnon
    (App (Val doExecute)
    (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.uint64)))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.SliceType go.uint64))))) (Var "sl")))
    (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.slices.«Sort» [(go.GoType.SliceType go.uint64), go.uint64]))) (Val #())) (Var "$a0"))))))
    (App (Val doExecute)
    (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.uint64)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.SliceType go.uint64))))) (Var "sl")) (Var "$r0")))))))))

omit package_sem in
/-- The closure on a slice known only to be empty (the six slices `Equivalent`'s callers
only know the length of): the copy is `nil` (`append` of nothing onto `nil`), which
`reflect.DeepEqual` will care about. The function value is a variable `f` fixed to the
literal, so that `wp_auto` cannot inline the call before the lemma is applied. -/
theorem wp_sortCopy_empty (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG))
    (f : GoFunc) (hf : f = func.mk BAnon (BNamed "sl") sortCopyBody)
    (slp : Loc) (sl : GoSlice) (hlen : sl.len = W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ slp ↦ sl }}
      (App (Val #f) (Val #slp))
    {{ RET #(); slp ↦ slice.nil ∗ slice.nil ↦* ([] : List w64) }} := by
  subst hf
  wp_start_folded as Hslp
  wp_auto
  ihave Hnil : (slice.nil ↦* ([] : List w64)) $$ []
  · iapply ownSlice_nil
  wp_apply wp_slice_append_nil_empty _ hlen
  wp_apply wp_slices_Sort $$ [$Hnil] as %vs' ⟨Hnil, %Hperm, -⟩
  · ipureintro; simp
  rw [List.Perm.nil_eq Hperm]
  iapply HΦ
  iframe

omit package_sem in
/-- The closure on an owned slice: the slice at `slp` becomes a fresh sorted copy,
`nil` iff empty; the input comes back as it was. -/
theorem wp_sortCopy_owned (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG))
    (f : GoFunc) (hf : f = func.mk BAnon (BNamed "sl") sortCopyBody)
    (slp : Loc) (sl : GoSlice) (vs : List w64) (dq : DFrac) (Hvlen : (vs.length : Int) ≤ 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ slp ↦ sl ∗ sl ↦*{dq} vs }}
      (App (Val #f) (Val #slp))
    {{ (sl' : GoSlice) (vs' : List w64), RET #();
        slp ↦ sl' ∗ sl ↦*{dq} vs ∗ sl' ↦* vs' ∗ ownSliceCap w64 sl' (DFrac.own 1) ∗
        ⌜vs ≡ₚ vs' ∧ SortedW64 vs' ∧ (sl' = slice.nil ↔ vs = [])⌝ }} := by
  subst hf
  wp_start_folded as ⟨Hslp, Hsl⟩
  wp_auto
  ihave Hnil : (slice.nil ↦* ([] : List w64)) $$ []
  · iapply ownSlice_nil
  ihave %Hlen := ownSlice_len $$ Hsl
  rcases Classical.em (vs = []) with Hvs | Hvs
  · -- empty: the copy is `nil`
    subst Hvs
    have Hlen0 : sl.len = W64 0 := by simp at Hlen; word
    wp_apply wp_slice_append_nil_empty _ Hlen0
    wp_apply wp_slices_Sort $$ [$Hnil] as %vs' ⟨Hnil, %Hperm, %Hsorted⟩
    · ipureintro; simp
    iapply HΦ
    iframe Hslp Hnil Hsl
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro
    exact ⟨Hperm, Hsorted, by simp⟩
  · ihave Hcapnil : ownSliceCap w64 slice.nil (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    wp_apply wp_slice_append (V := w64) slice.nil [] sl vs dq $$ [$Hnil $Hcapnil $Hsl]
      as %s' ⟨Hs', Hcap', Hsl⟩
    simp only [List.nil_append]
    wp_apply wp_slices_Sort $$ [$Hs'] as %vs' ⟨Hs', %Hperm, %Hsorted⟩
    · ipureintro; omega
    ihave %Hlen' := ownSlice_len $$ Hs'
    iapply HΦ
    iframe Hslp Hs' Hcap' Hsl
    ipureintro
    refine ⟨Hperm, Hsorted, ?_⟩
    constructor
    · intro h; exfalso
      subst h
      have : vs'.length = 0 := by rw [Hlen'.1]; rfl
      exact Hvs (List.Perm.eq_nil (Hperm.trans (List.Perm.of_eq
        (List.eq_nil_of_length_eq_zero this))))
    · intro h; exact absurd h Hvs

omit package_sem in
/-- The closure on a slice of ids that is empty or owned (`ownIdList`, 2026-10-13): a fresh
sorted copy, `nil` iff empty; the input comes back. -/
theorem wp_sortCopy_idlist (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG))
    (f : GoFunc) (hf : f = func.mk BAnon (BNamed "sl") sortCopyBody)
    (slp : Loc) (sl : GoSlice) (vs : List w64) (dq : DFrac) (Hvlen : (vs.length : Int) ≤ 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ slp ↦ sl ∗
        ownIdList sl dq vs }}
      (App (Val #f) (Val #slp))
    {{ (sl' : GoSlice) (vs' : List w64), RET #();
        slp ↦ sl' ∗ ownIdList sl dq vs ∗ sl' ↦* vs' ∗
        ⌜vs ≡ₚ vs' ∧ SortedW64 vs' ∧ (sl' = slice.nil ↔ vs = [])⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hslp, Hl⟩ HΦ
  unfold ownIdList
  icases Hl with (⟨%Hl0, %Hle⟩ | Hl)
  · subst Hle
    wp_apply (wp_sortCopy_empty wp_slices_Sort f hf) _ _ Hl0 $$ [$Hslp] as ⟨Hslp, Hnil⟩
    iapply HΦ $$ %slice.nil %([] : List w64)
    iframe Hslp Hnil
    isplitl
    · ileft; ipureintro; exact ⟨Hl0, rfl⟩
    ipureintro
    exact ⟨List.Perm.refl _, by simp [SortedW64], by simp⟩
  · wp_apply (wp_sortCopy_owned wp_slices_Sort f hf) _ _ vs dq Hvlen $$ [$Hslp $Hl]
      as %sl' %vs' ⟨Hslp, Hl, Hs, -, %Hf⟩
    iapply HΦ
    iframe Hslp Hs
    isplitl
    · iright; iexact Hl
    ipureintro; exact Hf

/-- One `ConfState` after the loop: its id slices replaced by fresh sorted copies (the
two empty ones by `nil`), the original voter and learner slices untouched. -/
def csSorted (c : Loc) (cs : raftpb.ConfState) (dq dl : DFrac) (v l : List w64) : IProp GF :=
  iprop(∃ (cs' : raftpb.ConfState) (v' l' : List w64),
    "Hc" ∷ c ↦ cs' ∗
    "Hv" ∷ cs.Voters' ↦*{dq} v ∗
    "Hl" ∷ ownIdList cs.Learners' dl l ∗
    "Hsv" ∷ cs'.Voters' ↦* v' ∗
    "Hsl" ∷ cs'.Learners' ↦* l' ∗
    "%Hfacts" ∷ ⌜cs'.VotersOutgoing' = slice.nil ∧
      cs'.LearnersNext' = slice.nil ∧ cs'.AutoLeave' = cs.AutoLeave' ∧
      v ≡ₚ v' ∧ SortedW64 v' ∧ (cs'.Voters' = slice.nil ↔ v = []) ∧
      l ≡ₚ l' ∧ SortedW64 l' ∧ (cs'.Learners' = slice.nil ↔ l = [])⌝)

theorem raftpb.ConfState.Equivalent.wp_proof
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG))
    (wp_reflect_DeepEqual : reflect.DeepEqual.spec (GF := GF) (hG := hG)) :
    raftpb.ConfState.Equivalent.spec (GF := GF) (hG := hG) := by
  intro p cs1 cs2 v1 v2 l1 l2 dq1 dq2 dl1 dl2 Hperm Hlen Hlperm Hllen H1 H3 H4 H6 Hal
  wp_start as ⟨Hp, Hv1, Hv2, Hl1, Hl2⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  -- `for _, cs := range []*ConfState{&cs1, &cs2}`
  wp_apply wp_slice_literal (V := Loc) [cs1_ptr, cs2_ptr]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hslcap⟩
  simp only [go.arrayLiteralSize, List.foldl]
  rw [show (max (max ((0 : Int) + 1 + 1) 0) 0) = 2 by decide]
  wp_auto
  -- the closure, as an opaque function value (so that its calls are not inlined)
  generalize hf : (func.mk BAnon (BNamed "sl") sortCopyBody : GoFunc) = f
  -- iteration 0 sorts `cs1`'s slices, iteration 1 `cs2`'s
  ihave IH : iprop(∃ (n : w64) (x : Loc),
      "i" ∷ i_ptr ↦ n ∗
      "cs" ∷ cs_ptr ↦ x ∗
      "Hst" ∷ ((⌜n = W64 0⌝ ∗ cs1_ptr ↦ cs1 ∗ cs1.Voters' ↦*{dq1} v1 ∗
                  ownIdList cs1.Learners' dl1 l1 ∗
                  cs2_ptr ↦ cs2 ∗ cs2.Voters' ↦*{dq2} v2 ∗ ownIdList cs2.Learners' dl2 l2) ∨
               (⌜n = W64 1⌝ ∗ csSorted cs1_ptr cs1 dq1 dl1 v1 l1 ∗ cs2_ptr ↦ cs2 ∗
                  cs2.Voters' ↦*{dq2} v2 ∗ ownIdList cs2.Learners' dl2 l2) ∨
               (⌜n = W64 2⌝ ∗ csSorted cs1_ptr cs1 dq1 dl1 v1 l1 ∗
                  csSorted cs2_ptr cs2 dq2 dl2 v2 l2)))
    $$ [i cs cs1 Hv1 Hl1 cs2 Hv2 Hl2]
  · iexists W64 0, zero_val Loc
    iframe i cs
    ileft
    iframe
    ipureintro; rfl
  wp_for IH
  wp_if_destruct
  · icases Hst with (⟨%Hn, cs1, Hv1, Hl1, cs2, Hv2, Hl2⟩ | ⟨%Hn, Hd1, cs2, Hv2, Hl2⟩ | ⟨%Hn, -, -⟩)
    · -- `cs = &cs1`
      have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 2) := ⟨by rw [Hn]; decide, Hif⟩
      simp only [Hbnd', _root_.and_self]
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ cs1_ptr Hbnd'.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro; rw [Hn]; rfl
      icases typedPointsto_not_null_dup _ _ _ $$ cs1 with ⟨cs1, %Hnn⟩
      iStructNamed cs1
      wp_apply (wp_sortCopy_owned wp_slices_Sort f hf.symm) _ _ v1 dq1 Hlen $$ [$Hv1 $Voters]
        as %sv %v1' ⟨Voters, Hv1, Hsv, -, %Hs1⟩
      wp_apply (wp_sortCopy_idlist wp_slices_Sort f hf.symm) _ _ l1 dl1 Hllen
        $$ [$Learners $Hl1] as %slv %l1' ⟨Learners, Hl1, Hslv, %Hsl1⟩
      wp_apply (wp_sortCopy_empty wp_slices_Sort f hf.symm) _ _ H1 $$ [$VotersOutgoing]
        as ⟨VotersOutgoing, -⟩
      wp_apply (wp_sortCopy_empty wp_slices_Sort f hf.symm) _ _ H3 $$ [$LearnersNext]
        as ⟨LearnersNext, -⟩
      wp_for_post
      iframe HΦ Hp s Hsl Hslcap orig1 orig2
      iexists n + W64 1, cs1_ptr
      simp only [named]
      iframe i cs
      iright; ileft
      isplitr
      · ipureintro; rw [Hn]; rfl
      iframe cs2 Hv2 Hl2
      unfold csSorted
      iexists ({ Voters' := sv, Learners' := slv, VotersOutgoing' := slice.nil, LearnersNext' := slice.nil, AutoLeave' := cs1.AutoLeave' } : raftpb.ConfState), v1', l1'
      simp only [named]
      iframe Hv1 Hl1 Hsv Hslv
      isplitl [Voters Learners VotersOutgoing LearnersNext AutoLeave]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
        try itrivial
      ipureintro
      exact ⟨trivial, trivial, trivial, Hs1.1, Hs1.2.1, Hs1.2.2, Hsl1.1, Hsl1.2.1, Hsl1.2.2⟩
    · -- `cs = &cs2`
      have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 2) := ⟨by rw [Hn]; decide, Hif⟩
      simp only [Hbnd', _root_.and_self]
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ cs2_ptr Hbnd'.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro; rw [Hn]; rfl
      icases typedPointsto_not_null_dup _ _ _ $$ cs2 with ⟨cs2, %Hnn⟩
      iStructNamed cs2
      wp_apply (wp_sortCopy_owned wp_slices_Sort f hf.symm) _ _ v2 dq2 (by rw [← Hperm.length_eq]; exact Hlen) $$ [$Hv2 $Voters]
        as %sv %v2' ⟨Voters, Hv2, Hsv, -, %Hs1⟩
      wp_apply (wp_sortCopy_idlist wp_slices_Sort f hf.symm) _ _ l2 dl2
          (by rw [← Hlperm.length_eq]; exact Hllen)
        $$ [$Learners $Hl2] as %slv %l2' ⟨Learners, Hl2, Hslv, %Hsl1⟩
      wp_apply (wp_sortCopy_empty wp_slices_Sort f hf.symm) _ _ H4 $$ [$VotersOutgoing]
        as ⟨VotersOutgoing, -⟩
      wp_apply (wp_sortCopy_empty wp_slices_Sort f hf.symm) _ _ H6 $$ [$LearnersNext]
        as ⟨LearnersNext, -⟩
      wp_for_post
      iframe HΦ Hp s Hsl Hslcap orig1 orig2
      iexists n + W64 1, cs2_ptr
      simp only [named]
      iframe i cs
      iright; iright
      isplitr
      · ipureintro; rw [Hn]; rfl
      iframe Hd1
      unfold csSorted
      iexists ({ Voters' := sv, Learners' := slv, VotersOutgoing' := slice.nil, LearnersNext' := slice.nil, AutoLeave' := cs2.AutoLeave' } : raftpb.ConfState), v2', l2'
      simp only [named]
      iframe Hv2 Hl2 Hsv Hslv
      isplitl [Voters Learners VotersOutgoing LearnersNext AutoLeave]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
        try itrivial
      ipureintro
      exact ⟨trivial, trivial, trivial, Hs1.1, Hs1.2.1, Hs1.2.2, Hsl1.1, Hsl1.2.1, Hsl1.2.2⟩
    · exfalso; rw [Hn] at Hif; exact absurd Hif (by decide)
  · -- both sorted: `reflect.DeepEqual(cs1, cs2)` holds
    icases Hst with (⟨%Hn, -, -, -, -, -, -⟩ | ⟨%Hn, -, -, -, -⟩ | ⟨%Hn, Hd1, Hd2⟩)
    · exfalso; rw [Hn] at Hif; exact Hif (by decide)
    · exfalso; rw [Hn] at Hif; exact Hif (by decide)
    unfold csSorted
    icases Hd1 with ⟨%cs1', %v1', %l1', Hc1, Hv1, Hl1, Hsv1, Hsl1, %Hf1⟩
    icases Hd2 with ⟨%cs2', %v2', %l2', Hc2, Hv2, Hl2, Hsv2, Hsl2, %Hf2⟩
    obtain ⟨Hvo1, Hln1, Hal1, Hp1, Hso1, Hnil1, Hlp1, Hlso1, Hlnil1⟩ := Hf1
    obtain ⟨Hvo2, Hln2, Hal2, Hp2, Hso2, Hnil2, Hlp2, Hlso2, Hlnil2⟩ := Hf2
    wp_auto
    ihave Hn2 : (cs1'.VotersOutgoing' ↦* ([] : List w64)) $$ []
    · rw [Hvo1]; iapply ownSlice_nil
    ihave Hn3 : (cs1'.LearnersNext' ↦* ([] : List w64)) $$ []
    · rw [Hln1]; iapply ownSlice_nil
    ihave Hn5 : (cs2'.VotersOutgoing' ↦* ([] : List w64)) $$ []
    · rw [Hvo2]; iapply ownSlice_nil
    ihave Hn6 : (cs2'.LearnersNext' ↦* ([] : List w64)) $$ []
    · rw [Hln2]; iapply ownSlice_nil
    wp_apply wp_reflect_DeepEqual cs1' cs2' v1' l1' [] [] v2' l2' [] []
      $$ [$Hsv1 $Hsl1 $Hn2 $Hn3 $Hsv2 $Hsl2 $Hn5 $Hn6] as ⟨Hsv1, -, -, -, Hsv2, -, -, -⟩
    have Heq : v1' = v2' :=
      sorted_perm_eq _ _ (Hp1.symm.trans (Hperm.trans Hp2))
        ((sortedW64_iff_pairwise _).1 Hso1) ((sortedW64_iff_pairwise _).1 Hso2)
    have Hleq : l1' = l2' :=
      sorted_perm_eq _ _ (Hlp1.symm.trans (Hlperm.trans Hlp2))
        ((sortedW64_iff_pairwise _).1 Hlso1) ((sortedW64_iff_pairwise _).1 Hlso2)
    have HP : confStateDeepEq cs1' cs2' v1' l1' [] [] v2' l2' [] [] := by
      refine ⟨?_, Heq, ?_, Hleq, by rw [Hvo1, Hvo2], rfl, by rw [Hln1, Hln2], rfl,
        by rw [Hal1, Hal2, Hal]⟩
      · rw [Hnil1, Hnil2]
        constructor
        · intro h; exact List.Perm.eq_nil (Hperm.symm.trans (List.Perm.of_eq h)) ▸ rfl
        · intro h; exact List.Perm.eq_nil (Hperm.trans (List.Perm.of_eq h)) ▸ rfl
      · rw [Hlnil1, Hlnil2]
        constructor
        · intro h; exact List.Perm.eq_nil (Hlperm.symm.trans (List.Perm.of_eq h)) ▸ rfl
        · intro h; exact List.Perm.eq_nil (Hlperm.trans (List.Perm.of_eq h)) ▸ rfl
    rw [decide_eq_true HP]
    wp_auto
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
