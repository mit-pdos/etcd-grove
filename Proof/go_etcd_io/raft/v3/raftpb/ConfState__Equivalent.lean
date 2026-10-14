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

/-- A slice `sl'` is a fresh sorted copy of the list `l`, `nil` iff `l` is empty. -/
def SortedCopy (l l' : List w64) (sl' : GoSlice) : Prop :=
  l ≡ₚ l' ∧ SortedW64 l' ∧ (sl' = slice.nil ↔ l = [])

/-- Two sorted copies of permutations of each other agree: the same list, and both `nil` or
neither. -/
theorem SortedCopy.agree {l1 l2 l1' l2' : List w64} {s1 s2 : GoSlice} (Hp : l1 ≡ₚ l2)
    (H1 : SortedCopy l1 l1' s1) (H2 : SortedCopy l2 l2' s2) :
    (s1 = slice.nil ↔ s2 = slice.nil) ∧ l1' = l2' := by
  obtain ⟨Hp1, Hs1, Hn1⟩ := H1
  obtain ⟨Hp2, Hs2, Hn2⟩ := H2
  refine ⟨?_, sorted_perm_eq _ _ (Hp1.symm.trans (Hp.trans Hp2))
    ((sortedW64_iff_pairwise _).1 Hs1) ((sortedW64_iff_pairwise _).1 Hs2)⟩
  rw [Hn1, Hn2]
  constructor
  · intro h; exact List.Perm.eq_nil (Hp.symm.trans (List.Perm.of_eq h)) ▸ rfl
  · intro h; exact List.Perm.eq_nil (Hp.trans (List.Perm.of_eq h)) ▸ rfl

/-- One `ConfState` after the loop: its four id slices replaced by fresh sorted copies (the
empty ones by `nil`), the original slices untouched. -/
def csSorted (c : Loc) (cs : raftpb.ConfState) (dq dl : DFrac) (a : CSLists) : IProp GF :=
  iprop(∃ (cs' : raftpb.ConfState) (a' : CSLists),
    "Hc" ∷ c ↦ cs' ∗
    "Hids" ∷ ownCSIds cs dq dl a ∗
    "Hsv" ∷ cs'.Voters' ↦* a'.voters ∗
    "Hsl" ∷ cs'.Learners' ↦* a'.learners ∗
    "Hso" ∷ cs'.VotersOutgoing' ↦* a'.outgoing ∗
    "Hsn" ∷ cs'.LearnersNext' ↦* a'.learnersNext ∗
    "%Hfacts" ∷ ⌜cs'.AutoLeave' = cs.AutoLeave' ∧
      SortedCopy a.voters a'.voters cs'.Voters' ∧
      SortedCopy a.learners a'.learners cs'.Learners' ∧
      SortedCopy a.outgoing a'.outgoing cs'.VotersOutgoing' ∧
      SortedCopy a.learnersNext a'.learnersNext cs'.LearnersNext'⌝)

theorem raftpb.ConfState.Equivalent.wp_proof
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG))
    (wp_reflect_DeepEqual : reflect.DeepEqual.spec (GF := GF) (hG := hG)) :
    raftpb.ConfState.Equivalent.spec (GF := GF) (hG := hG) := by
  intro p cs1 cs2 a b dq1 dq2 dl1 dl2 Hperm Hb Hal
  have Hb2 : b.Bounded := by
    obtain ⟨h1, h2, h3, h4⟩ := Hb
    obtain ⟨p1, p2, p3, p4⟩ := Hperm
    exact ⟨p1.length_eq ▸ h1, p2.length_eq ▸ h2, p3.length_eq ▸ h3, p4.length_eq ▸ h4⟩
  wp_start as ⟨Hp, Hc1, Hc2⟩
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
      "Hst" ∷ ((⌜n = W64 0⌝ ∗ cs1_ptr ↦ cs1 ∗ ownCSIds cs1 dq1 dl1 a ∗
                  cs2_ptr ↦ cs2 ∗ ownCSIds cs2 dq2 dl2 b) ∨
               (⌜n = W64 1⌝ ∗ csSorted cs1_ptr cs1 dq1 dl1 a ∗ cs2_ptr ↦ cs2 ∗
                  ownCSIds cs2 dq2 dl2 b) ∨
               (⌜n = W64 2⌝ ∗ csSorted cs1_ptr cs1 dq1 dl1 a ∗
                  csSorted cs2_ptr cs2 dq2 dl2 b)))
    $$ [i cs cs1 Hc1 cs2 Hc2]
  · iexists W64 0, zero_val Loc
    iframe i cs
    ileft
    iframe
    ipureintro; rfl
  wp_for IH
  wp_if_destruct
  · icases Hst with (⟨%Hn, cs1, Hc1, cs2, Hc2⟩ | ⟨%Hn, Hd1, cs2, Hc2⟩ | ⟨%Hn, -, -⟩)
    · -- `cs = &cs1`
      have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 2) := ⟨by rw [Hn]; decide, Hif⟩
      simp only [Hbnd', _root_.and_self]
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ cs1_ptr Hbnd'.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro; rw [Hn]; rfl
      icases typedPointsto_not_null_dup _ _ _ $$ cs1 with ⟨cs1, %Hnn⟩
      iStructNamed cs1
      unfold ownCSIds
      icases Hc1 with ⟨Hv, Hl, Ho, Hn⟩
      wp_apply (wp_sortCopy_owned wp_slices_Sort f hf.symm) _ _ a.voters dq1 Hb.1
        $$ [$Hv $Voters] as %sv %v' ⟨Voters, Hv, Hsv, -, %Hs1⟩
      wp_apply (wp_sortCopy_idlist wp_slices_Sort f hf.symm) _ _ a.learners dl1 Hb.2.1
        $$ [$Learners $Hl] as %slv %l' ⟨Learners, Hl, Hslv, %Hs2⟩
      wp_apply (wp_sortCopy_idlist wp_slices_Sort f hf.symm) _ _ a.outgoing dl1 Hb.2.2.1
        $$ [$VotersOutgoing $Ho] as %sov %o' ⟨VotersOutgoing, Ho, Hsov, %Hs3⟩
      wp_apply (wp_sortCopy_idlist wp_slices_Sort f hf.symm) _ _ a.learnersNext dl1 Hb.2.2.2
        $$ [$LearnersNext $Hn] as %snv %n' ⟨LearnersNext, Hn, Hsnv, %Hs4⟩
      ihave Hd1 : csSorted cs1_ptr cs1 dq1 dl1 a $$ [Voters Learners VotersOutgoing
          LearnersNext AutoLeave Hv Hl Ho Hn Hsv Hslv Hsov Hsnv]
      · unfold csSorted
        iexists ({ Voters' := sv, Learners' := slv, VotersOutgoing' := sov, LearnersNext' := snv, AutoLeave' := cs1.AutoLeave' } : raftpb.ConfState), (⟨v', l', o', n'⟩ : CSLists)
        simp only [named]
        iframe Hsv Hslv Hsov Hsnv
        isplitl [Voters Learners VotersOutgoing LearnersNext AutoLeave]
        · iapply typedPointsto_combine _ _ _ Hnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
          try itrivial
        isplitl [Hv Hl Ho Hn]
        · unfold ownCSIds; iframe
        ipureintro
        exact ⟨trivial, Hs1, Hs2, Hs3, Hs4⟩
      wp_for_post
      iframe HΦ Hp s Hsl Hslcap orig1 orig2
      iexists n + W64 1, cs1_ptr
      simp only [named]
      iframe i cs
      iright; ileft
      isplitr
      · ipureintro; rw [Hn]; rfl
      iframe
    · -- `cs = &cs2`
      have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 2) := ⟨by rw [Hn]; decide, Hif⟩
      simp only [Hbnd', _root_.and_self]
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ cs2_ptr Hbnd'.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro; rw [Hn]; rfl
      icases typedPointsto_not_null_dup _ _ _ $$ cs2 with ⟨cs2, %Hnn⟩
      iStructNamed cs2
      unfold ownCSIds
      icases Hc2 with ⟨Hv, Hl, Ho, Hn⟩
      wp_apply (wp_sortCopy_owned wp_slices_Sort f hf.symm) _ _ b.voters dq2 Hb2.1
        $$ [$Hv $Voters] as %sv %v' ⟨Voters, Hv, Hsv, -, %Hs1⟩
      wp_apply (wp_sortCopy_idlist wp_slices_Sort f hf.symm) _ _ b.learners dl2 Hb2.2.1
        $$ [$Learners $Hl] as %slv %l' ⟨Learners, Hl, Hslv, %Hs2⟩
      wp_apply (wp_sortCopy_idlist wp_slices_Sort f hf.symm) _ _ b.outgoing dl2 Hb2.2.2.1
        $$ [$VotersOutgoing $Ho] as %sov %o' ⟨VotersOutgoing, Ho, Hsov, %Hs3⟩
      wp_apply (wp_sortCopy_idlist wp_slices_Sort f hf.symm) _ _ b.learnersNext dl2 Hb2.2.2.2
        $$ [$LearnersNext $Hn] as %snv %n' ⟨LearnersNext, Hn, Hsnv, %Hs4⟩
      ihave Hd2 : csSorted cs2_ptr cs2 dq2 dl2 b $$ [Voters Learners VotersOutgoing
          LearnersNext AutoLeave Hv Hl Ho Hn Hsv Hslv Hsov Hsnv]
      · unfold csSorted
        iexists ({ Voters' := sv, Learners' := slv, VotersOutgoing' := sov, LearnersNext' := snv, AutoLeave' := cs2.AutoLeave' } : raftpb.ConfState), (⟨v', l', o', n'⟩ : CSLists)
        simp only [named]
        iframe Hsv Hslv Hsov Hsnv
        isplitl [Voters Learners VotersOutgoing LearnersNext AutoLeave]
        · iapply typedPointsto_combine _ _ _ Hnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
          try itrivial
        isplitl [Hv Hl Ho Hn]
        · unfold ownCSIds; iframe
        ipureintro
        exact ⟨trivial, Hs1, Hs2, Hs3, Hs4⟩
      wp_for_post
      iframe HΦ Hp s Hsl Hslcap orig1 orig2
      iexists n + W64 1, cs2_ptr
      simp only [named]
      iframe i cs
      iright; iright
      isplitr
      · ipureintro; rw [Hn]; rfl
      iframe
    · exfalso; rw [Hn] at Hif; exact absurd Hif (by decide)
  · -- both sorted: `reflect.DeepEqual(cs1, cs2)` holds
    icases Hst with (⟨%Hn, -, -, -, -⟩ | ⟨%Hn, -, -, -⟩ | ⟨%Hn, Hd1, Hd2⟩)
    · exfalso; rw [Hn] at Hif; exact Hif (by decide)
    · exfalso; rw [Hn] at Hif; exact Hif (by decide)
    unfold csSorted
    icases Hd1 with ⟨%cs1', %a', Hc1, Hids1, Hsv1, Hsl1, Hso1, Hsn1, %Hf1⟩
    icases Hd2 with ⟨%cs2', %b', Hc2, Hids2, Hsv2, Hsl2, Hso2, Hsn2, %Hf2⟩
    obtain ⟨Hal1, Hv1, Hl1, Ho1, Hn1⟩ := Hf1
    obtain ⟨Hal2, Hv2, Hl2, Ho2, Hn2⟩ := Hf2
    obtain ⟨Hpv, Hpl, Hpo, Hpn⟩ := Hperm
    wp_auto
    wp_apply wp_reflect_DeepEqual cs1' cs2' a'.voters a'.learners a'.outgoing a'.learnersNext
        b'.voters b'.learners b'.outgoing b'.learnersNext
      $$ [$Hsv1 $Hsl1 $Hso1 $Hsn1 $Hsv2 $Hsl2 $Hso2 $Hsn2] as -
    obtain ⟨Ev1, Ev2⟩ := SortedCopy.agree Hpv Hv1 Hv2
    obtain ⟨El1, El2⟩ := SortedCopy.agree Hpl Hl1 Hl2
    obtain ⟨Eo1, Eo2⟩ := SortedCopy.agree Hpo Ho1 Ho2
    obtain ⟨En1, En2⟩ := SortedCopy.agree Hpn Hn1 Hn2
    have HP : confStateDeepEq cs1' cs2' a'.voters a'.learners a'.outgoing a'.learnersNext
        b'.voters b'.learners b'.outgoing b'.learnersNext :=
      ⟨Ev1, Ev2, El1, El2, Eo1, Eo2, En1, En2, by rw [Hal1, Hal2, Hal]⟩
    rw [decide_eq_true HP]
    wp_auto
    iapply HΦ
    iframe

end proof
end EtcdGrove
end Perennial
