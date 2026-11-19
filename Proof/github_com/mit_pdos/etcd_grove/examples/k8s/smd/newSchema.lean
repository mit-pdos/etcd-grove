/-
`newSchema` (`examples/k8s/smd/smd.go`). Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.newSchema

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open smd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

open sigs_k8s_io.structured_merge_diff.v7

/-- A `TypeRef{NamedType: p}`. -/
abbrev tr (p : Loc) : sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef :=
  sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef.mk p zeroValDef null false

/-- A fresh `*schema.Map` literal (no unions, zero index) owns its model, its index not built. -/
theorem ownMapT_fresh (p : Loc) (fsl : GoSlice) (sfs : List schema.StructField)
    (etv : schema.TypeRef) (er : GoString) (fs : Fields) (et : TypeRef)
    (hfs : sfs = [] → fsl = slice.nil) :
    p ↦ schema.Map.mk fsl slice.nil etv er zeroValDef zeroValDef ∗ fsl ↦*{DFrac.discard} sfs ∗
      ownTypeRef (GF := GF) true etv et ∗ ownSFields true sfs fs ⊢ |==> ownMapT true p (.mk fs et er) := by
  iintro ⟨Hp, #Hfs, Het, Hsf⟩
  iStructNamed Hp
  ipersist Fields
  ipersist Unions
  ipersist ElementType
  ipersist ElementRelationship
  imodintro
  unfold ownMapT
  iexists fsl, sfs, slice.nil, etv
  simp only [ite_true, ownLazyIndex]
  iframe Fields Hfs Unions ElementType ElementRelationship Het Hsf
  isplitr
  · ipureintro; exact hfs
  ileft
  iframe

/-- A `TypeRef{NamedType: p}` of a pointer to the type's name. -/
theorem ownTypeRef_named (c : Bool) (p : Loc) (n : GoString) :
    p ↦□ n ⊢ ownTypeRef (GF := GF) c (tr p) (named n) := by
  iintro #Hp
  simp only [named, zeroAtom, ownTypeRef, ownStrPtr, ownAtom, ownOptList, ownOptMap, tr]
  iframe Hp
  ipureintro
  simp [zeroValDef]

/-- A fresh `*schema.List` literal owns its model. -/
theorem ownListT_fresh (c : Bool) (p : Loc) (etv : schema.TypeRef) (er : GoString) (ksl : GoSlice)
    (ks : List GoString) (et : TypeRef) :
    p ↦ schema.List'.mk etv er ksl ∗ ksl ↦*{DFrac.discard} ks ∗ ownTypeRef (GF := GF) c etv et ⊢
      |==> ownListT c p (.mk et er ks) := by
  iintro ⟨Hp, #Hks, Het⟩
  ipersist Hp
  imodintro
  unfold ownListT
  iexists schema.List'.mk etv er ksl
  iframe Hp Hks Het
  ipureintro; rfl

theorem ownTypeRef_zero (c : Bool) :
    ⊢ ownTypeRef (GF := GF) c (zeroValDef : schema.TypeRef) zeroRef := by
  simp only [zeroRef, zeroAtom, ownTypeRef, ownStrPtr, ownAtom, ownOptList, ownOptMap]
  ipureintro
  simp [zeroValDef]

theorem ownSFields_nil (c : Bool) : ⊢ ownSFields (GF := GF) c [] .nil := by
  simp only [ownSFields]; itrivial

theorem ownSFields_named (c : Bool) (n : GoString) (p : Loc) (m : GoString)
    (rest : List schema.StructField) (restF : Fields) :
    p ↦□ m ∗ ownSFields (GF := GF) c rest restF ⊢
      ownSFields c (schema.StructField.mk n (tr p) interface.nil :: rest) (.cons (.mk n (named m)) restF) := by
  iintro ⟨#Hp, Hr⟩
  simp only [ownSFields]
  iframe Hr
  isplitr
  · ipureintro; simp
  iapply ownTypeRef_named $$ Hp

theorem ownAtom_scalar (p : Loc) (s : GoString) :
    p ↦□ s ⊢ ownAtom (GF := GF) true (schema.Atom.mk p null null) (.ofScalar s) := by
  iintro #Hp
  simp only [Atom.ofScalar, ownAtom, ownStrPtr, ownOptList, ownOptMap]
  iframe Hp
  ipureintro; simp

theorem ownAtom_map (p : Loc) (m : MapT) :
    ownMapT (GF := GF) true p m ⊢ ownAtom true (schema.Atom.mk null null p) (.ofMap m) := by
  iintro Hp
  simp only [Atom.ofMap, ownAtom, ownStrPtr, ownOptList, ownOptMap]
  iframe Hp

theorem ownAtom_list (p : Loc) (l : ListT) :
    ownListT (GF := GF) true p l ⊢ ownAtom true (schema.Atom.mk null p null) (.ofList l) := by
  iintro Hp
  simp only [Atom.ofList, ownAtom, ownStrPtr, ownOptList, ownOptMap]
  iframe Hp

/-- `ownMapT_fresh` with the fields' condition a pure premise. -/
theorem ownMapT_fresh' (p : Loc) (fsl : GoSlice) (sfs : List schema.StructField)
    (etv : schema.TypeRef) (er : GoString) (m : MapT) :
    p ↦ schema.Map.mk fsl slice.nil etv er zeroValDef zeroValDef ∗ fsl ↦*{DFrac.discard} sfs ∗
      ownTypeRef (GF := GF) true etv (match m with | .mk _ et _ => et) ∗
      ownSFields true sfs (match m with | .mk fs _ _ => fs) ∗
      ⌜(sfs = [] → fsl = slice.nil) ∧ ∃ fs et, m = .mk fs et er ∧ True⌝ ⊢ |==> ownMapT true p m := by
  iintro ⟨H1, H2, H3, H4, %h⟩
  obtain ⟨hfs, fs, et, rfl, -⟩ := h
  iapply ownMapT_fresh p fsl sfs etv er fs et hfs
  iframe

theorem rootFields_own (ps pn pcs pl psel : Loc) :
    ps ↦□ go!"string" ∗ pn ↦□ go!"numeric" ∗ pcs ↦□ go!"containers" ∗ pl ↦□ go!"labels" ∗
      psel ↦□ go!"selector" ⊢
    ownSFields (GF := GF) true
      [schema.StructField.mk go!"name" (tr ps) interface.nil,
       schema.StructField.mk go!"image" (tr ps) interface.nil,
       schema.StructField.mk go!"replicas" (tr pn) interface.nil,
       schema.StructField.mk go!"containers" (tr pcs) interface.nil,
       schema.StructField.mk go!"labels" (tr pl) interface.nil,
       schema.StructField.mk go!"selector" (tr psel) interface.nil]
      (Fields.ofList [fld go!"name" strRef, fld go!"image" strRef, fld go!"replicas" numRef,
        fld go!"containers" (named go!"containers"), fld go!"labels" (named go!"labels"),
        fld go!"selector" (named go!"selector")]) := by
  iintro ⟨#a, #b, #c, #d, #e⟩
  simp only [Fields.ofList, fld, strRef, numRef]
  iapply ownSFields_named; isplitr; · iexact a
  iapply ownSFields_named; isplitr; · iexact a
  iapply ownSFields_named; isplitr; · iexact b
  iapply ownSFields_named; isplitr; · iexact c
  iapply ownSFields_named; isplitr; · iexact d
  iapply ownSFields_named; isplitr; · iexact e
  iapply ownSFields_nil

theorem containerFields_own (ps pn : Loc) :
    ps ↦□ go!"string" ∗ pn ↦□ go!"numeric" ⊢
    ownSFields (GF := GF) true
      [schema.StructField.mk go!"name" (tr ps) interface.nil,
       schema.StructField.mk go!"image" (tr ps) interface.nil,
       schema.StructField.mk go!"port" (tr pn) interface.nil]
      (Fields.ofList [fld go!"name" strRef, fld go!"image" strRef, fld go!"port" numRef]) := by
  iintro ⟨#a, #b⟩
  simp only [Fields.ofList, fld, strRef, numRef]
  iapply ownSFields_named; isplitr; · iexact a
  iapply ownSFields_named; isplitr; · iexact a
  iapply ownSFields_named; isplitr; · iexact b
  iapply ownSFields_nil

theorem newSchema.wp_proof : newSchema.spec (GF := GF) := by
  wp_start as #Hpkg
  iapply wp_fupd
  wp_auto
  wp_apply (wp_slice_literal (V := schema.StructField)
    [schema.StructField.mk go!"name" (tr stringName_ptr) interface.nil,
     schema.StructField.mk go!"image" (tr stringName_ptr) interface.nil,
     schema.StructField.mk go!"replicas" (tr numericName_ptr) interface.nil,
     schema.StructField.mk go!"containers" (tr containersName_ptr) interface.nil,
     schema.StructField.mk go!"labels" (tr labelsName_ptr) interface.nil,
     schema.StructField.mk go!"selector" (tr selectorName_ptr) interface.nil])
  isplitr
  · ipureintro; rfl
  iintro %rootF ⟨HrootF, -⟩
  wp_auto
  wp_apply (wp_slice_literal (V := schema.StructField)
    [schema.StructField.mk go!"name" (tr stringName_ptr) interface.nil,
     schema.StructField.mk go!"image" (tr stringName_ptr) interface.nil,
     schema.StructField.mk go!"port" (tr numericName_ptr) interface.nil])
  isplitr
  · ipureintro; rfl
  iintro %contF ⟨HcontF, -⟩
  wp_auto
  wp_apply (wp_slice_literal (V := GoString) [go!"name"])
  isplitr
  · ipureintro; rfl
  iintro %keysS ⟨HkeysS, -⟩
  wp_auto
  rename_i rootM contM listL labM
  wp_apply (wp_slice_literal (V := schema.TypeDef)
    [schema.TypeDef.mk go!"root" (schema.Atom.mk null null rootM),
     schema.TypeDef.mk go!"container" (schema.Atom.mk null null contM),
     schema.TypeDef.mk go!"containers" (schema.Atom.mk null listL null),
     schema.TypeDef.mk go!"labels" (schema.Atom.mk null null labM),
     schema.TypeDef.mk go!"selector" (schema.Atom.mk null null «$v0_ptr»),
     schema.TypeDef.mk go!"string" (schema.Atom.mk str_ptr null null),
     schema.TypeDef.mk go!"numeric" (schema.Atom.mk num_ptr null null)])
  isplitr
  · ipureintro; rfl
  iintro %tys ⟨Htys, -⟩
  wp_auto
  irename: (typedPointsto rootM (_ : schema.Map) _) => HrootM
  irename: (typedPointsto contM (_ : schema.Map) _) => HcontM
  irename: (typedPointsto listL (_ : schema.List') _) => HlistL
  irename: (typedPointsto labM (_ : schema.Map) _) => HlabM
  irename «$v0» => HselM
  ipersist stringName
  ipersist numericName
  ipersist containerName
  ipersist labelsName
  ipersist selectorName
  ipersist containersName
  ipersist str
  ipersist num
  ipersist HrootF
  ipersist HcontF
  ipersist HkeysS
  ipersist Htys
  ihave #Hz := ownTypeRef_zero (GF := GF) true
  ihave #Hs := ownTypeRef_named (GF := GF) true stringName_ptr go!"string" $$ stringName
  ihave #Hc := ownTypeRef_named (GF := GF) true containerName_ptr go!"container" $$ containerName
  imod (ownMapT_fresh' rootM _ _ _ _ rootMapT) $$ [HrootM] with HrootO
  · simp only [rootMapT]
    iframe HrootM HrootF Hz
    isplitl
    · iapply rootFields_own
      iframe stringName numericName containersName labelsName selectorName
    ipureintro; exact ⟨(fun h => nomatch h), _, _, rfl, trivial⟩
  imod (ownMapT_fresh' contM _ _ _ _ containerMapT) $$ [HcontM] with HcontO
  · simp only [containerMapT]
    iframe HcontM HcontF Hz
    isplitl
    · iapply containerFields_own
      iframe stringName numericName
    ipureintro; exact ⟨(fun h => nomatch h), _, _, rfl, trivial⟩
  ihave #Hnil : (slice.nil ↦*{DFrac.discard} ([] : List schema.StructField) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave #Hsfn := ownSFields_nil (GF := GF) true
  imod (ownMapT_fresh' labM _ _ _ _ labelsMapT) $$ [HlabM] with HlabO
  · simp only [labelsMapT, strRef]
    iframe HlabM Hnil Hsfn Hs
    ipureintro; exact ⟨(fun _ => rfl), _, _, rfl, trivial⟩
  imod (ownMapT_fresh' «$v0_ptr» _ _ _ _ selectorMapT) $$ [HselM] with HselO
  · simp only [selectorMapT, strRef]
    iframe HselM Hnil Hsfn Hs
    ipureintro; exact ⟨(fun _ => rfl), _, _, rfl, trivial⟩
  imod (ownListT_fresh (GF := GF) true listL _ _ _ _ (named go!"container")) $$ [HlistL] with HlistO
  · iframe HlistL HkeysS Hc
  ihave HrootA := ownAtom_map rootM rootMapT $$ HrootO
  ihave HcontA := ownAtom_map contM containerMapT $$ HcontO
  ihave HlabA := ownAtom_map labM labelsMapT $$ HlabO
  ihave HselA := ownAtom_map «$v0_ptr» selectorMapT $$ HselO
  ihave HlistA := ownAtom_list listL _ $$ HlistO
  ihave #HstrA := ownAtom_scalar (GF := GF) str_ptr go!"string" $$ str
  ihave #HnumA := ownAtom_scalar (GF := GF) num_ptr go!"numeric" $$ num
  iStructNamed «$r0»
  ipersist Types
  imodintro
  iapply HΦ
  unfold ownSchema
  iexists _, _
  iframe Types Htys
  isplitl [HrootA HcontA HlabA HselA HlistA]
  · simp only [k8s_smd.sc, ownTypeDefs, containersListT]
    iframe HrootA HcontA HlabA HselA HlistA HstrA HnumA
  unfold ownLazyIndex
  iframe lock resolvedTypes
  ileft
  iframe once m

end proof

end k8s_smd
end EtcdGrove
end Perennial
