/-
`newSchema`: the scenario's schema literal, `freshSchema` of `sc0` from its pieces
(`isTypeRef_intro`, `freshAtom_*`, `freshSchema_intro`), then shared (`isSchema_intro`).
Lean-first (2026-11-19).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.newSchema
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws

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

/-- A named `TypeRef{NamedType: p}`. -/
theorem isTypeRef_tr (hTR : isTypeRef_intro.law (GF := GF)) (p : Loc) (n : GoString) :
    p ↦□ n ⊢ isTypeRef (GF := GF) (tr p) ⟨n, false⟩ := by
  iintro #Hp
  iapply (hTR (tr p) ⟨n, false⟩ rfl rfl rfl rfl rfl)
  iexact Hp

/-- A `schema.Map` literal (no unions, zero index), allocated, is a fresh map atom. -/
theorem freshAtom_mapLit (hMap : freshAtom_map.law (GF := GF)) (p : Loc) (fsl : GoSlice)
    (sfs : List schema.StructField) (fs : List (GoString × TypeRef)) (etv : schema.TypeRef)
    (e : Option TypeRef) (rel : ElemRel) (rn : GoString) (hrn : rn = rel.goName)
    (hlen : sfs.length = fs.length) (hdef : ∀ sf ∈ sfs, sf.Default' = interface.nil) :
    p ↦ schema.Map.mk fsl slice.nil etv rn zeroValDef zeroValDef -∗
    fsl ↦*{DFrac.discard} sfs -∗
    sepL (fun sf => iprop(⌜sf.1.Name' = sf.2.1⌝ ∗ isTypeRef (GF := GF) sf.1.Type' sf.2.2)) (sfs.zip fs) -∗
    (match e with
     | some t => isTypeRef etv t
     | none => iprop(⌜etv.NamedType' = null ∧ etv.Inlined'.Scalar' = null ∧
         etv.Inlined'.List' = null ∧ etv.Inlined'.Map' = null ∧
         etv.ElementRelationship' = null ∧ etv.Nullable' = false⌝)) -∗
    |==> freshAtom (schema.Atom.mk null null p) (.map fs e rel) := by
  subst hrn
  iintro Hp #Hfs Hsf He
  iStructNamed Hp
  ipersist Fields
  ipersist Unions
  ipersist ElementType
  ipersist ElementRelationship
  imodintro
  iapply (hMap (schema.Atom.mk null null p) fsl sfs fs etv e rel rfl rfl hlen hdef) $$ Fields Hfs Hsf
    Unions ElementType He ElementRelationship once m

theorem newSchema.wp_proof_of (hTR : isTypeRef_intro.law (GF := GF))
    (hScalar : freshAtom_scalar.law (GF := GF)) (hList : freshAtom_list.law (GF := GF))
    (hMap : freshAtom_map.law (GF := GF)) (hSchema : freshSchema_intro.law (GF := GF))
    (hShare : isSchema_intro.law (GF := GF)) : newSchema.spec (GF := GF) := by
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
  imod ownSlice_persist $$ HrootF with #HrootF
  imod ownSlice_persist $$ HcontF with #HcontF
  imod ownSlice_persist $$ HkeysS with #HkeysS
  imod ownSlice_persist $$ Htys with #Htys
  ihave #Hs := isTypeRef_tr hTR stringName_ptr _ $$ stringName
  ihave #Hn := isTypeRef_tr hTR numericName_ptr _ $$ numericName
  ihave #Hc := isTypeRef_tr hTR containerName_ptr _ $$ containerName
  ihave #Hcs := isTypeRef_tr hTR containersName_ptr _ $$ containersName
  ihave #Hl := isTypeRef_tr hTR labelsName_ptr _ $$ labelsName
  ihave #Hsel := isTypeRef_tr hTR selectorName_ptr _ $$ selectorName
  have hz : (zeroValDef : schema.TypeRef).NamedType' = null ∧
      (zeroValDef : schema.TypeRef).Inlined'.Scalar' = null ∧
      (zeroValDef : schema.TypeRef).Inlined'.List' = null ∧
      (zeroValDef : schema.TypeRef).Inlined'.Map' = null ∧
      (zeroValDef : schema.TypeRef).ElementRelationship' = null ∧
      (zeroValDef : schema.TypeRef).Nullable' = false := by
    simp [zeroValDef]
  imod (freshAtom_mapLit hMap rootM _ _
      [(go!"name", strRef), (go!"image", strRef), (go!"replicas", numRef),
       (go!"containers", ⟨go!"containers", false⟩), (go!"labels", ⟨go!"labels", false⟩),
       (go!"selector", ⟨go!"selector", false⟩)] _ none .unset go!"" rfl rfl (by simp)) $$ HrootM HrootF [] []
      with HrootA
  · simp only [sepL, List.zip_cons_cons, List.zip_nil_right, List.foldr_cons, List.foldr_nil,
      strRef, numRef]
    repeat' (first | itrivial | iexact Hs | iexact Hn | iexact Hcs | iexact Hl | iexact Hsel | isplitr)
  · ipureintro; exact hz
  imod (freshAtom_mapLit hMap contM _ _
      [(go!"name", strRef), (go!"image", strRef), (go!"port", numRef)] _ none .unset go!"" rfl rfl
      (by simp)) $$ HcontM HcontF [] []
      with HcontA
  · simp only [sepL, List.zip_cons_cons, List.zip_nil_right, List.foldr_cons, List.foldr_nil,
      strRef, numRef]
    repeat' (first | itrivial | iexact Hs | iexact Hn | iexact Hcs | iexact Hl | iexact Hsel | isplitr)
  · ipureintro; exact hz
  ihave #Hnil : (slice.nil ↦*{DFrac.discard} ([] : List schema.StructField) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod (freshAtom_mapLit hMap labM _ [] [] _ (some strRef) .separable go!"separable" rfl rfl
      (by simp)) $$ HlabM Hnil [] []
      with HlabA
  · simp only [sepL, List.zip_nil_left, List.foldr_nil]; itrivial
  · simp only [strRef]; iexact Hs
  imod (freshAtom_mapLit hMap «$v0_ptr» _ [] [] _ (some strRef) .atomic go!"atomic" rfl rfl
      (by simp)) $$ HselM Hnil [] []
      with HselA
  · simp only [sepL, List.zip_nil_left, List.foldr_nil]; itrivial
  · simp only [strRef]; iexact Hs
  ipersist HlistL
  ihave HlistA : freshAtom (schema.Atom.mk null listL null)
      (.list ⟨go!"container", false⟩ .associative [go!"name"]) $$ []
  · iapply (hList (schema.Atom.mk null listL null) _ _ _ .associative [go!"name"] rfl rfl rfl rfl)
      $$ HlistL HkeysS
    iexact Hc
  ihave HstrA : freshAtom (schema.Atom.mk str_ptr null null) (.scalar .string) $$ []
  · iapply (hScalar (schema.Atom.mk str_ptr null null) .string rfl rfl)
    simp only [Scalar.goName]
    iexact str
  ihave HnumA : freshAtom (schema.Atom.mk num_ptr null null) (.scalar .numeric) $$ []
  · iapply (hScalar (schema.Atom.mk num_ptr null null) .numeric rfl rfl)
    simp only [Scalar.goName]
    iexact num
  iStructNamed «$r0»
  ipersist Types
  ihave Hfresh := (hSchema «$r0_ptr» _ _ sc0 rfl) $$ Types Htys [HrootA HcontA HlistA HlabA HselA HstrA HnumA]
      once m
  · simp only [sc0, sepL, List.zip_cons_cons, List.zip_nil_right, List.foldr_cons, List.foldr_nil]
    iframe
  imod (hShare _ _) $$ Hfresh with Hsch
  imodintro
  iapply HΦ
  iexact Hsch

theorem newSchema.wp_proof : newSchema.spec (GF := GF) :=
  newSchema.wp_proof_of sorry sorry sorry sorry sorry sorry

end proof

end k8s_smd
end EtcdGrove
end Perennial
