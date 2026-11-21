/-
`typed.getAssociativeKeyDefault`: proved (Prove phase, 2026-11-21): the element type resolves to the
map type (`S.find`); `FindField`'s field (or the zero field on a miss) has a nil `Default` (`isStructField_elim`).

Callees without a spec file here (other packages', the standard library's, or the
walker's own interface calls through a bundle): `errors.New`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.getAssociativeKeyDefault
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

theorem typed.getAssociativeKeyDefault.wp_proof
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (h_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF)) :
    typed.getAssociativeKeyDefault.spec (GF := GF) :=
    fun sc S lp e rel ks fs el r n => by
  wp_start as ⟨#HS, #Hl, %Hpre⟩
  obtain ⟨HWF, Hfind⟩ := Hpre
  have Hnd := Schema.WF_types_nodup_law_holds S HWF
  have Hfnd := Schema.WF_fields_nodup_law_holds S e.name fs el r HWF Hfind
  icases isListRep_elim_law_holds lp e rel ks $$ Hl with ⟨%lv, %ksl, #Hlv, %Hlv', #Hks, #Het⟩
  ihave #Het' := (isTypeRefOpt_some_law_holds _ e).2 $$ Het
  ihave ⟨Hlv2, %Hlnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hlv
  iStructNamed Hlv2
  wp_auto
  wp_apply h_Schema_Resolve sc S lv.ElementType' (some e) $$ [] as %a %ok ⟨%Hok, #Ha⟩
  · iframe #; ipureintro; exact Hnd
  simp only [Schema.resolveRef, Schema.resolvesRef, Schema.resolves, Hfind, Option.isSome_some] at Hok ⊢
  subst Hok
  icases (isAtomOpt_map_law_holds a fs el r).1 $$ Ha with ⟨%Hptr, #Hm⟩
  ihave %Hnn := isMapRep_nonnull_law_holds _ fs el r $$ Hm
  wp_auto
  simp only [decide_eq_false Hnn]
  wp_auto
  wp_apply h_Map_FindField a.Map' fs el r n $$ [] as %sf %ok2 Hsf
  · iframe #; ipureintro; exact Hfnd
  try wp_auto
  rcases hlk : lookupKV n fs with _ | t
  · icases Hsf with %Hsf
    obtain ⟨-, rfl⟩ := Hsf
    iapply HΦ; ipureintro; trivial
  · icases Hsf with ⟨%-, Hsf⟩
    icases (isStructField_elim_law_holds sf (n, t)).1 $$ Hsf with ⟨%Hd, -⟩
    rw [Hd.2]
    iapply HΦ; ipureintro; trivial

end proof

end smd
end EtcdGrove
end Perennial
