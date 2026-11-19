/-
`schema.Atom.Equals`: a member of the recursion cluster `schema.EqualsRec` (`EqualsRec.lean`); its proof is the
projection of the cluster's (its body is `Atom__EqualsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Atom__EqualsBody
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
variable [package_sem : schema.Assumptions]

theorem schema.Atom.Equals.wp_proofBody :
    schema.Atom.Equals.specBody (GF := GF) := by
  unfold schema.Atom.Equals.specBody schema.EqualsRec.specI schema.Atom.Equals.specI
    schema.List.Equals.specI schema.Map.Equals.specI schema.StructField.Equals.specI
    schema.TypeRef.Equals.specI
  iintro #IH
  iintro %a %b %dq1 %dq2 %va %vb %oA %oB
  wp_start as ⟨Ha, #HoA, Hb, #HoB⟩
  ihave %Hane := typedPointsto_not_null $$ Ha
  ihave %Hbne := typedPointsto_not_null $$ Hb
  iStructNamedSuffix Ha "a"
  iStructNamedSuffix Hb "b"
  cases va with | mk sa la ma =>
  cases vb with | mk sb lb mb =>
  ihave ⟨%hsa, %hla, %hma⟩ := LawProofs.isAtomOpt_ptrs _ _ $$ HoA
  ihave ⟨%hsb, %hlb, %hmb⟩ := LawProofs.isAtomOpt_ptrs _ _ $$ HoB
  simp only at hsa hla hma hsb hlb hmb
  wp_auto
  wp_if_destruct
  all_goals try (exact (Hane rfl).elim)
  all_goals try wp_if_destruct
  all_goals try (exact (Hbne rfl).elim)
  -- the three nil comparisons: a mismatch is a different kind
  all_goals try wp_if_destruct
  all_goals try wp_if_destruct
  all_goals try wp_if_destruct
  all_goals first
    | (iapply HΦ
       isplitl [Scalara Lista Mapa]
       · iapply typedPointsto_combine _ _ _ Hane
         simp only [TypedPointsto.typedPointstoDef]
         iframe
       isplitl [Scalarb Listb Mapb]
       · iapply typedPointsto_combine _ _ _ Hbne
         simp only [TypedPointsto.typedPointstoDef]
         iframe
       ipureintro
       simp only [Bool.false_eq_true, false_iff]
       intro h; subst h
       apply Hif
       first | rw [decide_eq_decide, hsa, hsb] | rw [decide_eq_decide, hla, hlb] | rw [decide_eq_decide, hma, hmb]
       done)
    | skip
  rename_i hs hl hm
  rcases oA with _ | (s | ⟨e, rel, ks⟩ | ⟨fs, e, rel⟩) <;>
    rcases oB with _ | (s' | ⟨e', rel', ks'⟩ | ⟨fs', e', rel'⟩) <;>
    simp at hsa hla hma hsb hlb hmb <;>
    simp only [hsa, hla, hma, hsb, hlb, hmb, decide_true, decide_false] at hs hl hm <;>
    (try simp at hs hl hm)
  all_goals simp only [hsa, hla, hma, hsb, hlb, hmb, decide_true, decide_false, Bool.not_true,
    Bool.not_false]
  all_goals first
    | (wp_auto
       iapply HΦ
       isplitl [Scalara Lista Mapa]
       · iapply typedPointsto_combine _ _ _ Hane
         simp only [TypedPointsto.typedPointstoDef]
         iframe
       isplitl [Scalarb Listb Mapb]
       · iapply typedPointsto_combine _ _ _ Hbne
         simp only [TypedPointsto.typedPointstoDef]
         iframe
       ipureintro
       simp
       done)
    | (icases (isAtomOpt_scalar_law_holds _ _).1 $$ HoA with ⟨#Hsa, -⟩
       icases (isAtomOpt_scalar_law_holds _ _).1 $$ HoB with ⟨#Hsb, -⟩
       wp_auto
       iapply HΦ
       isplitl [Scalara Lista Mapa]
       · iapply typedPointsto_combine _ _ _ Hane
         simp only [TypedPointsto.typedPointstoDef]
         iframe
       isplitl [Scalarb Listb Mapb]
       · iapply typedPointsto_combine _ _ _ Hbne
         simp only [TypedPointsto.typedPointstoDef]
         iframe
       ipureintro
       simp only [decide_eq_true_eq, Option.some.injEq, Atom.scalar.injEq]
       constructor
       · intro h; revert h; cases s <;> cases s' <;> simp [Scalar.goName]
       · rintro rfl; rfl
       done)
    | (icases (isAtomOpt_list_law_holds _ _ _ _).1 $$ HoA with ⟨-, #Hla⟩
       icases (isAtomOpt_list_law_holds _ _ _ _).1 $$ HoB with ⟨-, #Hlb⟩
       ihave ⟨-, #HL, -⟩ := IH
       wp_apply HL $$ [] as %r %hr
       · iframe #
       iapply HΦ
       isplitl [Scalara Lista Mapa]
       · iapply typedPointsto_combine _ _ _ Hane
         simp only [TypedPointsto.typedPointstoDef]
         iframe
       isplitl [Scalarb Listb Mapb]
       · iapply typedPointsto_combine _ _ _ Hbne
         simp only [TypedPointsto.typedPointstoDef]
         iframe
       ipureintro
       simpa using hr
       done)
    | (icases (isAtomOpt_map_law_holds _ _ _ _).1 $$ HoA with ⟨-, #Hma⟩
       icases (isAtomOpt_map_law_holds _ _ _ _).1 $$ HoB with ⟨-, #Hmb⟩
       ihave ⟨-, -, #HM, -⟩ := IH
       wp_apply HM $$ [] as %r %hr
       · iframe #
       iapply HΦ
       isplitl [Scalara Lista Mapa]
       · iapply typedPointsto_combine _ _ _ Hane
         simp only [TypedPointsto.typedPointstoDef]
         iframe
       isplitl [Scalarb Listb Mapb]
       · iapply typedPointsto_combine _ _ _ Hbne
         simp only [TypedPointsto.typedPointstoDef]
         iframe
       ipureintro
       simpa using hr
       done)

end proof

end smd
end EtcdGrove
end Perennial
