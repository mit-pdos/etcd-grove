/-
`fieldpath.ManagedFields.Equals`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.ManagedFields__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__APIVersion
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Applied
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsIter
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep

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
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.ManagedFields.Equals.wp_proof
    (h_Set_Equals : fieldpath.Set.Equals.spec (GF := GF))
    (h_versionedSet_APIVersion : fieldpath.versionedSet.APIVersion.spec (GF := GF))
    (h_versionedSet_Applied : fieldpath.versionedSet.Applied.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF)) :
    fieldpath.ManagedFields.Equals.spec (GF := GF) := fun m1 m2 a b => by
  wp_start as ⟨#Ha, #Hb⟩
  unfold isMF
  icases Ha with ⟨%Ma, #Hma, %ha, #Hla⟩
  icases Hb with ⟨%Mb, #Hmb, %hb, #Hlb⟩
  have sa := fpD.keysSorted_pairwise a ha.1
  have sb := fpD.keysSorted_pairwise b hb.1
  have za := fpD.size_eq Ma a sa ha.2
  have zb := fpD.size_eq Mb b sb hb.2
  wp_auto
  wp_apply (wp_map_len_lt m1 Ma DFrac.discard) $$ [$Hma] as ⟨-, %hla⟩
  wp_apply (wp_map_len_lt m2 Mb DFrac.discard) $$ [$Hmb] as ⟨-, %hlb⟩
  wp_if_destruct
  rotate_left
  · wp_end
    ipureintro
    simp only [Bool.false_eq_true, false_iff]
    rintro rfl
    exact Hif (by rw [za, zb])
  have hlen : a.length = b.length := by
    have : Ma.size = Mb.size := by word
    omega
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoInterface)
    (fun keys i => iprop((∀ r, ⌜r = true ↔ a = b⌝ -∗ Φ #r) ∗ «$res0_ptr» ↦ false ∗
      rhs_ptr ↦ m2 ∗ (∃ lv : GoInterface, left_ptr ↦ lv) ∗ (∃ mv : GoString, manager_ptr ↦ mv) ∗
      ⌜0 ≤ i ∧ ∀ j : Nat, (j : Int) < i → ∀ k, keys[j]? = some k → a.get k = b.get k⌝))
    _ go.string fieldpath.VersionedSet.ty m1 Ma DFrac.discard) $$ Hma
  iintro %keys %hkeys
  isplitl
  · iframe HΦ rhs
    isplitl [«$res0»]
    · iexact «$res0»
    isplitl [left]
    · iexists _; iexact left
    isplitl [manager]
    · iexists _; iexact manager
    ipureintro; exact ⟨Int.le_refl _, fun j hj => by omega⟩
  isplitr
  · iintro !> %i %key %v %hkv ⟨HΦ, Hres, Hrhs, ⟨%lv, Hl⟩, ⟨%mv, Hm⟩, %hi⟩
    obtain ⟨ea, hea⟩ : ∃ ea, a.get key = some ea := by
      have := ha.2 key; rw [hkv.2] at this
      exact Option.isSome_iff_exists.1 this.symm
    ihave ⟨%i', %hi', #Hva⟩ := fpD.isMFL_lookup Ma a key ea sa hea $$ Hla
    rw [hkv.2] at hi'; cases hi'
    unfold isVSet
    icases Hva with ⟨%pa, %hva, #Hsa⟩
    subst hva
    wp_auto
    cases hbk : b.get key with
    | none =>
      have hMb : Mb !! key = none := by
        have := hb.2 key; rw [hbk] at this; simpa using this
      wp_apply (wp_map_lookup2 go.string fieldpath.VersionedSet.ty m2 Mb key DFrac.discard) $$ [$Hmb] as _
      rw [hMb]
      wp_auto
      unfold forMapPostcondition
      iright; iright; iright
      iexists #()
      isplitr
      · ipureintro; rfl
      iintro _
      wp_auto
      iapply HΦ
      ipureintro
      simp only [Bool.false_eq_true, false_iff]
      rintro rfl; rw [hea] at hbk; cases hbk
    | some eb =>
      ihave ⟨%i'', %hi'', #Hvb⟩ := fpD.isMFL_lookup Mb b key eb sb hbk $$ Hlb
      unfold isVSet
      icases Hvb with ⟨%pb, %hvb, #Hsb⟩
      subst hvb
      wp_apply (wp_map_lookup2 go.string fieldpath.VersionedSet.ty m2 Mb key DFrac.discard) $$ [$Hmb] as _
      rw [hi'']
      simp only [Option.isSome_some, Option.getD_some]
      wp_auto
      ihave #Va := fpD.isVSet_mk pa ea $$ Hsa
      ihave #Vb := fpD.isVSet_mk pb eb $$ Hsb
      wp_apply (h_versionedSet_APIVersion _ ea) $$ [$Va] as %r1 %hr1
      wp_apply (h_versionedSet_APIVersion _ eb) $$ [$Vb] as %r2 %hr2
      subst hr1 hr2
      wp_if_destruct
      rotate_left
      · skip
        unfold forMapPostcondition
        iright; iright; iright
        iexists #()
        isplitr
        · ipureintro; rfl
        iintro _
        wp_auto
        iapply HΦ
        ipureintro
        simp only [Bool.false_eq_true, false_iff]
        rintro rfl
        rw [hea] at hbk; cases hbk
        exact Hif rfl
      wp_apply (h_versionedSet_Applied _ ea) $$ [$Va] as %r1 %hr1
      wp_apply (h_versionedSet_Applied _ eb) $$ [$Vb] as %r2 %hr2
      subst hr1 hr2
      wp_if_destruct
      rotate_left
      · skip
        unfold forMapPostcondition
        iright; iright; iright
        iexists #()
        isplitr
        · ipureintro; rfl
        iintro _
        wp_auto
        iapply HΦ
        ipureintro
        simp only [Bool.false_eq_true, false_iff]
        rintro rfl
        rw [hea] at hbk; cases hbk
        exact Hif rfl
      wp_apply (h_versionedSet_Set _ eb) $$ [$Vb] as %q2 #Hq2
      wp_apply (h_versionedSet_Set _ ea) $$ [$Va] as %q1 #Hq1
      wp_apply (h_Set_Equals q1 q2 ea.set eb.set) $$ [$Hq1 $Hq2] as %r %hr
      cases r
      · wp_auto
        unfold forMapPostcondition
        iright; iright; iright
        iexists #()
        isplitr
        · ipureintro; rfl
        iintro _
        wp_auto
        iapply HΦ
        ipureintro
        simp only [Bool.false_eq_true, false_iff]
        rintro rfl
        rw [hea] at hbk; cases hbk
        exact absurd (hr.2 rfl) (by simp)
      wp_auto
      rename_i hver
      have heq : ea = eb := by
        have hs := hr.1 rfl
        cases ea; cases eb; simp_all
      subst heq
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iframe HΦ Hres Hrhs
      isplitl [Hl]
      · iexists _; iexact Hl
      isplitl [Hm]
      · iexists _; iexact Hm
      ipureintro
      refine ⟨by omega, fun j hj k hk => ?_⟩
      by_cases hji : (j : Int) < i
      · exact hi.2 j hji k hk
      · have : j = i.toNat := by omega
        subst this
        rw [hkv.1] at hk; cases hk
        rw [hea, hbk]
  · iintro ⟨HΦ, Hres, Hrhs, -, -, %hi⟩ _
    wp_auto
    iapply HΦ
    ipureintro
    simp only [true_iff]
    apply fpD.mf_eq_of_sub a b ha.1 hb.1 hlen
    intro k e he
    have hk : k ∈ keys := (hkeys.1 k).2 (by rw [ha.2 k, he]; rfl)
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hk
    have hjl := (List.getElem?_eq_some_iff.1 hj).1
    rw [← hi.2 j (by omega) k hj]; exact he

end proof

end smd
end EtcdGrove
end Perennial
