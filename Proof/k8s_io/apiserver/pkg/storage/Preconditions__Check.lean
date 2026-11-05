/-
Lean-first (no Rocq counterpart). The proof of `(*storage.Preconditions).Check`: `nil`
preconditions return at once; otherwise `meta.Accessor` gives the object back as a
`metav1.Object` (`metaAt`'s type-set fact), and each set precondition is compared with the
object's `GetUID`/`GetResourceVersion` (`metaAt`'s methods), a mismatch formatted
(`fmt.SprintfNamed`: two `types.UID`s, or two strings) into `NewInvalidObjError`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.Preconditions__Check
public import Spec.k8s_io.apiserver.pkg.storage.NewInvalidObjError
public import Spec.k8s_io.apimachinery.pkg.api.meta.Accessor
public import Spec.fmt.SprintfNamed

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.Preconditions.Check.wp_proof
    (wp_Accessor : apimeta.Accessor.spec (GF := GF) (hG := hG))
    (wp_NewInvalidObjError : storage.NewInvalidObjError.spec (GF := GF) (hG := hG))
    (wp_SprintfNamed : fmt.SprintfNamed.spec (GF := GF) (hG := hG)) :
    storage.Preconditions.Check.spec (GF := GF) (hG := hG) := by
  intro pp ⟨pu, pr⟩ key obj R uid rvs
  wp_start as ⟨#Hpre, #Hmeta, HR⟩
  iunfold preAt at Hpre
  icases Hpre with (⟨%hpp, %hp⟩ | ⟨%lu, %lr, #Hpp, #Hu, #Hr⟩)
  · subst hpp; cases hp
    wp_auto
    iapply HΦ
    iframe
    have : KPre.ok ⟨none, none⟩ uid rvs = true := rfl
    simp only [this, ↓reduceIte]
    ipureintro; trivial
  · ihave %hnn := typedPointsto_not_null _ _ _ $$ Hpp
    iunfold metaAt at Hmeta
    icases Hmeta with ⟨#Hty, #Huid, #Hrv⟩
    ihave %hty := Hty $$ HR
    obtain ⟨ii, rfl, hty⟩ := hty
    wp_auto
    rw [decide_eq_false hnn]
    wp_auto
    wp_apply (wp_Accessor ii hty)
    iStructNamed Hpp
    wp_auto
    cases pu with
    | none =>
      iunfold optStrPtr at Hu
      icases Hu with %hlu
      subst hlu
      wp_auto
      cases pr with
      | none =>
        iunfold optStrPtr at Hr
        icases Hr with %hlr
        subst hlr
        wp_auto
        iapply HΦ
        iframe HR
        have : KPre.ok ⟨none, none⟩ uid rvs = true := by simp [KPre.ok]
        simp only [this, ↓reduceIte]
        ipureintro; trivial
      | some r =>
        iunfold optStrPtr at Hr
        ihave %hlr := typedPointsto_not_null _ _ _ $$ Hr
        rw [decide_eq_false hlr]
        wp_auto
        wp_bind
        iapply Hrv $$ %ii %_ [] HR
        · ipureintro; rfl
        inext
        iintro HR
        wp_auto
        by_cases hr : r = rvs
        · subst hr
          rw [decide_eq_true rfl]
          wp_auto
          iapply HΦ
          iframe HR
          have : KPre.ok ⟨none, some r⟩ uid r = true := by simp [KPre.ok]
          simp only [this, ↓reduceIte]
          ipureintro; trivial
        · rw [decide_eq_false hr]
          wp_auto
          wp_bind
          iapply Hrv $$ %ii %_ [] HR
          · ipureintro; rfl
          inext
          iintro HR
          wp_auto
          wp_apply wp_slice_literal
          try (isplitr; (ipureintro; rfl))
          iintro %sla ⟨Hargs, -⟩
          (try wp_auto)
          ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
          · iPkgInit
          wp_apply wp_SprintfNamed $$ [$Hfmt $Hargs] as %msg ⟨-, -⟩
          · ipureintro
            intro a ha
            rw [show sint.nat (W64 (0 + 1)) = 1 by rfl] at ha
            simp only [List.set_cons_succ, List.set_cons_zero, List.mem_cons, List.not_mem_nil,
              or_false] at ha
            rcases ha with rfl | rfl
            · exact Or.inl ((_root_.Perennial.fmt.ArgsWf.cons_string r []
                _root_.Perennial.fmt.ArgsWf.nil) _ (List.mem_singleton_self _))
            · exact Or.inl ((_root_.Perennial.fmt.ArgsWf.cons_string rvs []
                _root_.Perennial.fmt.ArgsWf.nil) _ (List.mem_singleton_self _))
          (try wp_auto)
          wp_apply +noauto wp_NewInvalidObjError as %l ⟨%e, Hl⟩
          ipersist Hl
          (try wp_auto)
          iapply HΦ
          iframe HR
          have : KPre.ok ⟨none, some r⟩ uid rvs = false := by simp [KPre.ok, hr]
          simp only [this, Bool.false_eq_true, ↓reduceIte]
          iunfold invalidErrIs
          iexists l, e
          iframe Hl
          ipureintro; rfl
    | some u =>
      iunfold optStrPtr at Hu
      ihave %hlu := typedPointsto_not_null _ _ _ $$ Hu
      rw [decide_eq_false hlu]
      wp_auto
      wp_bind
      iapply Huid $$ %ii %_ [] HR
      · ipureintro; rfl
      inext
      iintro HR
      wp_auto
      by_cases hu : u = uid
      · subst hu
        rw [decide_eq_true rfl]
        wp_auto
        cases pr with
        | none =>
          iunfold optStrPtr at Hr
          icases Hr with %hlr
          subst hlr
          wp_auto
          iapply HΦ
          iframe HR
          have : KPre.ok ⟨some u, none⟩ u rvs = true := by simp [KPre.ok]
          simp only [this, ↓reduceIte]
          ipureintro; trivial
        | some r =>
          iunfold optStrPtr at Hr
          ihave %hlr := typedPointsto_not_null _ _ _ $$ Hr
          rw [decide_eq_false hlr]
          wp_auto
          wp_bind
          iapply Hrv $$ %ii %_ [] HR
          · ipureintro; rfl
          inext
          iintro HR
          wp_auto
          by_cases hr : r = rvs
          · subst hr
            rw [decide_eq_true rfl]
            wp_auto
            iapply HΦ
            iframe HR
            have : KPre.ok ⟨some u, some r⟩ u r = true := by simp [KPre.ok]
            simp only [this, ↓reduceIte]
            ipureintro; trivial
          · rw [decide_eq_false hr]
            wp_auto
            wp_bind
            iapply Hrv $$ %ii %_ [] HR
            · ipureintro; rfl
            inext
            iintro HR
            wp_auto
            wp_apply wp_slice_literal
            try (isplitr; (ipureintro; rfl))
            iintro %sla ⟨Hargs, -⟩
            (try wp_auto)
            ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
            · iPkgInit
            wp_apply wp_SprintfNamed $$ [$Hfmt $Hargs] as %msg ⟨-, -⟩
            · ipureintro
              intro a ha
              rw [show sint.nat (W64 (0 + 1)) = 1 by rfl] at ha
              simp only [List.set_cons_succ, List.set_cons_zero, List.mem_cons, List.not_mem_nil,
                or_false] at ha
              rcases ha with rfl | rfl
              · exact Or.inl ((_root_.Perennial.fmt.ArgsWf.cons_string r []
                  _root_.Perennial.fmt.ArgsWf.nil) _ (List.mem_singleton_self _))
              · exact Or.inl ((_root_.Perennial.fmt.ArgsWf.cons_string rvs []
                  _root_.Perennial.fmt.ArgsWf.nil) _ (List.mem_singleton_self _))
            (try wp_auto)
            wp_apply +noauto wp_NewInvalidObjError as %l ⟨%e, Hl⟩
            ipersist Hl
            (try wp_auto)
            iapply HΦ
            iframe HR
            have : KPre.ok ⟨some u, some r⟩ u rvs = false := by simp [KPre.ok, hr]
            simp only [this, Bool.false_eq_true, ↓reduceIte]
            iunfold invalidErrIs
            iexists l, e
            iframe Hl
            ipureintro; rfl
      · rw [decide_eq_false hu]
        wp_auto
        wp_bind
        iapply Huid $$ %ii %_ [] HR
        · ipureintro; rfl
        inext
        iintro HR
        wp_auto
        wp_apply wp_slice_literal
        try (isplitr; (ipureintro; rfl))
        iintro %sla ⟨Hargs, -⟩
        (try wp_auto)
        ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
        · iPkgInit
        wp_apply wp_SprintfNamed $$ [$Hfmt $Hargs] as %msg ⟨-, -⟩
        · ipureintro
          have hU : _root_.Perennial.fmt.IsBasicType
              (underlying k8s_io.apimachinery.pkg.types.UID.ty) := by
            rw [show underlying k8s_io.apimachinery.pkg.types.UID.ty = go.string
              from go.IsUnderlying.is_underlying]
            simp [_root_.Perennial.fmt.IsBasicType]
          have hn : ∃ n, k8s_io.apimachinery.pkg.types.UID.ty = go.GoType.Named n [] ∧
              n ∈ EtcdGrove.fmt.methodlessNamedTypes :=
            ⟨go!"k8s.io/apimachinery/pkg/types.UID", by simp [k8s_io.apimachinery.pkg.types.UID.ty],
              by simp [EtcdGrove.fmt.methodlessNamedTypes]⟩
          intro a ha
          rw [show sint.nat (W64 (0 + 1)) = 1 by rfl] at ha
          simp only [List.set_cons_succ, List.set_cons_zero, List.mem_cons, List.not_mem_nil,
            or_false] at ha
          rcases ha with rfl | rfl <;> exact Or.inr ⟨hn, hU⟩
        (try wp_auto)
        wp_apply +noauto wp_NewInvalidObjError as %l ⟨%e, Hl⟩
        ipersist Hl
        (try wp_auto)
        iapply HΦ
        iframe HR
        have : KPre.ok ⟨some u, pr⟩ uid rvs = false := by simp [KPre.ok, hu]
        simp only [this, Bool.false_eq_true, ↓reduceIte]
        iunfold invalidErrIs
        iexists l, e
        iframe Hl
        ipureintro; rfl

end proof

end EtcdGrove
end Perennial
