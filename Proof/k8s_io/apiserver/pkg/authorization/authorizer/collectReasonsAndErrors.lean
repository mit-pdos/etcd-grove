/-
The proof of `collectReasonsAndErrors.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/collectReasonsAndErrors.lean`). Lean-first
(no Rocq counterpart).
-/
module

public import Proof.fmt.OutLemmas
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.collectReasonsAndErrors
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Reason
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Error
public import Perennial.Spec.strings.Join
public import Perennial.Spec.fmt.Sprintf
public import Spec.fmt.ErrorfLeaf
public import Proof.k8s_io.apimachinery.pkg.util.errors.ErrTreeOk
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnionedDecisions
public import Spec.slices.Concat
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethods
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethodsB3
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ForRange
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B3Lemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem collectReasonsAndErrors.wp_proof
    (wp_ConditionsAwareDecision_IsAllow : EtcdGrove.authorizer.ConditionsAwareDecision.IsAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecision.IsNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsDeny : EtcdGrove.authorizer.ConditionsAwareDecision.IsDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_Reason : EtcdGrove.authorizer.ConditionsAwareDecision.Reason.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_Error : EtcdGrove.authorizer.ConditionsAwareDecision.Error.spec (GF := GF) (hG := hG))
    (wp_Join : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG))
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_ErrorfLeaf : EtcdGrove.fmt.ErrorfLeaf.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsUnion : EtcdGrove.authorizer.ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_UnionedDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.UnionedDecisions.spec (GF := GF) (hG := hG))
    (wp_Concat : EtcdGrove.slices.Concat.spec (GF := GF) (hG := hG))
    (wp_aggregate_Error : EtcdGrove.utilerrors.aggregate.Error.spec (GF := GF) (hG := hG)) :
    collectReasonsAndErrors.spec (GF := GF) (hG := hG) := by
  have H : ⊢ (∀ (s : GoSlice) (dq : DFrac) (pre : List GoString) (d : ConditionsAwareDecision)
      (m : Dec) (k : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗
        s ↦*{dq} pre ∗ isDecision d m ∗ ⌜pre.length + m.depth < 2 ^ 63⌝ }}
      (App (App (App (Val (@! collectReasonsAndErrors)) (Val #s)) (Val #d)) (Val #k))
    {{ (rs es : GoSlice), RET (PairV #rs #es); s ↦*{dq} pre ∗
        (∃ xs : List GoString, rs ↦* xs ∗ ownSliceCap GoString rs (DFrac.own 1)) ∗
        (∃ ys : List GoInterface, es ↦* ys ∗ ownSliceCap GoInterface es (DFrac.own 1) ∗
          [∗list] e ∈ ys, utilerrors.errTree e) }}
      : IProp GF) := by
    iloeb as IH
    iintro %s %dq %pre %d %m %k
    wp_start as ⟨Hs, #Hd, %Hdep⟩
    wp_auto
    icases isDecision_tag d m $$ Hd with %Htag
    wp_join (Q := fun v => iprop(∃ b : Bool, ⌜v = #b⌝ ∗ condAwareDecision_ptr ↦ d ∗
        unconditionalDecisionToCollect_ptr ↦ k)) at (if: _ then #true else _)
      with [condAwareDecision unconditionalDecisionToCollect]
    · repeat' (first
        | (wp_apply (ConditionsAwareDecision.wp_ptr_IsAllow_of wp_ConditionsAwareDecision_IsAllow _ _ d)
            $$ [$condAwareDecision] as condAwareDecision)
        | (wp_apply (ConditionsAwareDecision.wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion
            _ _ d) $$ [$condAwareDecision] as condAwareDecision)
        | (wp_apply (ConditionsAwareDecision.wp_ptr_IsDeny_of wp_ConditionsAwareDecision_IsDeny _ _ d)
            $$ [$condAwareDecision] as condAwareDecision)
        | wp_if_destruct)
      all_goals (iexists _; iframe; ipureintro; rfl)
    iintro ⟨%b, %Hb, condAwareDecision, unconditionalDecisionToCollect⟩
    subst Hb
    ihave Hrn : (slice.nil ↦* ([] : List GoString) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hrc : ownSliceCap (GF := GF) GoString slice.nil (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    ihave Hen : (slice.nil ↦* ([] : List GoInterface) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hec : ownSliceCap (GF := GF) GoInterface slice.nil (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    ihave #Hest : ([∗list] e ∈ ([] : List GoInterface), utilerrors.errTree (GF := GF) e) $$ []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    wp_if_destruct
    · wp_apply (ConditionsAwareDecision.wp_ptr_IsUnion_of wp_ConditionsAwareDecision_IsUnion _ _ d)
        $$ [$condAwareDecision] as condAwareDecision
      rw [Htag, Dec.tag_union]
      cases hU : m.isUnion
      · wp_auto
        iapply HΦ
        iframe
        iapply BigSepL.bigSepL_nil.2; itrivial
      cases m with
      | union ks =>
        icases isDecision_union d ks $$ Hd with ⟨%nds, #Hinner, #HL⟩
        wp_apply (ConditionsAwareDecision.wp_ptr_UnionedDecisions_of
          wp_ConditionsAwareDecision_UnionedDecisions _ _ d nds) $$ [$condAwareDecision]
          as %f ⟨condAwareDecision, #Hf⟩
        · iexact Hinner
        wp_bind (App (App (Val (func.forRange 2)) _) _)
        iapply k8s.wp_forRange2 _ _ _ (by simp) rfl
        iintro %y %Tok %Done HTok #Hy
        iunfold seq2Ok at Hf
        ihave Hrun := Hf $$ %y %(fun _ => iprop(Tok ∗ ∃ (rsl esl : GoSlice) (rxs : List GoString)
            (eys : List GoInterface) (sd : ConditionsAwareDecision) (an : GoString),
            aggregateReasons_ptr ↦ rsl ∗ rsl ↦* rxs ∗ ownSliceCap GoString rsl (DFrac.own 1) ∗
            aggregateErrors_ptr ↦ esl ∗ esl ↦* eys ∗ ownSliceCap GoInterface esl (DFrac.own 1) ∗
            ([∗list] e ∈ eys, utilerrors.errTree e) ∗ s ↦*{dq} pre ∗ authorizerNamePrefix_ptr ↦ s ∗ unconditionalDecisionToCollect_ptr ↦ k ∗
            subDecision_ptr ↦ sd ∗ authorizerName_ptr ↦ an)) %(iprop(False)) []
        · iintro !> %i %kk %vv %Hi
          iunfold yield2Ok
          iintro !> %Ψ HI HΨ
          icases HI with ⟨HTok, %rsl, %esl, %rxs, %eys, %sd, %an, aggregateReasons, Hrn, Hrc,
            aggregateErrors, Hen, Hec, #Hest, Hs, authorizerNamePrefix, unconditionalDecisionToCollect,
            subDecision, authorizerName⟩
          iapply Hy $$ %(#kk) %(#vv) %Ψ [] HTok
          · ipureintro; constructor <;> simp
          wp_auto
          wp_apply (wp_slice_literal [kk])
          isplitr
          · ipureintro; rfl
          iintro %t ⟨Ht, -⟩
          wp_apply (wp_slice_literal [s, _])
          isplitr
          · ipureintro; rfl
          iintro %ss ⟨Hss, -⟩
          imod ownSlice_string_common s _ dq pre [kk] $$ [Hs Ht] with ⟨%dq', Hs, Ht, Hback⟩
          · iframe
          have Hsum : ([pre, [kk]].map List.length).sum < 2 ^ 63 := by
            simp only [Dec.depth] at Hdep
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              List.length_singleton]
            omega
          wp_apply (wp_Concat _ (DFrac.own 1) [s, _] [pre, [kk]] dq' rfl Hsum) $$ [$Hss Hs Ht]
            as %s' ⟨-, HL2, Hs', Hcap'⟩
          · simp only [List.zip_cons_cons, List.zip_nil_left]
            iapply BigSepL.bigSepL_cons.2
            iframe Hs
            iapply BigSepL.bigSepL_cons.2
            iframe Ht
            iapply BigSepL.bigSepL_nil.2
            iempintro
          icases HL2 with ⟨Hs, -, -⟩
          ihave Hs := Hback $$ Hs
          have Hi' : (List.map (fun x => x.d') nds)[i]? = some vv := by
            rw [List.getElem?_map] at Hi ⊢
            cases h : nds[i]? with
            | none => simp [h] at Hi
            | some nd => simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at Hi ⊢; exact Hi.2
          icases isDecisionL_lookup _ ks i vv Hi' $$ HL with ⟨%mi, %Hmi, #Hdi⟩
          wp_apply IH $$ %s' %(DFrac.own 1) %([pre, [kk]].flatten) %vv %mi %k [Hs']
            as %rs %es ⟨Hs', ⟨%xs2, Hrs, Hrsc⟩, ⟨%ys2, Hes, Hesc, #Hest2⟩⟩
          · iframe
            isplitr
            · iexact Hdi
            ipureintro
            have := Dec.depth_le_depthL ks i mi Hmi
            simp only [Dec.depth] at Hdep
            simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append,
              List.length_singleton]
            omega
          wp_apply wp_slice_append $$ [$Hrn $Hrc $Hrs] as %rsl' ⟨Hrn, Hrc, -⟩
          wp_apply wp_slice_append $$ [$Hen $Hec $Hes] as %esl' ⟨Hen, Hec, -⟩
          iunfold k8s.forRangePost
          ileft
          isplitr
          · ipureintro; left; rfl
          iintro HTok
          iapply HΨ
          simp only [↓reduceIte]
          iframe HTok
          iexists _, _, _, _, _, _
          iframe
          iapply BigSepL.bigSepL_append.2
          isplitr; · iexact Hest
          iexact Hest2
        iunfold iterRunOk at Hrun
        iapply Hrun $$ [HTok aggregateReasons aggregateErrors Hrn Hrc Hen Hec Hs authorizerNamePrefix
          unconditionalDecisionToCollect subDecision authorizerName]
        · simp only
          iframe HTok
          iexists slice.nil, slice.nil, [], [], _, _
          iframe
          iapply BigSepL.bigSepL_nil.2; itrivial
        iintro !> Hpost
        icases Hpost with (⟨HTok, %rsl, %esl, %rxs, %eys, %sd, %an, aggregateReasons, Hrn, Hrc,
          aggregateErrors, Hen, Hec, #Hest', Hs, authorizerNamePrefix, unconditionalDecisionToCollect,
          subDecision, authorizerName⟩ | %HF)
        rotate_left
        · exact HF.elim
        isplitr
        · ipureintro; simp
        ileft
        iframe HTok
        wp_auto
        iapply HΦ
        iframe
        iexact Hest'
      | deny => simp [Dec.isUnion] at hU
      | allow => simp [Dec.isUnion] at hU
      | noOpinion => simp [Dec.isUnion] at hU
      | cmap => simp [Dec.isUnion] at hU
    · wp_apply (ConditionsAwareDecision.wp_ptr_Reason_of wp_ConditionsAwareDecision_Reason _ _ d)
        $$ [$condAwareDecision] as condAwareDecision
      wp_join iprop(∃ (sl : GoSlice) (xs : List GoString), aggregateReasons_ptr ↦ sl ∗ sl ↦* xs ∗
          ownSliceCap GoString sl (DFrac.own 1) ∗ s ↦*{dq} pre ∗ authorizerNamePrefix_ptr ↦ s ∗
          reason_ptr ↦ d.reason') at next
        with [aggregateReasons Hrn Hrc Hs authorizerNamePrefix reason]
        as ⟨%rsl, %rxs, aggregateReasons, Hrn, Hrc, Hs, authorizerNamePrefix, reason⟩
      · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
        wp_if_destruct
        · iframe
          try (ipureintro; rfl)
        · wp_apply (wp_Join s pre dq) $$ [$Hs] as Hs
          wp_apply (wp_slice_literal [interface.mkOk go.string #(go!": ".intercalate pre),
            interface.mkOk go.string #d.reason'])
          isplitr
          · ipureintro; rfl
          iintro %asl ⟨Hasl, -⟩
          wp_apply (EtcdGrove.fmt.wp_Sprintf_pure wp_Sprintf go!"%s: {%s}"
            [.dir none _root_.Perennial.fmt.verb_s, .lit go!": {", .dir none _root_.Perennial.fmt.verb_s, .lit go!"}"] _ _ _ _
            (by fmt_encode) (by fmt_fits) (.str _ _ _ (.str _ _ _ .nil)))
            $$ [$Hasl] as %str ⟨-, -⟩
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %osl ⟨Hosl, -⟩
          wp_apply wp_slice_append $$ [$Hrn $Hrc $Hosl] as %rsl' ⟨Hrn, Hrc, -⟩
          wp_join_done
      wp_apply (ConditionsAwareDecision.wp_ptr_Error_of wp_ConditionsAwareDecision_Error _ _ d)
        $$ [$condAwareDecision] as condAwareDecision
      ihave #Hde := isDecision_err d m $$ Hd
      wp_join iprop(∃ (sl : GoSlice) (ys : List GoInterface), aggregateErrors_ptr ↦ sl ∗ sl ↦* ys ∗
          ownSliceCap GoInterface sl (DFrac.own 1) ∗ s ↦*{dq} pre ∗ authorizerNamePrefix_ptr ↦ s ∗
          [∗list] e ∈ ys, utilerrors.errTree e) at next
        with [aggregateErrors Hen Hec Hs authorizerNamePrefix err]
        as ⟨%esl, %eys, aggregateErrors, Hen, Hec, Hs, authorizerNamePrefix, #Hest'⟩
      · cases he : d.err' with
        | nil =>
          wp_auto; wp_join_done
          iexists _, []
          iframe
          try (iapply BigSepL.bigSepL_nil.2; itrivial)
        | ok ei =>
          wp_auto
          wp_apply (wp_Join s pre dq) $$ [$Hs] as Hs
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %asl ⟨Hasl, -⟩
          wp_apply (wp_ErrorfLeaf _ _ _ _) $$ [$Hasl] as %e ⟨-, #He, %hE⟩
          · fmt_args_intro
            isplitl
            · simp only [fmt.argOkAt]; ileft; ipureintro
              exact (show _root_.Perennial.fmt.ArgsWf [interface.mkOk go.string #(go!": ".intercalate pre)] from
                .cons_string _ _ .nil) _ (List.mem_singleton_self _)
            isplitl
            · iapply fmt.argOkAt_of_fmtErrorOkOrNil
              isplitr
              · ipureintro; exact ⟨by decide, by decide⟩
              rw [← he]
              iapply utilerrors.errTreeOrNil_fmtErrorOkOrNil wp_aggregate_Error
              isplitr
              · iPkgInit
              · iexact Hde
            · itrivial
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %osl ⟨Hosl, -⟩
          wp_apply wp_slice_append $$ [$Hen $Hec $Hosl] as %esl' ⟨Hen, Hec, -⟩
          ihave #Het := utilerrors.errTree_of_errOk e hE $$ He
          wp_join_done
          iexists _, _
          iframe
          rw [List.nil_append]
          iapply BigSepL.bigSepL_cons.2
          isplitr; · iexact Het
          iapply BigSepL.bigSepL_nil.2; itrivial
      iapply HΦ
      iframe
      iexact Hest'
  intro s dq pre d m k hdep
  iintro %Φ ⟨#Hpkg, Hs, #Hd⟩ HΦ
  ihave #H := H
  iapply H $$ %s %dq %pre %d %m %k [Hs] HΦ
  iframe Hs
  iframe #
  ipureintro; exact hdep

end proof

end authorizer
end EtcdGrove
end Perennial
