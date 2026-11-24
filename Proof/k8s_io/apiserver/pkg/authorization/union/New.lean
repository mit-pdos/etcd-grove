/-
The proof of `New.spec` (`Spec/k8s_io/apiserver/pkg/authorization/union/New.lean`). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.union.New
public import Spec.fmt.ErrorfLeaf

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace union

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union EtcdGrove.authorizer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.union.Assumptions]

theorem New.wp_proof
    (wp_ErrorfLeaf : EtcdGrove.fmt.ErrorfLeaf.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro s nas
  wp_start as ⟨#Hs, #Has, %Hnas⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply (wp_map_make2 (K := GoString) (V := GoInterface) s.len go.string Authorizer.ty) as %mref Hmref
  (try wp_auto)
  ihave HI : (∃ (j : w64) (hd : NamedAuthorizer) (mm : GMap GoString GoInterface), "i" ∷ i_ptr ↦ j ∗
      "handler" ∷ handler_ptr ↦ hd ∗ "Hmref" ∷ mref ↦$ mm ∗ "Hmm" ∷ ([∗map] _k ↦ a ∈ mm, isAuthorizer (GF := GF) a) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ ∗
      "nameToAuthorizer" ∷ nameToAuthorizer_ptr ↦ mref ∗
      "authorizationHandlers" ∷ authorizationHandlers_ptr ↦ s : IProp GF) $$ [-HΦ «$res0» «$res1»]
  · iexists W64 0, zero_val NamedAuthorizer, ∅
    iframe
    isplitl []
    · iapply BigSepM.bigSepM_empty.2
      iempintro
    · ipureintro; constructor <;> word
  wp_for HI
  by_cases hlt : sint.Z j < sint.Z s.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    obtain ⟨na', hv⟩ : ∃ v, nas[sint.nat j]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index s (sint.Z j) nas _ na' Hj.1) $$ [Hs] as -
    · iframe #; ipureintro; simpa [sint.nat] using hv
    ihave #Ha := (BigSepL.bigSepL_lookup (Φ := fun _ na => isAuthorizer (GF := GF) na.Authorizer') hv) $$ Has
    (try wp_auto)
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hnl
    wp_if_destruct
    · -- an empty name
      wp_apply (wp_ErrorfLeaf _ slice.nil [] (DFrac.own 1)) $$ [] as %ferr -
      · isplitr; · iapply ownSlice_nil
        fmt_args_ok
      (try wp_auto)
      wp_for_post
      iapply HΦ
      ileft
      ipureintro; simp
    · (try wp_auto)
      wp_apply (wp_map_lookup2 go.string Authorizer.ty mref mm na'.AuthorizerName' (DFrac.own 1)) $$ [$Hmref]
        as Hmref
      cases hl : mm !! na'.AuthorizerName' with
      | some a0 =>
        simp only [Option.isSome_some]
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sp ⟨Hsp, -⟩
        (try wp_auto)
        wp_apply wp_ErrorfLeaf $$ [$Hsp] as %ferr -
        · fmt_args_ok
        (try wp_auto)
        wp_for_post
        iapply HΦ
        ileft
        ipureintro; simp
      | none =>
        simp only [Option.isSome_none]
        wp_auto
        wp_apply (wp_mapInsert go.string mref mm na'.AuthorizerName' na'.Authorizer') $$ [$Hmref] as Hmref
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, na', _
        iframe
        isplitl
        · iapply (BigSepM.bigSepM_insert hl).2
          isplitr
          · iexact Ha
          iexact Hmm
        ipureintro; constructor <;> word
  · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    imod ownMap_persist mref _ mm $$ Hmref with #Hmref
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists { chain' := s, nameToAuthorizer' := mref }
    isplitr
    · ipureintro; rfl
    unfold isUnionAuthz
    iexists nas, mm
    dsimp only
    isplitr
    · iexact Hs
    isplitr
    · iexact Has
    isplitr
    · iexact Hmref
    isplitl [Hmm]
    · iexact Hmm
    ipureintro; exact Hnas

end proof

end union
end EtcdGrove
end Perennial
