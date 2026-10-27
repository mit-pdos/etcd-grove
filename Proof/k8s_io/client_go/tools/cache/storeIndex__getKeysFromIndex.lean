/-
Proof of `Spec/k8s_io/client_go/tools/cache/storeIndex__getKeysFromIndex.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.storeIndex__getKeysFromIndex
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- A lookup in indexer `n`'s index (at `l`, `ix !! n = some (l, X)`): the set's location. -/
theorem wp_ix_lookup (ip : Loc) (dq : DFrac) (ix : Ix) (n v : GoString) (l : Loc) (X : IxN)
    (hx : ix !! n = some (l, X)) :
    {{ ownIx (GF := GF) ip dq ix }}
      (App (App (Val (map.lookup1 go.string (k8s_io.apimachinery.pkg.util.sets.Set'.ty go.string)))
        (Val #l)) (Val #v))
    {{ RET #(setLoc ix n v); ownIx ip dq ix }} := by
  iintro %Φ Hix HΦ
  iunfold ownIx at Hix
  icases Hix with ⟨Hip, HIX⟩
  icases (BigSepM.bigSepM_lookup_acc hx) $$ HIX with ⟨HX, HIXc⟩
  iunfold ownIxN at HX
  icases HX with ⟨Hl, HXs⟩
  wp_apply (wp_map_lookup1 go.string (k8s_io.apimachinery.pkg.util.sets.Set'.ty go.string)
    l _ v dq) $$ [$Hl] as Hl
  have hs : ((GMap.fmap Prod.fst X) !! v).getD (zero_val Loc) = setLoc ix n v := by
    unfold setLoc; rw [hx]; simp only [Option.bind_some, GMap.lookup_fmap]
    cases X !! v <;> rfl
  rw [hs]
  iapply HΦ
  iunfold ownIx
  iframe
  iapply HIXc
  iunfold ownIxN
  iframe

theorem keysOfVals_take_succ (X : IxN) (vs : List GoString) (j : Nat) (v : GoString)
    (hv : vs[j]? = some v) (k : GoString) :
    keysOfVals X (vs.take (j + 1)) k ↔ keysOfVals X (vs.take j) k ∨ k ∈ viewN X v := by
  unfold keysOfVals
  rw [List.take_add_one, hv]
  simp only [Option.toList_some, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨w, hw | rfl, hk⟩
    · exact Or.inl ⟨w, hw, hk⟩
    · exact Or.inr hk
  · rintro (⟨w, hw, hk⟩ | hk)
    · exact ⟨w, Or.inl hw, hk⟩
    · exact ⟨v, Or.inr rfl, hk⟩

theorem storeIndex.getKeysFromIndex.wp_proof
    (wp_Insert : sets.Set.Insert.spec (GF := GF) (hG := hG)) :
    storeIndex.getKeysFromIndex.spec (GF := GF) (hG := hG) := by
  intro i im ip dqi dqm dq fv fns ix OK n obj
  wp_start as ⟨Hixr, Him, #Hfns, Hipr, Hix, #HOK⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hsets : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets $$ []
  · iPkgInit
  iunfold fnsOk at Hfns
  icases Hfns with ⟨%hdom, #Hfv⟩
  wp_auto
  wp_apply (wp_map_lookup1 go.string IndexFunc.ty im fv n dqm) $$ [$Him] as Him
  cases hf : fv !! n with
  | none =>
    have hn : fns !! n = none := by
      cases h : fns !! n with
      | none => rfl
      | some _ =>
        have := (hdom n).1 (by rw [GMap.mem_iff, h]; rfl)
        rw [GMap.mem_iff, hf] at this; cases this
    simp only [Option.getD_none]
    (try wp_auto)
    simp only [show zero_val GoFunc = func.nil from rfl, _root_.decide_true]
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply (fmt.wp_Errorf _ _ _ (_root_.Perennial.fmt.ArgsWf.cons_string n []
      _root_.Perennial.fmt.ArgsWf.nil)) $$ [$Hl1] as %err #Herr
    (try wp_auto)
    iapply HΦ
    iframe
    simp only [hn]
    iframe
    ipureintro
    intro h; cases h
  | some f =>
    ihave ⟨%F, %hF, #Hfn⟩ := BigSepM.bigSepM_lookup hf $$ Hfv
    iunfold fnOk at Hfn
    icases Hfn with ⟨%hfnn, #Hcall⟩
    simp only [Option.getD_some, decide_eq_false hfnn]
    (try wp_auto)
    wp_apply Hcall $$ [$HOK]
    iintro %vsl %err ⟨%herr, %dqv, Hvsl⟩
    subst herr
    (try wp_auto)
    ihave %Hvlen := ownSlice_len _ _ _ $$ Hvsl
    iunfold ownIx at Hix
    icases Hix with ⟨Hip, HIX⟩
    wp_apply (wp_map_lookup1 go.string index.ty ip _ n dq) $$ [$Hip] as Hip
    cases hx : ix !! n with
    | none =>
      have hix : ixAt ix n = ∅ := by unfold ixAt; rw [hx]; rfl
      have hno : ∀ vs k, ¬ keysOfVals (ixAt ix n) vs k := by
        rintro vs k ⟨w, -, hk⟩
        rw [hix] at hk; unfold viewN at hk; simp [GMap.mem_iff] at hk
      simp only [Option.map_none, Option.getD_none, show zero_val Loc = map.nil from rfl]
      (try wp_auto)
      wp_if_destruct
      · obtain ⟨v, hv⟩ : ∃ v, (F obj)[0]? = some v := by
          cases h : F obj with
          | nil => rw [h] at Hvlen; simp at Hvlen; word
          | cons v _ => exact ⟨v, rfl⟩
        simp only [show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z vsl.len by word, ↓reduceIte]
        wp_apply (wp_load_slice_index vsl (sint.Z (W64 0)) (F obj) dqv v (by word)) $$ [$Hvsl] as Hvsl
        · ipureintro; exact hv
        (try wp_auto)
        iapply HΦ
        iframe
        simp only [hF]
        isplitr
        · ipureintro; first | rfl | trivial
        iexists ∅
        isplitr
        · ipureintro; intro k; simp only [GMap.mem_iff, GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true, false_iff]; exact hno _ k
        iunfold setRes
        ileft
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        iunfold ownIx; iframe
      · wp_apply (wp_map_make1 (K := GoString) (V := sets.Elem) go.string
          k8s_io.apimachinery.pkg.util.sets.Empty.ty) as %m Hm
        (try wp_auto)
        ihave IH : iprop(∃ (j : w64) (x : GoString),
            "i" ∷ i_ptr ↦ j ∗
            "indexedValue" ∷ indexedValue_ptr ↦ x ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z vsl.len⌝) $$ [i indexedValue]
        · iexists W64 0, _
          iframe
          ipureintro
          exact ⟨by word, by have := Hvlen.2; word⟩
        wp_for IH
        wp_if_destruct
        · have Hif' : sint.Z j < sint.Z vsl.len := by
            first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
          have Hlt : sint.nat j < (F obj).length := by word
          obtain ⟨e, He⟩ : ∃ e, (F obj)[sint.nat j]? = some e :=
            ⟨_, List.getElem?_eq_getElem Hlt⟩
          simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z vsl.len from ⟨Hj.1, Hif'⟩, _root_.and_self,
            ↓reduceIte]
          wp_apply (wp_load_slice_index vsl (sint.Z j) (F obj) dqv e Hj.1) $$ [$Hvsl] as Hvsl
          · ipureintro; exact He
          (try wp_auto)
          rw [show (zero_val GoMap) = map.nil from rfl]
          wp_func_lits
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, _
          iframe
          ipureintro; word
        · have Hif' : ¬ sint.Z j < sint.Z vsl.len := by
            first | exact Hif | (intro h; apply Hif; rw [decide_eq_true h])
          simp [Hif']
          (try wp_auto)
          iapply HΦ
          iframe
          simp only [hF]
          isplitr
          · ipureintro; first | rfl | trivial
          iexists ∅
          isplitr
          · ipureintro; intro k; simp only [GMap.mem_iff, GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true, false_iff]; exact hno _ k
          iunfold setRes
          iright
          iexists (DFrac.own 1)
          iframe Hm
          iintro -
          iunfold ownIx; iframe
    | some e =>
      obtain ⟨l, X⟩ := e
      have hix : ixAt ix n = X := by unfold ixAt; rw [hx]; rfl
      simp only [Option.map_some, Option.getD_some]
      ihave Hix : ownIx ip dq ix $$ [Hip HIX]
      · iunfold ownIx; iframe
      (try wp_auto)
      wp_if_destruct
      · obtain ⟨v, hv⟩ : ∃ v, (F obj)[0]? = some v := by
          cases h : F obj with
          | nil => rw [h] at Hvlen; simp at Hvlen; word
          | cons v _ => exact ⟨v, rfl⟩
        have hone : F obj = [v] := by
          cases h : F obj with
          | nil => rw [h] at hv; cases hv
          | cons w ws =>
            rw [h] at hv Hvlen
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
            subst hv
            cases ws with
            | nil => rfl
            | cons _ _ => simp at Hvlen; word
        simp only [show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z vsl.len by word, ↓reduceIte]
        wp_apply (wp_load_slice_index vsl (sint.Z (W64 0)) (F obj) dqv v (by word)) $$ [$Hvsl] as Hvsl
        · ipureintro; exact hv
        (try wp_auto)
        wp_apply (wp_ix_lookup ip dq ix n v l X hx) $$ [$Hix] as Hix
        (try wp_auto)
        iapply HΦ
        iframe
        simp only [hF]
        isplitr
        · ipureintro; first | rfl | trivial
        iexists viewN (ixAt ix n) v
        isplitr
        · ipureintro; intro k
          rw [hone]
          unfold keysOfVals
          simp
        iunfold setRes
        icases (ownIx_set_acc ip dq ix n v) $$ Hix with (⟨%hsn, Hix⟩ | ⟨Hs, Hsc⟩)
        · ileft; iframe; ipureintro; exact hsn
        · iright; iexists dq; iframe
      · wp_apply (wp_map_make1 (K := GoString) (V := sets.Elem) go.string
          k8s_io.apimachinery.pkg.util.sets.Empty.ty) as %m Hm
        (try wp_auto)
        ihave IH : iprop(∃ (j : w64) (x : GoString) (S : KSet),
            "i" ∷ i_ptr ↦ j ∗
            "indexedValue" ∷ indexedValue_ptr ↦ x ∗
            "storeKeySet" ∷ storeKeySet_ptr ↦ m ∗
            "Hm" ∷ m ↦$ S ∗
            "Hix" ∷ ownIx ip dq ix ∗
            "%HS" ∷ ⌜∀ k, k ∈ S ↔ keysOfVals (ixAt ix n) ((F obj).take (sint.nat j)) k⌝ ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z vsl.len⌝) $$ [i indexedValue storeKeySet Hm Hix]
        · iexists W64 0, _, ∅
          iframe
          ipureintro
          refine ⟨fun k => ?_, by word, by have := Hvlen.2; word⟩
          simp only [GMap.mem_iff, GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true, false_iff]
          rintro ⟨w, hw, -⟩
          rw [show sint.nat (W64 0) = 0 from rfl] at hw
          simp at hw
        wp_for IH
        wp_if_destruct
        · have Hif' : sint.Z j < sint.Z vsl.len := by
            first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
          have Hlt : sint.nat j < (F obj).length := by word
          obtain ⟨e, He⟩ : ∃ e, (F obj)[sint.nat j]? = some e :=
            ⟨_, List.getElem?_eq_getElem Hlt⟩
          simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z vsl.len from ⟨Hj.1, Hif'⟩, _root_.and_self,
            ↓reduceIte]
          wp_apply (wp_load_slice_index vsl (sint.Z j) (F obj) dqv e Hj.1) $$ [$Hvsl] as Hvsl
          · ipureintro; exact He
          (try wp_auto)
          wp_apply (wp_ix_lookup ip dq ix n e l X hx) $$ [$Hix] as Hix
          (try wp_auto)
          have hnext := keysOfVals_take_succ (ixAt ix n) (F obj) (sint.nat j) e He
          have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
          icases (ownIx_set_acc ip dq ix n e) $$ Hix with (⟨%hsn, Hix⟩ | ⟨Hs, Hsc⟩)
          · obtain ⟨hsl, hsv⟩ := hsn
            rw [hsl, show (null : Loc) = map.nil from rfl]
            wp_func_lits
            (try wp_auto)
            wp_for_post
            iframe
            iexists j + W64 1, _, S
            iframe
            ipureintro
            refine ⟨fun k => ?_, by word⟩
            rw [hj1, hnext, hsv, HS]
            simp [GMap.mem_iff]
          · wp_func_lits
            wp_bind (App (App (Val (map.forRange _ _)) _) _)
            iapply wp_map_for_range (fun (keys : List GoString) (p : Int) => iprop(∃ (S' : KSet)
                (x : GoString),
                "%Hp" ∷ ⌜0 ≤ p⌝ ∗
                "key" ∷ key_ptr ↦ x ∗
                "storeKeySet" ∷ storeKeySet_ptr ↦ m ∗
                "Hm" ∷ m ↦$ S' ∗
                "%HS'" ∷ ⌜∀ k, k ∈ S' ↔ keysOfVals (ixAt ix n) ((F obj).take (sint.nat j)) k ∨
                  k ∈ keys.take p.toNat⌝)) $$ Hs
            iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
            isplitl [key storeKeySet Hm]
            · iexists S, _
              simp only [named]
              iframe
              ipureintro
              refine ⟨Int.le_refl _, fun k => ?_⟩
              rw [HS]; simp
            isplitr
            · imodintro
              iintro %p %k %el ⟨%Hkey, %Hel⟩ HP
              iNamed HP
              wp_auto
              wp_apply wp_slice_literal
              isplitr
              · ipureintro; rfl
              iintro %l1 ⟨Hl1, -⟩
              simp only [go.arrayLiteralSize, List.foldl]
              (try wp_auto)
              wp_apply (sets.Set.wp_ptr_Insert_of wp_Insert) $$ [$Hsets $storeKeySet $Hm $Hl1]
                as ⟨storeKeySet, Hm, -⟩
              (try wp_auto)
              unfold forMapPostcondition
              iright; ileft
              isplitr
              · ipureintro; rfl
              iexists sets.insertAll S' [k], k
              simp only [named]
              iframe
              ipureintro
              refine ⟨by omega, fun k' => ?_⟩
              have Htake : keys.take (p + 1).toNat = keys.take p.toNat ++ [k] := by
                rw [show (p + 1).toNat = p.toNat + 1 by omega]
                rw [List.take_add_one, Hkey]; rfl
              rw [Htake]
              simp only [sets.insertAll, List.foldl, mem_ins, HS', List.mem_append,
                List.mem_singleton]
              constructor
              · rintro (h | h | h)
                · exact Or.inr (Or.inr h)
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
              · rintro (h | h | h)
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr h)
                · exact Or.inl h
            iintro HP Hs
            iNamed HP
            ihave Hix := Hsc $$ Hs
            (try wp_auto)
            wp_for_post
            iframe
            iexists j + W64 1, _, S'
            iframe
            ipureintro
            refine ⟨fun k => ?_, by word⟩
            rw [Int.toNat_natCast, ← Hklen, List.take_length] at HS'
            rw [hj1, hnext, HS', Hkset, ← GMap.mem_iff]
        · have Hif' : ¬ sint.Z j < sint.Z vsl.len := by
            first | exact Hif | (intro h; apply Hif; rw [decide_eq_true h])
          simp [Hif']
          (try wp_auto)
          have hj : sint.nat j = (F obj).length := by word
          rw [hj, List.take_length] at HS
          iapply HΦ
          iframe
          simp only [hF]
          isplitr
          · ipureintro; first | rfl | trivial
          iexists S
          isplitr
          · ipureintro; exact HS
          iunfold setRes
          iright
          iexists (DFrac.own 1)
          iframe Hm
          iintro -
          iexact Hix

end proof

end cache
end EtcdGrove
end Perennial
