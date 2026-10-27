/-
Proof of `Spec/k8s_io/client_go/tools/cache/cache__Replace.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.cache__Replace
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Replace

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

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

theorem keyedItems_snoc (KF : GoInterface → GoString) (xs : List GoInterface) (x : GoInterface) :
    keyedItems KF (xs ++ [x]) = <[KF x := x]> (keyedItems KF xs) := by
  unfold keyedItems; rw [List.foldl_append]; rfl

/-- Every object of `keyedItems KF xs` is one of `xs`. -/
theorem keyedItems_mem (KF : GoInterface → GoString) (xs : List GoInterface) :
    ∀ k o, keyedItems KF xs !! k = some o → o ∈ xs := by
  suffices h : ∀ (ys : List GoInterface) (m : Items), (∀ k o, m !! k = some o → o ∈ xs) →
      (∀ y ∈ ys, y ∈ xs) → ∀ k o, (ys.foldl (fun m x => <[KF x := x]> m) m) !! k = some o →
        o ∈ xs from
    h xs ∅ (by intro k o h; simp at h) (fun y hy => hy)
  intro ys
  induction ys with
  | nil => intro m hm _ k o h; exact hm k o h
  | cons y ys ih =>
    intro m hm hys
    apply ih
    · intro k o h
      rw [GMap.lookup_insert_Some] at h
      rcases h with ⟨_, rfl⟩ | ⟨_, h⟩
      · exact hys _ List.mem_cons_self
      · exact hm k o h
    · intro z hz; exact hys z (List.mem_cons_of_mem _ hz)

theorem cache.Replace.wp_proof
    (wp_inner : threadSafeMap.Replace.spec (GF := GF) (hG := hG)) :
    cache.Replace.spec (GF := GF) (hG := hG) := by
  intro ca ts γ OK Fam KF sl xs rv
  iintro %Φ ⟨#Hpkg, #Hca, Hsl, #Hok⟩ HAU
  iunfold isCache at Hca
  icases Hca with ⟨%kf, #Hcs, #Hkf, #Htr, #Hkey, #Hts⟩
  iunfold keyOk at Hkey
  wp_method_call
  wp_call
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_apply (wp_map_make2 (K := GoString) (V := GoInterface) _ go.string (go.GoType.InterfaceType []))
    as %m Hm
  ihave IH : iprop(∃ (n : w64) (x : GoInterface),
      "i" ∷ i_ptr ↦ n ∗
      "item" ∷ item_ptr ↦ x ∗
      "Hm" ∷ m ↦$ keyedItems KF (xs.take (sint.nat n)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝) $$ [i item Hm]
  · iexists W64 0, _
    iframe
    ipureintro
    word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by word
    obtain ⟨e, He⟩ : ∃ e, xs[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) xs (DFrac.own 1) e Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact He
    ihave #He := BigSepL.bigSepL_lookup (Φ := fun _ x => iprop(OK x)) He $$ Hok
    wp_apply Hkey $$ [$He]
    iintro %k %err %hk
    obtain ⟨rfl, rfl⟩ := hk
    wp_auto
    wp_apply (wp_mapInsert go.string m _ (KF e) e) $$ [$Hm] as Hm
    wp_for_post
    iframe
    iexists n + W64 1, _
    iframe
    isplitl
    · have : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [this, List.take_add_one, He]
      simp only [Option.toList_some]
      rw [keyedItems_snoc]
      iexact Hm
    · ipureintro; word
  · wp_bind
    have hn : sint.nat n = xs.length := by word
    rw [hn, List.take_length] at *
    iapply (wp_inner ts γ OK Fam m (keyedItems KF xs) rv) $$ [$Hpkg $Hts $Hm]
    · iapply (BigSepM.bigSepM_intro (P := iprop(□ [∗list] x ∈ xs, OK x)) ?_) $$ Hok
      intro k o hko
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (keyedItems_mem KF xs k o hko)
      iintro #H
      iunfold okNil
      iright
      imodintro
      iapply (BigSepL.bigSepL_lookup (Φ := fun _ x => iprop(OK x)) hi) $$ H
    inext
    imod HAU with ⟨%σ, Hst, Hcl⟩
    imodintro
    iexists σ
    iframe Hst
    iintro Hst
    imod Hcl $$ Hst with HK
    imodintro
    iintro -
    wp_auto
    iapply HK; iexact Hsl

end proof

end cache
end EtcdGrove
end Perennial
