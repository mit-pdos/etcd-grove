/-
Proof of `Spec/k8s_io/client_go/tools/cache/storeIndex__updateIndices.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.storeIndex__updateIndices
public import Spec.k8s_io.client_go.tools.cache.storeIndex__updateSingleIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem storeIndex.updateIndices.wp_proof
    (wp_upd1 : storeIndex.updateSingleIndex.spec (GF := GF) (hG := hG)) :
    storeIndex.updateIndices.spec (GF := GF) (hG := hG) := by
  intro i im ip dqi qm fv fns ix OK iv key old new
  wp_start as ⟨Hixr, Him, #Hfns, #Hold, #Hnew, #Hovs, Hipr, Hix, %hok⟩
  icases (fvMap_halves im fv qm).1 $$ Him with ⟨Him1, Him2⟩
  iunfold fnsOk at Hfns
  icases Hfns with ⟨%hdom, #Hfv⟩
  iunfold valsOk at Hovs
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (p : Int) => iprop(∃ (x : GoString)
      (ixp : Ix) (vs : Vals),
      "%Hp" ∷ ⌜0 ≤ p⌝ ∗
      "%Hok" ∷ ⌜ixOk fns (<[key := vs]> iv) ixp⌝ ∗
      "%Hrest" ∷ ⌜∀ n, n ∉ keys.take p.toNat → vsAt vs n = ivAt iv n key⌝ ∗
      "#Hdone" ∷ □ (∀ (n : GoString) (F : Fn GF), ⌜fns !! n = some F ∧ n ∈ keys.take p.toNat⌝ -∗
        objVals F new (vsAt vs n)) ∗
      "name" ∷ name_ptr ↦ x ∗
      "oldObj" ∷ oldObj_ptr ↦ old ∗ "newObj" ∷ newObj_ptr ↦ new ∗ "key" ∷ key_ptr ↦ key ∗
      "i" ∷ i_ptr ↦ i ∗
      "Hixr" ∷ structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗
      "Him2" ∷ im ↦${DFrac.own qm.half} fv ∗
      "Hipr" ∷ structFieldRef storeIndex go!"indices" i ↦ ip ∗
      "Hix" ∷ ownIx ip (DFrac.own 1) ixp)) $$ Him1
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [name oldObj newObj key i Hixr Him2 Hipr Hix]
  · iexists _, ix, ivOf iv key
    simp only [named]
    iframe
    isplitr
    · ipureintro; exact Int.le_refl _
    isplitr
    · ipureintro; exact ixOk_congr hok (fun n _ k => ivAt_insert_self iv key n k)
    isplitr
    · ipureintro; exact fun n _ => rfl
    · imodintro
      iintro %n %F %h
      simp at h
  isplitr
  · imodintro
    iintro %p %nm %f ⟨%Hkey, %Hf⟩ HP
    iNamed HP
    ihave ⟨%F, %hF, #Hfn⟩ := BigSepM.bigSepM_lookup Hf $$ Hfv
    have hnd : nm ∉ keys.take p.toNat := by
      intro hm
      have hd : nm ∈ keys.drop p.toNat := by
        rw [List.mem_iff_getElem?]
        exact ⟨0, by rw [List.getElem?_drop]; simpa using Hkey⟩
      have hnod := List.nodup_append.1 ((List.take_append_drop p.toNat keys).symm ▸ Hknodup)
      exact hnod.2.2 nm hm nm hd rfl
    ihave #Hov := BigSepM.bigSepM_lookup hF $$ Hovs
    have hov : vsAt (ivOf iv key) nm = vsAt vs nm := (Hrest nm hnd).symm
    rw [hov]
    wp_auto
    wp_apply wp_upd1 $$ [$Hixr $Him2 $Hipr $Hix]
      as ⟨%ix', %nvs, Hixr, Him2, Hipr, Hix, #Hnvs, %hix'⟩
    · iframe; iframe #; ipureintro; exact Hf
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    have Htake : keys.take (p + 1).toNat = keys.take p.toNat ++ [nm] := by
      rw [show (p + 1).toNat = p.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    iexists nm, ix', <[nm := nvs]> vs
    simp only [named]
    iframe
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro
      have hname : nm ∈ fns := by rw [GMap.mem_iff, hF]; rfl
      exact ixOk_step Hok hname hix'.1 hix'.2
    isplitr
    · ipureintro
      intro n hn
      rw [Htake] at hn
      have hn1 : n ≠ nm := by intro h; subst h; simp at hn
      rw [vsAt_insert]; simp only [hn1, ↓reduceIte]
      exact Hrest n (fun h => hn (List.mem_append_left _ h))
    · imodintro
      iintro %n %G ⟨%hG, %hn⟩
      rw [Htake] at hn
      rw [vsAt_insert]
      by_cases hnn : n = nm
      · subst hnn
        rw [hF] at hG; cases hG
        simp only [↓reduceIte]
        iexact Hnvs
      · simp only [hnn, ↓reduceIte]
        have hn' : n ∈ keys.take p.toNat := by simpa [hnn] using hn
        iapply Hdone $$ %n %G
        ipureintro; exact ⟨hG, hn'⟩
  iintro HP Hm
  iNamed HP
  have hall : keys.take (GMap.size fv : Int).toNat = keys := by
    rw [Int.toNat_natCast, ← Hklen, List.take_length]
  wp_auto
  iapply HΦ
  iexists ixp, vs
  iframe
  isplitl [Hm Him2]
  · iapply (fvMap_halves im fv qm).2; iframe
  isplitr
  · iunfold valsOk
    iapply (BigSepM.bigSepM_intro (P := iprop(□ (∀ (n : GoString) (F : Fn GF),
        ⌜fns !! n = some F ∧ n ∈ keys.take (GMap.size fv : Int).toNat⌝ -∗
          objVals F new (vsAt vs n))))
        (fun {n F} hn => ?_)) $$ [Hdone]
    · iintro #H
      iapply H $$ %n %F
      ipureintro
      refine ⟨hn, ?_⟩
      rw [hall]
      refine (Hkset n).2 ((hdom n).1 ?_)
      rw [GMap.mem_iff, show fns !! n = some F from hn]; rfl
    · iexact Hdone
  · ipureintro
    refine ⟨Hok, fun n hn => Hrest n ?_⟩
    rw [hall]
    intro hk
    exact hn ((hdom n).2 (by have := (Hkset n).1 hk; rw [GMap.mem_iff]; exact this))

end proof

end cache
end EtcdGrove
end Perennial
