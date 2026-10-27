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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem storeIndex.updateIndices.wp_proof
    (wp_upd1 : storeIndex.updateSingleIndex.spec (GF := GF) (hG := hG)) :
    storeIndex.updateIndices.spec (GF := GF) (hG := hG) := by
  intro i im ip dqi qm fv fns ix OK it it' key old new
  wp_start as ⟨Hixr, Him, #Hfns, #Hold, #Hnew, Hipr, Hix, %hpre⟩
  obtain ⟨hok, hold, hnew, hsame⟩ := hpre
  icases (fvMap_halves im fv qm).1 $$ Him with ⟨Him1, Him2⟩
  iunfold fnsOk at Hfns
  icases Hfns with ⟨%hdom, #Hfv⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (p : Int) => iprop(∃ (x : GoString) (ixp : Ix),
      "%Hp" ∷ ⌜0 ≤ p⌝ ∗
      "%Hok" ∷ ⌜ixOkPart fns it it' (keys.take p.toNat) ixp⌝ ∗
      "name" ∷ name_ptr ↦ x ∗
      "oldObj" ∷ oldObj_ptr ↦ old ∗ "newObj" ∷ newObj_ptr ↦ new ∗ "key" ∷ key_ptr ↦ key ∗
      "i" ∷ i_ptr ↦ i ∗
      "Hixr" ∷ structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗
      "Him2" ∷ im ↦${DFrac.own qm.half} fv ∗
      "Hipr" ∷ structFieldRef storeIndex go!"indices" i ↦ ip ∗
      "Hix" ∷ ownIx ip (DFrac.own 1) ixp)) $$ Him1
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [name oldObj newObj key i Hixr Him2 Hipr Hix]
  · iexists _, ix
    simp only [named]
    iframe
    ipureintro
    exact ⟨Int.le_refl _, ixOkPart_nil hok⟩
  isplitr
  · imodintro
    iintro %p %nm %f ⟨%Hkey, %Hf⟩ HP
    iNamed HP
    ihave ⟨%F, %hF, #Hfn⟩ := BigSepM.bigSepM_lookup Hf $$ Hfv
    wp_auto
    wp_apply wp_upd1 $$ [$Hixr $Him2 $Hipr $Hix] as ⟨%ix', Hixr, Him2, Hipr, Hix, %hix'⟩
    · iframe; iframe #; ipureintro; exact Hf
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists nm, ix'
    simp only [named]
    iframe
    ipureintro
    refine ⟨by omega, ?_⟩
    have Htake : keys.take (p + 1).toNat = keys.take p.toNat ++ [nm] := by
      rw [show (p + 1).toNat = p.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake]
    have hnd : nm ∉ keys.take p.toNat := by
      intro hm
      have hd : nm ∈ keys.drop p.toNat := by
        rw [List.mem_iff_getElem?]
        exact ⟨0, by rw [List.getElem?_drop]; simpa using Hkey⟩
      have hnod := List.nodup_append.1 ((List.take_append_drop p.toNat keys).symm ▸ Hknodup)
      exact hnod.2.2 nm hm nm hd rfl
    rw [hold, hnew] at hix'
    exact ixOkPart_step Hok hF hnd hsame hix'.1 hix'.2
  iintro HP Hm
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hok
  wp_auto
  iapply HΦ
  iexists ixp
  iframe
  isplitl [Hm Him2]
  · iapply (fvMap_halves im fv qm).2; iframe
  · ipureintro
    refine ixOkPart_done Hok (fun n hn => ?_)
    have := (hdom n).1 hn
    exact (Hkset n).2 this

end proof

end cache
end EtcdGrove
end Perennial
