/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/LeaseQueue__Swap.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseQueue__Swap
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.LeaseQueue.Swap.wp_proof : lease.LeaseQueue.Swap.spec (GF := GF) (hG := hG) := by
  intro s xs i j hi0 hi1 hj0 hj1
  wp_start as Hq
  iunfold queueAt at Hq
  icases Hq with ⟨Hs, Hcap, Hits⟩
  ihave %Hlen := ownSlice_len s _ _ $$ Hs
  simp only [List.length_map] at Hlen
  have hj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨hj0, by word⟩
  have hi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := ⟨hi0, by word⟩
  have hiN : (sint.Z i).toNat < xs.length := by omega
  have hjN : (sint.Z j).toNat < xs.length := by omega
  have ha : xs[(sint.Z i).toNat]? = some xs[(sint.Z i).toNat] := List.getElem?_eq_getElem hiN
  have hb : xs[(sint.Z j).toNat]? = some xs[(sint.Z j).toNat] := List.getElem?_eq_getElem hjN
  generalize xs[(sint.Z i).toNat] = a at ha
  generalize xs[(sint.Z j).toNat] = b at hb
  have hsw : listSwap xs (sint.nat i) (sint.nat j) =
      (xs.set (sint.Z i).toNat b).set (sint.Z j).toNat a :=
    listSwap_eq xs _ _ a b ha hb
  rw [hsw]
  generalize hI : (sint.Z i).toNat = I at *
  generalize hJ : (sint.Z j).toNat = J at *
  have hpa : (xs.map Prod.fst)[I]? = some a.1 := by simp [ha]
  have hpb : (xs.map Prod.fst)[J]? = some b.1 := by simp [hb]
  -- the slice's two elements after the stores
  have hab : I = J → a = b := by intro h; subst h; rw [ha] at hb; cases hb; rfl
  have hgi : (((xs.map Prod.fst).set I b.1).set J a.1)[I]? = some b.1 := by
    by_cases h : I = J
    · subst h; simp [hiN, hab rfl]
    · rw [List.getElem?_set_ne (Ne.symm h)]; simp [hiN]
  have hgj : (((xs.map Prod.fst).set I b.1).set J a.1)[J]? = some a.1 := by simp [hjN]
  have hmap : ((xs.set I b).set J a).map Prod.fst = ((xs.map Prod.fst).set I b.1).set J a.1 := by
    simp [List.map_set]
  -- the two items' resources
  icases (BigSepL.bigSepL_delete_cond ha).1 $$ Hits with ⟨Ha, Hrest⟩
  wp_auto
  simp only [hi, _root_.and_self, ite_true]
  wp_auto
  simp only [hj, _root_.and_self, ite_true]
  wp_auto
  simp only [hj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index s (sint.Z j) (xs.map Prod.fst) _ b.1 hj0 $$ [Hs] as Hs
  · iframe; ipureintro; rw [hJ]; exact hpb
  (try wp_auto); (try simp only [hi, _root_.and_self, ite_true])
  wp_apply wp_load_slice_index s (sint.Z i) (xs.map Prod.fst) _ a.1 hi0 $$ [Hs] as Hs
  · iframe; ipureintro; rw [hI]; exact hpa
  wp_apply wp_store_slice_index s (sint.Z i) (xs.map Prod.fst) b.1 $$ [Hs] as Hs
  · iframe; ipureintro; simp only [List.length_map]; omega
  wp_apply wp_store_slice_index s (sint.Z j) ((xs.map Prod.fst).set (sint.Z i).toNat b.1) a.1
    $$ [Hs] as Hs
  · iframe; ipureintro; simp only [List.length_set, List.length_map]; omega
  rw [hI, hJ]
  (try wp_auto); (try simp only [hi, _root_.and_self, ite_true])
  wp_apply wp_load_slice_index s (sint.Z i) _ _ b.1 hi0 $$ [Hs] as Hs
  · iframe; ipureintro; rw [hI]; exact hgi
  by_cases hij : I = J
  · -- one item: `a = b`
    subst hij
    have hab' := hab rfl
    subst hab'
    iunfold lwtAt at Ha
    icases Ha with ⟨#Hid, Ht, Hix⟩
    wp_auto
    (try simp only [hj, _root_.and_self, ite_true])
    wp_apply wp_load_slice_index s (sint.Z j) _ _ a.1 hj0 $$ [Hs] as Hs
    · iframe; ipureintro; rw [hJ]; exact hgj
    iapply HΦ
    iunfold queueAt
    rw [hmap]
    iframe Hs Hcap
    have hset : (xs.set I a).set I a = xs := by
      rw [List.set_set]; exact list_set_lookup_self xs I a ha
    rw [hset]
    have hjw : (W64 (I : Int) : w64) = j := by rw [← hJ]; word
    iapply (BigSepL.bigSepL_delete_cond ha).2
    iframe Hrest
    iunfold lwtAt
    rw [hjw]
    iframe
    iframe #
  · -- two items
    icases (BigSepL.bigSepL_delete_cond
      (Φ := fun k y => if k = I then iprop(emp) else lwtAt (GF := GF) y.1 y.2 (W64 k) 1) hb).1 $$ Hrest
      with ⟨Hb, Hrest⟩
    have hJI : (J = I) = False := eq_false (Ne.symm hij)
    simp only [hJI, ite_false]
    iunfold lwtAt at Hb Ha
    icases Hb with ⟨#Hidb, Htb, Hixb⟩
    icases Ha with ⟨#Hida, Hta, Hixa⟩
    wp_auto
    (try simp only [hj, _root_.and_self, ite_true])
    wp_apply wp_load_slice_index s (sint.Z j) _ _ a.1 hj0 $$ [Hs] as Hs
    · iframe; ipureintro; rw [hJ]; exact hgj
    iapply HΦ
    iunfold queueAt
    rw [hmap]
    iframe Hs Hcap
    have hiw : (W64 (I : Int) : w64) = i := by rw [← hI]; word
    have hjw : (W64 (J : Int) : w64) = j := by rw [← hJ]; word
    have hL'I : ((xs.set I b).set J a)[I]? = some b := by
      rw [List.getElem?_set_ne (Ne.symm hij)]; simp [hiN]
    have hL'J : ((xs.set I b).set J a)[J]? = some a := by simp [hjN]
    iapply (BigSepL.bigSepL_delete_cond hL'I).2
    isplitl [Htb Hixb]
    · iunfold lwtAt; rw [hiw]; iframe; iframe #
    iapply (BigSepL.bigSepL_delete_cond
      (Φ := fun k y => if k = I then iprop(emp) else lwtAt (GF := GF) y.1 y.2 (W64 k) 1) hL'J).2
    simp only [hJI, ite_false]
    isplitl [Hta Hixa]
    · iunfold lwtAt; rw [hjw]; iframe; iframe #
    iapply (bigSepL_set_emp _ (xs.set I b) J a (by simpa using hjN) (fun y => by simp)).2
    iapply (bigSepL_set_emp _ xs I b hiN (fun y => by simp [hij])).2
    iexact Hrest

end proof

end EtcdGrove
end Perennial
