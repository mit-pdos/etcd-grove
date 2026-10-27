/-
Proof of `Spec/k8s_io/client_go/tools/cache/storeIndex__addIndexers.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.storeIndex__addIndexers
public import Spec.k8s_io.apimachinery.pkg.util.sets.KeySet
public import Spec.k8s_io.apimachinery.pkg.util.sets.List
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__HasAny
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Intersection
public import Proof.k8s_io.client_go.tools.cache.ErrorfSet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

/-- The entries of `m` at the keys `ks`. -/
def restrictF {V : Type} (m : GMap GoString V) (ks : List GoString) : GMap GoString V :=
  GMap.filter (fun k _ => decide (k ∈ ks)) m

theorem restrictF_nil {V : Type} (m : GMap GoString V) : restrictF m [] = ∅ := by
  ext k; unfold restrictF; rw [GMap.lookup_filter]; cases m !! k <;> simp [Option.filter]

theorem restrictF_all {V : Type} (m : GMap GoString V) (ks : List GoString)
    (h : ∀ k, k ∈ ks ↔ (m !! k).isSome) : restrictF m ks = m := by
  ext k; unfold restrictF; rw [GMap.lookup_filter]
  cases hk : m !! k with
  | none => rfl
  | some v => simp [Option.filter, (h k).2 (by rw [hk]; rfl)]

theorem restrictF_snoc {V : Type} (m fv : GMap GoString V) (ks : List GoString) (k : GoString)
    (v : V) (hv : m !! k = some v) :
    <[k := v]> (restrictF m ks ∪ fv) = restrictF m (ks ++ [k]) ∪ fv := by
  ext k'
  unfold restrictF
  by_cases hk : k = k'
  · subst hk; simp [GMap.lookup_filter, hv, Option.filter]
  · simp only [GMap.lookup_insert_eq_iff, hk, ↓reduceIte, GMap.lookup_union,
      GMap.lookup_filter, List.mem_append, List.mem_singleton]
    cases m !! k' <;> simp [Option.filter, Ne.symm hk]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem storeIndex.addIndexers.wp_proof
    (wp_KeySet : sets.KeySet.spec (GF := GF) (hG := hG))
    (wp_List : sets.List'.spec (GF := GF) (hG := hG))
    (wp_HasAny : sets.Set.HasAny.spec (GF := GF) (hG := hG))
    (wp_Intersection : sets.Set.Intersection.spec (GF := GF) (hG := hG)) :
    storeIndex.addIndexers.spec (GF := GF) (hG := hG) := by
  intro i im nm dqi dn fv nfv hsz
  wp_start as ⟨Hidx, Him, Hnm⟩
  ihave #Hsets : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_KeySet (T := go.string) (Vt := IndexFunc.ty) im (DFrac.own 1) fv) $$ [$Him]
    as %ok ⟨Him, Hok⟩
  (try wp_auto)
  wp_apply (wp_KeySet (T := go.string) (Vt := IndexFunc.ty) nm dn nfv) $$ [$Hnm]
    as %nk ⟨Hnm, Hnk⟩
  (try wp_auto)
  have hsz' : GMap.size (sets.keysOf nfv) ≤ 2 ^ 62 := by
    rw [GMap.size_eq_length (sets.keysOf nfv) nfv.domList (GMap.nodup_dom_list nfv)
      (fun k => by rw [GMap.mem_dom_list]; unfold sets.keysOf; simp),
      ← GMap.size_eq_dom_list_length]
    exact hsz
  wp_apply (wp_List nk (DFrac.own 1) (sets.keysOf nfv) hsz') $$ [$Hnk] as %sl %ks ⟨Hnk, Hks, %Hk⟩
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply (wp_HasAny (T := go.string) ok (DFrac.own 1) (sets.keysOf fv) sl (DFrac.own 1) ks)
    $$ [$Hok $Hks] as ⟨Hok, Hks⟩
  have hiff : (∃ k, k ∈ ks ∧ (Option.map (fun _ => sets.present) (fv !! k)).isSome = true) ↔
      nameClash fv nfv := by
    unfold nameClash
    constructor
    · rintro ⟨k, hk, hs⟩
      have := (Hk.1 k).1 hk
      unfold sets.keysOf at this
      simp only [GMap.lookup_fmap, Option.isSome_map] at this hs
      exact ⟨k, hs, this⟩
    · rintro ⟨k, h1, h2⟩
      refine ⟨k, (Hk.1 k).2 ?_, ?_⟩
      · unfold sets.keysOf; simpa [GMap.lookup_fmap] using h2
      · simpa using h1
  by_cases hc : nameClash fv nfv
  · rw [decide_eq_true (hiff.2 hc)]
    (try wp_auto)
    wp_method_call
    wp_call
    (try wp_auto)
    wp_apply (wp_Intersection (T := go.string) ok nk (DFrac.own 1) (DFrac.own 1)) $$ [$Hok $Hnk]
      as %r ⟨Hok, Hnk, %sr, Hr⟩
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply (wp_Errorf_setArgs _ _ _ (by
      intro a ha; simp only [List.mem_singleton] at ha; exact ⟨r, ha⟩)) $$ [$Hl1] as %err -
    (try wp_auto)
    iapply HΦ
    iframe
    ileft
    iframe
    ipureintro
    exact ⟨hc, fun h => by cases h⟩
  · rw [decide_eq_false (fun h => hc (hiff.1 h))]
    (try wp_auto)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List GoString) (p : Int) => iprop(∃ (x0 : GoString)
        (f0 : GoFunc),
        "%Hp" ∷ ⌜0 ≤ p⌝ ∗ "k" ∷ k_ptr ↦ x0 ∗ "v" ∷ v_ptr ↦ f0 ∗ "i" ∷ i_ptr ↦ i ∗
        "Hidx" ∷ structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗
        "Him" ∷ im ↦$ (restrictF nfv (keys.take p.toNat) ∪ fv))) $$ Hnm
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [k v i Hidx Him]
    · iexists _, _
      simp only [named]
      rw [Int.toNat_zero, List.take_zero, restrictF_nil, GMap.mapEmpty_union]
      iframe
      ipureintro; exact Int.le_refl _
    isplitr
    · imodintro
      iintro %p %k %f ⟨%Hkey, %Hf⟩ HP
      iNamed HP
      (try wp_auto)
      wp_apply (wp_mapInsert go.string im _ k f) $$ [$Him] as Him
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists k, f
      simp only [named]
      have Htake : keys.take (p + 1).toNat = keys.take p.toNat ++ [k] := by
        rw [show (p + 1).toNat = p.toNat + 1 by omega]
        rw [List.take_add_one, Hkey]; rfl
      rw [Htake, ← restrictF_snoc nfv fv _ k f Hf]
      iframe
      ipureintro; omega
    · iintro HP Hnm
      iNamed HP
      rw [← Hklen, Int.toNat_natCast, List.take_length, restrictF_all nfv keys Hkset]
      (try wp_auto)
      iapply HΦ
      iframe
      iright
      iframe
      ipureintro
      exact ⟨hc, rfl⟩

end proof

end cache
end EtcdGrove
end Perennial
