/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__Index.lean`. Lean-first: as `ByIndex`'s
proof, over `getKeysFromIndex`'s set.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Index
public import Spec.k8s_io.client_go.tools.cache.storeIndex__getKeysFromIndex
public import Proof.k8s_io.client_go.tools.cache.threadSafeMap__ByIndex

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

theorem threadSafeMap.Index.wp_proof
    (wp_keys : storeIndex.getKeysFromIndex.spec (GF := GF) (hG := hG)) :
    threadSafeMap.Index.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam n obj
  iintro %Φ ⟨#Hpkg, #Hc, Hrd, #HOK⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hsets : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets $$ []
  · iPkgInit
  iunfold isTS at Hc
  icases Hc with ⟨%mp, %g, #Hidx, #Him, #Hmp, #Hg, #Hgok, #Hguard⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  iunfold tsReader at Hrd
  wp_apply (lc := 2) sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  iunfold tsP at HP
  icases HP with ⟨%σ, %ph, %iv, Hst, Hgp, Hph, #Hpers, %Hok⟩
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrv, Hind, Hix, Hfv⟩
  iunfold tsPers at Hpers
  icases Hpers with ⟨#Hfns, #Hits, #Hiv⟩
  (try wp_auto)
  wp_apply (wp_keys γ.idx γ.im ph.ip DFrac.discard _ _ ph.fv (σ.fns Fam) ph.ix OK n obj)
    $$ [$Him $Hfv $Hfns $Hind $Hix $HOK] as %s %err ⟨-, Hfv, Hind, Hpost⟩
  cases hF : (σ.fns Fam) !! n with
  | none =>
    have e : Option.map Fam (σ.fnIds !! n) = none := by rw [← hF]; simp [St.fns]
    rw [e]
    icases Hpost with ⟨%herr, Hix⟩
    cases err with
    | nil => exact absurd rfl herr
    | ok e =>
      (try wp_auto)
      imod storeSt_peek γ _ σ _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hgp Hitems Hrv Hind Hix Hfv Hil Hst]
      · inext
        iunfold tsP
        iexists σ, ph, iv
        iframe
        isplitl
        · iunfold tsPhys; iframe
        isplitr
        · iunfold tsPers; iframe #
        · ipureintro; exact Hok
      iintro Hrd
      (try wp_auto)
      iapply HK
      iunfold indexPost
      rw [hF]
      isplitr
      · ipureintro; exact herr
      iunfold tsReader; iexact Hrd
  | some F =>
    have e : Option.map Fam (σ.fnIds !! n) = some F := by rw [← hF]; simp [St.fns]
    rw [e]
    icases Hpost with ⟨%herr, %S, %vq, %HS, #HFq, Hres⟩
    subst herr
    (try wp_auto)
    have hn : n ∈ σ.fns Fam := by rw [GMap.mem_iff, hF]; rfl
    have hset := Hok.1.2 n hn
    have hkeys : ∀ k, k ∈ S ↔ ∃ v ∈ vq, v ∈ ivAt iv n k := fun k =>
      (HS k).trans ⟨fun ⟨v, hv, hk⟩ => ⟨v, hv, (hset v k).1 hk⟩,
        fun ⟨v, hv, hk⟩ => ⟨v, hv, (hset v k).2 hk⟩⟩
    iunfold setRes at Hres
    icases Hres with (⟨%hsn, Hix⟩ | ⟨%dq', Hs, Hsc⟩)
    · -- no set: no keys
      obtain ⟨hsl, hsv⟩ := hsn
      subst hsl hsv
      wp_apply set_ptr_Len_nil $$ [$Hsets $storeKeySet] as storeKeySet
      have h00 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) := by word
      wp_apply (wp_slice_make3 (V := GoInterface) (W64 0) (W64 0) h00)
        as %sl0 ⟨Hsl0, Hcap0, -⟩
      (try wp_auto)
      rw [show (null : Loc) = map.nil from rfl]
      wp_func_lits
      (try wp_auto)
      imod storeSt_peek γ _ σ _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hgp Hitems Hrv Hind Hix Hfv Hil Hst]
      · inext
        iunfold tsP
        iexists σ, ph, iv
        iframe
        isplitl
        · iunfold tsPhys; iframe
        isplitr
        · iunfold tsPers; iframe #
        · ipureintro; exact Hok
      iintro Hrd
      (try wp_auto)
      iapply HK
      iunfold indexPost
      iunfold tsReader
      rw [hF]
      dsimp only
      iframe Hrd
      isplitr
      · ipureintro; rfl
      iexists vq, []
      simp only [List.map_nil, List.replicate_zero]
      isplitr
      · ipureintro; exact List.nodup_nil
      isplitr
      · iexact HFq
      isplitr
      · iapply (idxSel_of _ σ.items iv n F (fun vs => ∃ v ∈ vq, v ∈ vs) [] hF Hok.2 (by simp)
          (fun k => ?_)) $$ Hiv
        rw [← hkeys k]
        simp [GMap.mem_iff]
      isplitl
      · iexact Hsl0
      · iapply BigSepL.bigSepL_nil.2; itrivial
    · -- the set's keys
      wp_apply set_ptr_Len_lt $$ [$Hsets $storeKeySet $Hs] as ⟨storeKeySet, Hs, %hlt⟩
      have h0S : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (GMap.size S)) := by word
      wp_apply (wp_slice_make3 (V := GoInterface) (W64 0) (W64 (GMap.size S)) h0S)
        as %sl0 ⟨Hsl0, Hcap0, -⟩
      (try wp_auto)
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (fun (keys : List GoString) (p : Int) => iprop(∃ (sl : GoSlice)
          (x : GoString),
          "%Hp" ∷ ⌜0 ≤ p⌝ ∗
          "list" ∷ list_ptr ↦ sl ∗
          "Hsl" ∷ sl ↦* ((keys.take p.toNat).map (objAt σ.items)) ∗
          "Hcap" ∷ ownSliceCap GoInterface sl (DFrac.own 1) ∗
          "key" ∷ storeKey_ptr ↦ x ∗
          "c" ∷ c_ptr ↦ c ∗
          "Hitems" ∷ structFieldRef threadSafeMap go!"items" c ↦{DFrac.own sync.rfrac} ph.il ∗
          "Hil" ∷ ph.il ↦${DFrac.own sync.rfrac} σ.items)) $$ Hs
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [list Hsl0 Hcap0 storeKey c Hitems Hil]
      · iexists sl0, _
        simp only [named]
        iframe
        ipureintro
        exact Int.le_refl _
      isplitr
      · imodintro
        iintro %p %k %e ⟨%Hkey, %He⟩ HP
        iNamed HP
        wp_auto
        wp_apply (wp_map_lookup1 go.string (go.GoType.InterfaceType []) ph.il σ.items k)
          $$ [$Hil] as Hil
        (try wp_auto)
        wp_apply wp_slice_literal (V := GoInterface) [(σ.items !! k).getD GoInterface.nil]
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        (try wp_auto)
        wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
        (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists sl', k
        simp only [named]
        iframe
        have Htake : keys.take (p + 1).toNat = keys.take p.toNat ++ [k] := by
          rw [show (p + 1).toNat = p.toNat + 1 by omega]
          rw [List.take_add_one, Hkey]; rfl
        rw [Htake, List.map_append, List.map_singleton]
        iframe
        ipureintro; omega
      iintro HP Hs
      iNamed HP
      rw [Int.toNat_natCast, ← Hklen, List.take_length]
      imod storeSt_peek γ _ σ _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
      (try wp_auto)
      have hks : ∀ k, k ∈ keys ↔ ∃ v ∈ vq, v ∈ ivAt iv n k := fun k =>
        (Hkset k).trans ((GMap.mem_iff _ _).symm.trans (hkeys k))
      ihave #Hsel := idxSel_of _ σ.items iv n F (fun vs => ∃ v ∈ vq, v ∈ vs) keys hF Hok.2
        (by simp) hks $$ Hiv
      ihave %hin : ⌜∀ k, k ∈ keys → k ∈ σ.items⌝ $$ []
      · iunfold idxSel at Hsel; icases Hsel with ⟨%h, -⟩; ipureintro; exact h
      ihave #Hoks := okNil_of_keys OK σ.items keys hin $$ Hits
      ihave Hix := Hsc $$ Hs
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hgp Hitems Hrv Hind Hix Hfv Hil Hst]
      · inext
        iunfold tsP
        iexists σ, ph, iv
        iframe
        isplitl
        · iunfold tsPhys; iframe
        isplitr
        · iunfold tsPers; iframe #
        · ipureintro; exact Hok
      iintro Hrd
      (try wp_auto)
      iapply HK
      iunfold indexPost
      iunfold tsReader
      rw [hF]
      dsimp only
      iframe Hrd
      isplitr
      · ipureintro; rfl
      iexists vq, keys
      iframe
      iframe #
      ipureintro
      exact Hknodup

end proof

end cache
end EtcdGrove
end Perennial
