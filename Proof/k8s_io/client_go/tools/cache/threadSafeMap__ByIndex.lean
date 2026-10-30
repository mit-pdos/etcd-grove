/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__ByIndex.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__ByIndex
public import Spec.k8s_io.client_go.tools.cache.storeIndex__getKeysByIndex
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Len
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods

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

/-- `(*Set[string]).Len` on a `nil` set. -/
theorem set_ptr_Len_nil (l : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗
        l ↦ (null : Loc) }}
      (App (Val (l @!! go.GoType.PointerType
        (k8s_io.apimachinery.pkg.util.sets.Set'.ty go.string) @!! go!"Len")) (Val #()))
    {{ RET #(W64 0); l ↦ (null : Loc) }} := by
  wp_start as Hl
  wp_auto
  wp_method_call
  wp_call
  (try wp_auto)
  rw [show (null : Loc) = map.nil from rfl]
  wp_auto
  iapply HΦ; iframe

/-- `(*Set[string]).Len` on a set owned at any fraction, with the model's bound on its size. -/
theorem set_ptr_Len_lt (l m : Loc) (dq : DFrac) (S : KSet) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗
        l ↦ m ∗ m ↦${dq} S }}
      (App (Val (l @!! go.GoType.PointerType
        (k8s_io.apimachinery.pkg.util.sets.Set'.ty go.string) @!! go!"Len")) (Val #()))
    {{ RET #(W64 (GMap.size S)); l ↦ m ∗ m ↦${dq} S ∗ ⌜GMap.size S < 2 ^ 63⌝ }} := by
  wp_start as ⟨Hl, Hm⟩
  wp_auto
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply (wp_map_len_lt (t := k8s_io.apimachinery.pkg.util.sets.Set'.ty go.string) m S dq)
    $$ [$Hm] as ⟨Hm, %hlt⟩
  (try wp_auto)
  iapply HΦ; iframe; ipureintro; exact hlt

theorem threadSafeMap.ByIndex.wp_proof
    (wp_keys : storeIndex.getKeysByIndex.spec (GF := GF) (hG := hG)) :
    threadSafeMap.ByIndex.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam n v
  iintro %Φ ⟨#Hpkg, #Hc, Hrd⟩ HAU
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
  wp_apply (wp_keys γ.idx γ.im ph.ip DFrac.discard _ _ ph.fv (σ.fns Fam) ph.ix OK n v)
    $$ [$Him $Hfv $Hfns $Hind $Hix] as %s %err ⟨-, Hfv, Hind, Hix, %Hs⟩
  -- the state back to the lock and the reader slot, once committed
  cases hF : (σ.fns Fam) !! n with
  | none =>
    have hn : n ∉ σ.fns Fam := by rw [GMap.mem_iff, hF]; simp
    have herr := Hs.2 hn
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
      iunfold byIndexPost
      rw [hF]
      isplitr
      · ipureintro; exact herr
      iunfold tsReader; iexact Hrd
  | some F =>
    have hn : n ∈ σ.fns Fam := by rw [GMap.mem_iff, hF]; rfl
    obtain ⟨rfl, rfl⟩ := Hs.1 hn
    (try wp_auto)
    have hset := Hok.1.2 n hn
    icases (ownIx_set_acc ph.ip _ ph.ix n v) $$ Hix with (⟨%hsn, Hix⟩ | ⟨Hs, Hsc⟩)
    · -- no set: no keys
      obtain ⟨hsl, hsv⟩ := hsn
      rw [hsl]
      wp_apply set_ptr_Len_nil $$ [$Hsets $set] as set
      wp_apply (wp_slice_make3 (V := GoInterface) (W64 0) (W64 0) ⟨by word, by word⟩)
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
      iunfold byIndexPost
      iunfold tsReader
      rw [hF]
      dsimp only
      iframe Hrd
      isplitr
      · ipureintro; rfl
      iexists []
      simp only [List.map_nil, List.replicate_zero]
      isplitr
      · ipureintro; exact List.nodup_nil
      isplitr
      · iapply (idxSel_of _ σ.items iv n F (fun vs => v ∈ vs) [] hF Hok.2 (by simp)
          (fun k => ?_)) $$ Hiv
        have h := hset v k; unfold inIdx at h; rw [← h, hsv]
        simp [GMap.mem_iff]
      isplitl
      · iexact Hsl0
      · iapply BigSepL.bigSepL_nil.2; itrivial
    · -- the set's keys
      wp_apply set_ptr_Len_lt $$ [$Hsets $set $Hs] as ⟨set, Hs, %hlt⟩
      wp_apply (wp_slice_make3 (V := GoInterface) (W64 0)
        (W64 (GMap.size (viewN (ixAt ph.ix n) v))) ⟨by word, by word⟩)
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
          "key" ∷ key_ptr ↦ x ∗
          "c" ∷ c_ptr ↦ c ∗
          "Hitems" ∷ structFieldRef threadSafeMap go!"items" c ↦{DFrac.own sync.rfrac} ph.il ∗
          "Hil" ∷ ph.il ↦${DFrac.own sync.rfrac} σ.items)) $$ Hs
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [list Hsl0 Hcap0 key c Hitems Hil]
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
      have hks : ∀ k, k ∈ keys ↔ v ∈ ivAt iv n k := fun k =>
        (Hkset k).trans ((GMap.mem_iff _ _).symm.trans (hset v k))
      ihave #Hsel := idxSel_of _ σ.items iv n F (fun vs => v ∈ vs) keys hF Hok.2 (by simp) hks
        $$ Hiv
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
      iunfold byIndexPost
      iunfold tsReader
      rw [hF]
      dsimp only
      iframe Hrd
      isplitr
      · ipureintro; rfl
      iexists keys
      iframe
      iframe #
      ipureintro
      exact Hknodup


end proof

end cache
end EtcdGrove
end Perennial
