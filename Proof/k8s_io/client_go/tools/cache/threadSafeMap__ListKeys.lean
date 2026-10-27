/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__ListKeys.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__ListKeys

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

theorem threadSafeMap.ListKeys.wp_proof : threadSafeMap.ListKeys.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam
  iintro %Φ ⟨#Hpkg, #Hc, Hrd⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
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
  (try wp_auto)
  wp_apply (wp_map_len_lt (t := go.GoType.MapType go.string (go.GoType.InterfaceType []))
    ph.il σ.items _) $$ [$Hil] as ⟨Hil, %hlt⟩
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) (W64 (GMap.size σ.items))
    ⟨by word, by word⟩) as %sl0 ⟨Hsl0, Hcap0, -⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (p : Int) => iprop(∃ (sl : GoSlice)
      (x : GoString),
      "%Hp" ∷ ⌜0 ≤ p⌝ ∗
      "list" ∷ list_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* (keys.take p.toNat) ∗
      "Hcap" ∷ ownSliceCap GoString sl (DFrac.own 1) ∗
      "key" ∷ key_ptr ↦ x)) $$ Hil
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [list Hsl0 Hcap0 key]
  · iexists sl0, _
    simp only [named]
    iframe
    ipureintro
    exact Int.le_refl _
  isplitr
  · imodintro
    iintro %p %k %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_slice_literal (V := GoString) [k]
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
    rw [Htake]
    iframe
    ipureintro; omega
  iintro HP Hil
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length]
  imod storeSt_peek γ _ σ _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hgp Hitems Hrv Hind Hix Hfv Hil Hst]
  · inext
    iunfold tsP
    iexists σ, ph, iv
    iframe
    isplitl
    · iunfold tsPhys; iframe
    iframe #
    ipureintro; exact Hok
  iintro Hrd
  (try wp_auto)
  iapply HK
  iexists keys
  iframe
  isplitr
  · ipureintro
    exact ⟨Hknodup, fun k => (Hkset k).trans (GMap.mem_iff _ _).symm⟩
  iunfold tsReader; iexact Hrd

end proof

end cache
end EtcdGrove
end Perennial
