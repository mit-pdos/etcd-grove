/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__SetEndpoints.lean` (PR #21765).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__SetEndpoints
public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver__SetEndpoints

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.SetEndpoints.wp_proof
    (_wp_rSetEndpoints : resolver.EtcdManualResolver.SetEndpoints.spec (GF := GF) (hG := hG)) :
    Client.SetEndpoints.spec (GF := GF) (hG := hG) := by
  intro c mu mref dq esl0 sl eps
  wp_start as ⟨#Hmu, #Hguard, Heps, Hchf, Hm, #Hsl⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hguard] as ⟨Hwl, -⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List GoString) (_ : Int) => iprop(True)) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitr
  · itrivial
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ _
    exfalso
    simp at Hvv
  iintro _ Hm
  wp_auto
  wp_apply sync.RWMutex.wp_Unlock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hwl]
  iapply HΦ
  iframe

theorem Client.SetEndpoints_singleton.wp_proof
    (wp_rSetEndpoints : resolver.EtcdManualResolver.SetEndpoints.spec (GF := GF) (hG := hG)) :
    Client.SetEndpoints_singleton.spec (GF := GF) (hG := hG) := by
  intro c mu mref conn r dq k₀ esl0 eps0 sl eps
  wp_start as ⟨#Hmu, #Hguard, Heps, Hchf, Hm, Hro, #Hsl⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hres : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hguard] as ⟨Hwl, -⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (i : Int) =>
    iprop(∃ (chv : go_etcd_io.etcd.client.v3.channel),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "ch" ∷ ch_ptr ↦ chv ∗
      "eps" ∷ eps_ptr ↦ sl ∗
      "Hro" ∷ etcdResolverOwn r (if k₀ ∈ keys.take i.toNat then eps else eps0))) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [ch eps Hro]
  · iexists _
    simp only [named, Int.toNat_zero, List.take_zero, List.not_mem_nil, ↓reduceIte]
    iframe
    ipureintro; exact Int.le_refl _
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    by_cases hk : k₀ = key
    · subst hk
      simp at Hvv
      subst Hvv
      wp_auto
      wp_apply wp_rSetEndpoints r (if k₀ ∈ keys.take i.toNat then eps else eps0) sl eps
        $$ [$Hres $Hro $Hsl] as Hro
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      simp only [named]
      have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [k₀] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega]
        rw [List.take_add_one, Hkey]; rfl
      have hmem : k₀ ∈ keys.take (i + 1).toNat := by
        rw [Htake]; simp
      simp only [hmem, ↓reduceIte]
      iframe
      ipureintro; omega
    · simp [hk] at Hvv
  iintro HP Hm
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length]
  have hkmem : k₀ ∈ keys := by
    rw [Hkset]
    simp
  simp only [hkmem, ↓reduceIte]
  wp_auto
  wp_apply sync.RWMutex.wp_Unlock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hwl]
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
