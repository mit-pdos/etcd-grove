/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/tokenSimple__invalidateUser.lean` (pr-verify etcd#22560, 2026-10-16).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.tokenSimple__invalidateUser
public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__deleteSimpleToken

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.tokenSimple.invalidateUser.wp_proof
    (h_del : auth.simpleTokenTTLKeeper.deleteSimpleToken.spec (GF := GF) (hG := hG)) :
    auth.tokenSimple.invalidateUser.spec (GF := GF) (hG := hG) := fun t γ γk A kp u => by
  wp_start as ⟨#Hts, Hadm⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTS at Hts
  icases Hts with ⟨%Htnn, -, #Hmu⟩
  iunfold tsAdmin at Hadm
  icases Hadm with ⟨Hkp1, HA1⟩
  wp_auto
  ipersist t
  ipersist username
  wp_if_destruct
  · iapply HΦ
    iunfold tsAdmin
    iframe
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HP⟩
  iunfold stLockP at HP
  icases HP with ⟨%kp', %A', %K, %ttl, Hkp, HA, Htab, Httl, HK, #HKe, HKm, Hcur⟩
  iunfold stTables at Htab
  icases Htab with ⟨%sp, %ep, %live, %exp, Hsp, Hspm, Hep, Hepm, %Hsub⟩
  icombine Hkp1 Hkp gives %Heq
  subst Heq
  ihave %HAeq := ghostVar_agree γ A _ A' _ $$ HA1 HA
  subst HAeq
  icases Hcur with (%Hnull | ⟨%HKkp, #Hro⟩)
  · exact absurd Hnull Hif
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun k (_ : Unit) => keeperMap (GF := GF) k) HKkp).1
    $$ HKm with ⟨Hkm, HKback⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range_mut_keys (fun (keys : List GoString) (i : Nat) (m' : GMap GoString GoString) =>
      iprop(∃ (nm tk : GoString),
        "name" ∷ name_ptr ↦ nm ∗ "token" ∷ token_ptr ↦ tk ∗
        "Hsp" ∷ tF go!"simpleTokens" t ↦ sp ∗ "Hkm" ∷ keeperMap kp ∗
        "Hkp" ∷ tF go!"simpleTokenKeeper" t ↦{DFrac.own (1 : Qp).half} kp ∗
        "%Hm" ∷ ⌜m' ⊆ live ∧ noUserBelow keys i m' u⌝))) $$ Hspm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [name token Hsp Hkm Hkp]
  · iexists _, _
    simp only [named]
    iframe
    ipureintro; exact ⟨fun _ _ h => h, noUserBelow_zero _ _ _⟩
  isplitr
  · imodintro
    iintro %i %key %v %m' ⟨%Hkey, %Hv, %Hagree⟩ HP Hm
    iNamed HP
    have Hv' : m' !! key = some v := by rw [Hagree i key (Nat.le_refl _) Hkey]; exact Hv
    wp_auto
    wp_if_destruct
    · wp_apply wp_mapDelete $$ [$Hm] as Hm
      wp_apply (h_del kp key) $$ [$Hkm] as Hkm
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      isplitl
      · iexists _, _
        simp only [named]
        iframe
        ipureintro
        exact ⟨subseteq_trans' (subseteq_delete key (fun _ _ h => h)) Hm.1,
          noUserBelow_delete keys i key m' u Hkey Hm.2⟩
      · ipureintro; intro k hk; exact GMap.lookup_delete_ne _ (Ne.symm hk)
    · unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      isplitl
      · iexists _, _
        simp only [named]
        iframe
        ipureintro
        exact ⟨Hm.1, noUserBelow_keep keys i key m' u v Hkey Hv' Hif Hm.2⟩
      · ipureintro; intro k _; rfl
  iintro %live' HP Hspm
  iNamed HP
  have Hlive' : ∀ k, live' !! k ≠ some u := noUserBelow_end keys live live' u Hkset Hm.1 Hm.2
  have Hlsub : live' ⊆ live := Hm.1
  clear Hm Hkset Hklen Hknodup keys
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range_mut_keys (fun (keys : List GoString) (i : Nat) (m' : GMap GoString GoString) =>
      iprop(∃ (nm tk : GoString),
        "name" ∷ name_ptr ↦ nm ∗ "token" ∷ token_ptr ↦ tk ∗
        "Hep" ∷ tF go!"expiredTokens" t ↦ ep ∗
        "%Hm" ∷ ⌜m' ⊆ exp ∧ noUserBelow keys i m' u⌝))) $$ Hepm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [name token Hep]
  · iexists _, _
    simp only [named]
    iframe
    ipureintro; exact ⟨fun _ _ h => h, noUserBelow_zero _ _ _⟩
  isplitr
  · imodintro
    iintro %i %key %v %m' ⟨%Hkey, %Hv, %Hagree⟩ HP Hm
    iNamed HP
    have Hv' : m' !! key = some v := by rw [Hagree i key (Nat.le_refl _) Hkey]; exact Hv
    wp_auto
    wp_if_destruct
    · wp_apply wp_mapDelete $$ [$Hm] as Hm
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      isplitl
      · iexists _, _
        simp only [named]
        iframe
        ipureintro
        exact ⟨subseteq_trans' (subseteq_delete key (fun _ _ h => h)) Hm.1,
          noUserBelow_delete keys i key m' u Hkey Hm.2⟩
      · ipureintro; intro k hk; exact GMap.lookup_delete_ne _ (Ne.symm hk)
    · unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      isplitl
      · iexists _, _
        simp only [named]
        iframe
        ipureintro
        exact ⟨Hm.1, noUserBelow_keep keys i key m' u v Hkey Hv' Hif Hm.2⟩
      · ipureintro; intro k _; rfl
  iintro %exp' HP Hepm
  iNamed HP
  have Hexp' : ∀ k, exp' !! k ≠ some u := noUserBelow_end keys exp exp' u Hkset Hm.1 Hm.2
  have Hesub : exp' ⊆ exp := Hm.1
  ihave HKm := HKback $$ Hkm
  imod ghostVar_update_halves (GMap.filter (fun _ v => decide (v ≠ u)) A) γ A A $$ HA1 HA
    with ⟨HA1, HA⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkp HA Httl HK HKm Hsp Hspm Hep Hepm]
  · inext
    iunfold stLockP
    iexists kp, (GMap.filter (fun _ v => decide (v ≠ u)) A), K, ttl
    iframe
    iframe HKe
    isplitl [Hsp Hspm Hep Hepm]
    · iunfold stTables
      iexists sp, ep, live', exp'
      iframe
      ipureintro
      exact ⟨subseteq_filter_user live' A u (subseteq_trans' Hlsub Hsub.1) Hlive',
        subseteq_filter_user exp' A u (subseteq_trans' Hesub Hsub.2) Hexp'⟩
    · iright; iframe #; ipureintro; exact HKkp
  iapply HΦ
  iunfold tsAdmin
  rw [if_neg Hif]
  iframe

end proof

end EtcdGrove
end Perennial
