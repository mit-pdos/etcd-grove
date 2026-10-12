module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__PendingCount

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.PendingCount.wp_proof : shared.PendingCount.spec (GF := GF) (hG := hG) := by
  intro s iface σ
  wp_start as Hs
  unfold ownShared ownSharedC
  icases Hs with ⟨%sv, %c, Hs, %Hok⟩
  iNamed Hs
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (tp : Loc),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp;σ.pending, ownPending p pd) ∗
      "count" ∷ count_ptr ↦
        W64 (((keys.take i.toNat).map (fun t => (σ.pendingOf t).ids.length)).sum : Int) ∗
      "txp" ∷ txp_ptr ↦ tp)) $$ Hpending
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hpds count txp]
  · iexists _
    simp only [Int.toNat_zero, List.take_zero, List.map_nil, List.sum_nil]
    iframe
    ipureintro; omega
  isplitr
  · imodintro
    iintro %i %key %p ⟨%Hkey, %Hp⟩ HP
    iNamed HP
    obtain ⟨pd, Hpd⟩ := Option.isSome_iff_exists.1
      ((Hdom key).1 (by simp only [show Std.get? pp key = some p from Hp, Option.isSome_some]))
    icases BigSepM2.bigSepM2_lookup_acc Hp Hpd $$ Hpds with ⟨Hpo, Hback⟩
    iNamed Hpo
    ihave %Hl := ownSlice_len _ _ _ $$ Hids
    wp_auto
    ihave Hpds := Hback $$ [Hp Hids Hids_cap Hatx Hatx_cap]
    · unfold ownPending; iexists tv; iframe; ipureintro; exact Hlrb
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists p
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    have Hpo : (σ.pendingOf key).ids.length = pd.ids.length := by
      simp [FLState.pendingOf, show σ.pending !! key = some pd from Hpd]
    rw [Htake, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Hpo, Nat.add_zero]
    have Hw : ∀ S : Nat, (W64 ((S + pd.ids.length : Nat) : Int) : w64) =
        W64 (S : Int) + tv.ids'.len := by intro S; word
    rw [Hw]
    iframe
    ipureintro; omega
  iintro HP Hpending
  iNamed HP
  rw [show (GMap.size pp : Int).toNat = keys.length by omega, List.take_length,
    pendingCount_keys σ keys (fun k => (Hkset k).trans (Hdom k)) Hknodup]
  wp_auto
  iapply HΦ
  iexists sv, c
  iframe
  ipureintro; exact ⟨Hiface, Hok⟩

end proof

end bbolt
end EtcdGrove
end Perennial
