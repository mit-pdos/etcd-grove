module
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__hashmapFreeCountSlow

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

/-- The running sum of `hashmapFreeCountSlow`, one span more. -/
theorem fc_sum_step (S : Nat) (v : w64) :
    W64 ((S + uint.nat v : Nat) : Int) = W64 (S : Int) + v := by
  word

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem hashMap.hashmapFreeCountSlow.wp_proof :
    hashMap.hashmapFreeCountSlow.spec (GF := GF) (hG := hG) := by
  intro h s free
  wp_start as Hown
  unfold ownHashPart
  iNamed Hown
  unfold hmRaw
  iNamed Hraw
  obtain ⟨hok, hf, hmaps, hc, hlen⟩ := Hok
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (c sz : w64),
      "count" ∷ count_ptr ↦ c ∗ "size" ∷ size_ptr ↦ sz ∗
      "%Hi" ∷ ⌜0 ≤ i ∧ c = W64 (((keys.take i.toNat).map (spanLen sp)).sum : Int)⌝)) $$ Hfw
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [count size]
  · iexists _, _
    iframe
    ipureintro; exact ⟨Int.le_refl _, by simp⟩
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _, _
    iframe
    ipureintro
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    refine ⟨by omega, ?_⟩
    rw [Htake, List.map_append, List.sum_append, Hi.2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [show spanLen sp key = uint.nat v by unfold spanLen; rw [Hv]; rfl, fc_sum_step]
  iintro HP Hfw
  iNamed HP
  wp_auto
  rw [show (GMap.size sp : Int).toNat = keys.length by omega, List.take_length,
    spans_sum hok hf Hknodup Hkset] at Hi
  rw [Hi.2]
  iapply HΦ
  iexists cnt, sp, bwm, sets
  simp only [named]
  iframe
  ipureintro; exact ⟨hok, hf, hmaps, hc, hlen⟩

end proof

end bbolt
end EtcdGrove
end Perennial
