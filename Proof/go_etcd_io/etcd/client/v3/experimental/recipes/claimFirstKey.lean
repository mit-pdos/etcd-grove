/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/claimFirstKey.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.claimFirstKey
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.deleteRevKey

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem claimFirstKey.wp_proof (hDRK : deleteRevKey.spec (GF := GF) (hG := hG)) :
    claimFirstKey.spec (GF := GF) (hG := hG) := by
  intro kv pfx sl ps vs lo
  wp_start as ⟨#Hkv, #Hlo, #Hsl, #Hps, %Hvs⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave #Hps' := Hps
  iunfold kvPtrsAt at Hps'
  icases Hps' with ⟨%Hpvl, #Hpv⟩
  wp_auto
  ihave IH : iprop(∃ (n : w64) (k0 : Loc),
      "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ k0 ∗
      "#Hcb" ∷ claimedBefore pfx lo vs (sint.nat n) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ps.length : Int)⌝) $$ [i k]
  · iexists W64 0, _
    simp only [named]
    iframe
    isplitl
    · unfold claimedBefore
      isplitl
      · ipureintro; simp
      imodintro
      iintro %j %v ⟨%Hj, -⟩
      exfalso; simp at Hj; omega
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z sl.len := by simpa using Hif
    have Hlt : sint.nat n < ps.length := by word
    obtain ⟨p, Hp⟩ : ∃ p, ps[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨v, Hv⟩ : ∃ v, vs[sint.nat n]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hpvl]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z n) p sl DFrac.discard ps Hn.1 Hp $$ Hsl with ⟨#Hpe, -⟩
    ihave #Hkvp := Hpv $$ %(sint.nat n) %p %v %Hp %Hv
    ihave #Hkvp' := Hkvp
    iunfold kvValAt at Hkvp'
    icases Hkvp' with ⟨%keySl, %valSl, #HK, #HKs, -, #HM, -⟩
    have Hvv := Hvs v (List.mem_of_getElem? Hv)
    wp_auto
    wp_apply wp_bytes_to_string keySl v.key DFrac.discard $$ [$HKs] as -
    (try wp_auto)
    wp_apply hDRK kv pfx v.key v.modRev lo $$ [$Hpkg $Hkv $Hlo] as %ok %err Hres
    · ipureintro; exact Hvv
    icases Hres with (⟨%Heq, %r, #Hr, %Hrr, Hc⟩ | %Hne)
    · subst Heq
      cases ok
      · -- gone: on to the next one
        simp only [Bool.false_eq_true, ↓reduceIte]
        iunfold revKeyGone at Hc
        icases Hc with ⟨%sg, #Hsg, %Hg⟩
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        simp only [named]
        iframe
        isplitl
        · unfold claimedBefore
          icases Hcb with ⟨-, #Hcb⟩
          isplitl
          · ipureintro; word
          imodintro
          iintro %j %w ⟨%Hj, %Hw⟩
          by_cases hjn : j < sint.nat n
          · iapply Hcb $$ %j %w; ipureintro; exact ⟨hjn, Hw⟩
          · have hj : j = sint.nat n := by
              have : sint.nat (n + W64 1) = sint.nat n + 1 := by word
              omega
            subst hj
            rw [Hv] at Hw; cases Hw
            iexists r
            iframe Hr
            unfold revKeyGone
            isplitl
            · iexists sg; iframe Hsg; ipureintro; exact Hg
            ipureintro; exact Hrr.1
        ipureintro; constructor <;> word
      · -- claimed
        simp only [↓reduceIte]
        icases Hc with ⟨Hc, Htok⟩
        iunfold revKeyDeleted at Hc
        icases Hc with ⟨%sd, %sd', #Hsd, #Hsd', %Hd⟩
        wp_auto
        wp_for_post
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        iexists sint.nat n
        iframe Hcb
        iright
        iexists v, r
        iframe Hkvp Hr
        isplitr
        · ipureintro; exact ⟨Hp, Hv⟩
        isplitr
        · unfold revKeyDeleted; iexists sd, sd'; iframe Hsd Hsd'; ipureintro; exact Hd
        iframe Htok
        ipureintro; exact Hrr.1
    · obtain ⟨Hne, rfl⟩ := Hne
      obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok e => exact ⟨e, rfl⟩
      wp_auto
      wp_for_post
      iapply HΦ
      iright
      ipureintro; exact ⟨Hne, rfl⟩
  · have Hif' : ¬ sint.Z n < sint.Z sl.len := by simpa using Hif
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists sint.nat n
    iframe Hcb
    ileft
    ipureintro
    refine ⟨rfl, ?_⟩
    rw [← Hpvl]; word

end proof

end recipes
end EtcdGrove
end Perennial
