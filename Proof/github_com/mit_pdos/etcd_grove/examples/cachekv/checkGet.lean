/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/cachekv/checkGet.lean` (2026-11-02): the
first loop's `lastVal` of each key-value's key is its value (`CheckGetOk`'s first half), the second
loop's `hasKey` of each event's key at or below `r` true (its second half): no panic.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.checkGet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.cachekv go_etcd_io.etcd.cache.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

theorem checkGet.wp_proof
    (wp_lastVal : lastVal.spec (GF := GF) (hG := hG))
    (wp_hasKey : hasKey.spec (GF := GF) (hG := hG)) :
    checkGet.spec (GF := GF) (hG := hG) := by
  intro esl evs r ksl ps s Hok
  wp_start as ⟨#He, #Hk, #Hh⟩
  ihave %Hel := ownSlice_len $$ He
  ihave %Hkl := ownSlice_len $$ Hk
  ihave #Hh' := Hh
  iunfold kvsHold at Hh'
  icases Hh' with ⟨%Hlen, #Hkv⟩
  wp_auto
  -- the key-values: each one's value its key's last
  ihave HI : (∃ (j : w64) (p0 : Loc),
      "i" ∷ i_ptr ↦ j ∗ "kv" ∷ kv_ptr ↦ p0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ksl.len⌝ : IProp GF) $$ [i kv]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ksl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem ps (sint.nat j) as p
    obtain ⟨v, hv⟩ : ∃ v, s[sint.nat j]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact (List.getElem?_eq_some_iff.1 Hp_lookup).1)⟩
    wp_apply wp_load_slice_index ksl (sint.Z j) ps DFrac.discard p Hj.1 $$ [Hk] as -
    · iframe #; ipureintro; exact Hp_lookup
    ihave #Hv := Hkv $$ %(sint.nat j) %p %v %Hp_lookup %hv
    iunfold kvValAt at Hv
    icases Hv with ⟨%keySl, %valSl, #HkF, #HkS, -, -, -, #HvF, #HvS, -⟩
    (try wp_auto)
    wp_apply wp_bytes_to_string keySl v.key DFrac.discard $$ [HkS] as -
    · iframe #
    (try wp_auto)
    wp_apply (wp_lastVal esl evs DFrac.discard v.key r) $$ [He] as %lv %lok ⟨-, %Hlv⟩
    · iframe #
    have Hlast := Hok.1 v (List.mem_of_getElem? hv)
    rw [← Hlv] at Hlast
    have Hlok : lok = true := by cases lok <;> simp_all
    subst Hlok
    simp only [↓reduceIte, Option.some.injEq] at Hlast
    subst Hlast
    (try wp_auto)
    wp_apply wp_bytes_to_string valSl v.value DFrac.discard $$ [HvS] as -
    · iframe #
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, _
    iframe
    ipureintro; constructor <;> word
  -- the events: each key at or below `r` among the key-values
  (try wp_auto)
  ihave HJ : (∃ (j : w64) (e0 : cev),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z esl.len⌝ : IProp GF) $$ [i e]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HJ
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z esl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem evs (sint.nat j) as x
    wp_apply wp_load_slice_index esl (sint.Z j) evs DFrac.discard x Hj.1 $$ [He] as -
    · iframe #; ipureintro; exact Hx_lookup
    (try wp_auto)
    wp_if_destruct
    · wp_apply (wp_hasKey ksl ps s x.Key') $$ [] as %b %Hb
      · iframe #
      obtain ⟨kv, hkv, hkk⟩ := Hok.2 x (List.mem_of_getElem? Hx_lookup) Hif
      have : b = true := Hb.2 ⟨kv, hkv, hkk⟩
      subst this
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _
      iframe
      ipureintro; constructor <;> word
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _
      iframe
      ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ; itrivial

end proof

end cachekv
end EtcdGrove
end Perennial
