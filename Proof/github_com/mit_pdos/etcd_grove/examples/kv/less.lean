/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/less.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.less

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

theorem less.wp_proof : less.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  try wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro; word
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hla
  wp_if_destruct
  · have Hia : sint.Z i < sint.Z (W64 (a.length : Int)) := Hif
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlb
    try wp_auto
    by_cases hb : sint.Z i < sint.Z (W64 (b.length : Int))
    · rw [decide_eq_true hb, if_pos (by simp)]
      have Hia' : sint.nat i < a.length := by word
      have Hib : sint.nat i < b.length := by word
      obtain ⟨ca, Hca⟩ : ∃ c, a[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem Hia'⟩
      obtain ⟨cb, Hcb⟩ : ∃ c, b[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem Hib⟩
      repeat (first | (simp only [Hi, ↓reduceIte, Hca, Hcb]) | wp_auto)
      wp_if_destruct
      all_goals repeat (first | (simp only [Hi, ↓reduceIte, Hca, Hcb]) | wp_auto)
      all_goals first
        | (wp_for_post; iapply HΦ; done)
        | (wp_for_post; iapply HΦ; ipureintro; trivial)
        | (wp_for_post
           iframe
           iexists i + W64 1
           iframe
           ipureintro; word)
    · rw [decide_eq_false hb, if_neg (by
          simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
        if_pos (by simp)]
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      try wp_auto
      iapply HΦ
      ipureintro; trivial
  · try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    iapply HΦ
    ipureintro; trivial

end proof

end kv
end EtcdGrove
end Perennial
