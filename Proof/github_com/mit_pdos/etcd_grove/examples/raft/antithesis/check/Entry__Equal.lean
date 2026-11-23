/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): the proof of `Entry.Equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Entry__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value__Equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Entry.Equal.wp_proof (wp_ValueEqual : Value.Equal.spec (GF := GF) (hG := hG)) :
    Entry.Equal.spec (GF := GF) (hG := hG) := by
  intro ge x gf y b
  wp_start as ⟨#Hx, #Hy, %Hb⟩
  iunfold entryRO at Hx Hy
  icases Hx with ⟨%Hx1, #Hxv⟩
  icases Hy with ⟨%Hy1, #Hyv⟩
  unfold Entry.equal at Hb
  obtain ⟨hxt, hxy⟩ := Hx1
  obtain ⟨hyt, hyy⟩ := Hy1
  wp_auto
  icases typedPointsto_split _ _ _ $$ e with Hef
  icases typedPointsto_split _ _ _ $$ f with Hff
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hef
  iNamed Hff
  try wp_auto
  by_cases ht : ge.Term' = gf.Term'
  · rw [decide_eq_true ht]
    try wp_auto
    by_cases hty : ge.Type' = gf.Type'
    · rw [decide_eq_true hty]
      try wp_auto
      rw [ite_eq_right (by
        intro h; rcases h with h | h
        · exact h (by rw [← hxt, ← hyt, ht])
        · exact h (by rw [← hxy, ← hyy, hty]))] at Hb
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value.TypeAssumptions.ptr_Equal_unfold.method_unfold]
      try wp_auto
      wp_apply wp_ValueEqual _ _ _ _ _ $$ [Hxv Hyv] as -
      · iframe Hxv Hyv; ipureintro; exact Hb
      try wp_auto
      iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false hty]
      try wp_auto
      rw [ite_eq_left (.inr (by rw [← hxy, ← hyy]; exact hty))] at Hb
      cases Hb
      iapply HΦ; ipureintro; trivial
  · rw [decide_eq_false ht]
    try wp_auto
    rw [ite_eq_left (.inl (by rw [← hxt, ← hyt]; exact fun h => ht (by word)))] at Hb
    cases Hb
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
