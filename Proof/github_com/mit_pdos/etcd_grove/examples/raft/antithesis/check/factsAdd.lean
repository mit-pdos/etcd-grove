/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `factsAdd`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsAdd
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsHas

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

theorem factsAdd.wp_proof (wp_factsHas : factsHas.spec (GF := GF) (hG := hG)) :
    factsAdd.spec (GF := GF) (hG := hG) := by
  intro sl xs g x
  wp_start as ⟨#Hs, %Hgx, %Hb⟩
  ihave #Hs0 := Hs
  iunfold factsRO at Hs0
  icases Hs0 with ⟨%gs, #Hgs, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  have Hl := Hrel.length_eq
  iapply wp_fupd
  wp_auto
  wp_apply wp_factsHas sl xs g x $$ [Hs]
  · iframe Hs; ipureintro; exact Hgx
  cases hc : xs.contains x
  · try wp_auto
    wp_apply (wp_slice_make3 (V := G.Fact) (W64 0) (sl.len + W64 1) ⟨by word, by word⟩) as %o ⟨Ho, Hocap, -⟩
    try wp_auto
    wp_apply wp_slice_append o _ sl gs DFrac.discard $$ [Ho Hocap Hgs] as %o1 ⟨Ho1, Hocap1, -⟩
    · iframe Ho Hocap; iexact Hgs
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [Ho1 Hocap1 Hsl1] as %o2 ⟨Ho2, -, -⟩
    · iframe
    try wp_auto
    imod ownSlice_persist $$ Ho2 with #Ho2
    imodintro
    iapply HΦ
    iunfold factsRO
    iexists _
    iframe Ho2
    ipureintro
    unfold lset.add; rw [hc]
    simp only [List.replicate, List.nil_append, Bool.false_eq_true, ite_false]
    exact List.Forall₂.append Hrel (List.Forall₂.cons Hgx List.Forall₂.nil)
  · try wp_auto
    imodintro
    iapply HΦ
    unfold lset.add; rw [hc]; simp only [↓reduceIte]
    iexact Hs

end proof

end AntCheck
end EtcdGrove
end Perennial
