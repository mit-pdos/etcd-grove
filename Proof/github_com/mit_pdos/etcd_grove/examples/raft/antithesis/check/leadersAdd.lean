/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `leadersAdd`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.leadersAdd
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.leadersHas

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

theorem leadersAdd.wp_proof (wp_leadersHas : leadersHas.spec (GF := GF) (hG := hG)) :
    leadersAdd.spec (GF := GF) (hG := hG) := by
  intro sl xs g x
  wp_start as ⟨#Hs, ⟨%Hgx1, %Hgx2, %Hb⟩⟩
  ihave #Hs0 := Hs
  iunfold leadersRO at Hs0
  icases Hs0 with ⟨%gs, #Hgs, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  have Hl := Hrel.length_eq
  iapply wp_fupd
  wp_auto
  wp_apply wp_leadersHas sl xs g x $$ [Hs]
  · iframe Hs; ipureintro; exact ⟨Hgx1, Hgx2⟩
  cases hc : xs.contains x
  · try wp_auto
    wp_apply (wp_slice_make3 (V := G.LeaderRec) (W64 0) (sl.len + W64 1) ⟨by word, by word⟩) as %o ⟨Ho, Hocap, -⟩
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
    iunfold leadersRO
    iexists _
    iframe Ho2
    ipureintro
    unfold lset.add; rw [hc]
    simp only [List.replicate, List.nil_append, Bool.false_eq_true, ite_false]
    exact List.Forall₂.append Hrel (List.Forall₂.cons ⟨Hgx1, Hgx2⟩ List.Forall₂.nil)
  · try wp_auto
    imodintro
    iapply HΦ
    unfold lset.add; rw [hc]; simp only [↓reduceIte]
    iexact Hs

end proof

end AntCheck
end EtcdGrove
end Perennial
