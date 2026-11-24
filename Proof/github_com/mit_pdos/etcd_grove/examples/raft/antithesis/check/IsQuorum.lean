/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `IsQuorum`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsQuorum
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Majority

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

theorem IsQuorum.wp_proof (wp_Majority : Majority.spec (GF := GF) (hG := hG)) :
    IsQuorum.spec (GF := GF) (hG := hG) := by
  intro sl xs g c
  wp_start as ⟨#Hx, #Hc, %Hb⟩
  iunfold confRO at Hc
  icases Hc with ⟨#Hin, #Hout⟩
  ihave #Hout' := Hout
  iunfold strsRO at Hout'
  ihave %Hol := ownSlice_len $$ Hout'
  wp_auto
  wp_apply wp_Majority sl xs g.In' c.cin $$ [Hx Hin]
  · iframe Hx Hin; ipureintro; omega
  try wp_auto
  unfold isQuorum
  cases hm : majority xs c.cin
  · try wp_auto
    iapply HΦ; ipureintro; trivial
  · try wp_auto
    wp_if_destruct
    · try wp_auto
      have : c.cout.length = 0 := by rw [Hol.1]; word
      simp only [this, Bool.true_and, BEq.rfl, Bool.true_or]
      iapply HΦ; ipureintro; trivial
    · wp_apply wp_Majority sl xs g.Out' c.cout $$ [Hx Hout]
      · iframe Hx Hout; ipureintro; omega
      try wp_auto
      have : (c.cout.length == 0) = false := by
        simp only [beq_eq_false_iff_ne]; intro h; apply Hif; rw [h] at Hol; word
      simp only [this, Bool.true_and, Bool.false_or]
      iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
