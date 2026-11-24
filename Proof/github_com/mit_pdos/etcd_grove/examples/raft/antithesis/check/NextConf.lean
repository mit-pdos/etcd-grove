/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `NextConf`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.NextConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value__rec
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Target

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

theorem NextConf_asRec (d r : Value) (h : d.asRec = .ok r) : r = d := by
  unfold Value.asRec at h
  split at h
  · cases h
  · exact (Except.ok.inj h).symm

theorem NextConf.wp_proof (wp_rec : Value.rec.spec (GF := GF) (hG := hG))
    (wp_Target : Target.spec (GF := GF) (hG := hG)) :
    NextConf.spec (GF := GF) (hG := hG) := by
  intro g c h d c'
  wp_start as ⟨#Hc, #Hd, %Ht, %Hb1, %Hb2⟩
  ihave #Hc' := Hc
  iunfold confRO at Hc'
  icases Hc' with ⟨#Hin, #Hout⟩
  ihave #Hd' := Hd
  iunfold valueRO at Hd'
  icases Hd' with ⟨%Hdf, -, -⟩
  unfold nextConf at Ht
  cases hr : d.asRec with
  | error _ => rw [hr] at Ht; cases Ht
  | ok r =>
  rw [hr] at Ht
  have hrd := NextConf_asRec d r hr
  subst hrd
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value.TypeAssumptions.ptr_rec_unfold.method_unfold]
  try wp_auto
  wp_apply wp_rec h r r $$ [Hd] as #Hr
  · iframe Hd; ipureintro; exact hr
  try wp_auto
  obtain ⟨_, _, Hj, Hl⟩ := Hdf
  rw [Hl]
  have Ht' : (if r.leave = true then (pure { cin := c.cin } : EvalM Conf) else do
      let t ← target c r
      if r.joint = true then pure { cin := t, cout := c.cin } else pure { cin := t }) = .ok c' := Ht
  cases hl : r.leave
  · rw [hl] at Ht'
    simp only [Bool.false_eq_true, ↓reduceIte] at Ht'
    cases ht : target c r with
    | error _ => rw [ht] at Ht'; cases Ht'
    | ok t =>
    rw [ht] at Ht'
    try wp_auto
    wp_apply wp_Target g c h r t $$ [Hc Hd] as %u #Hu
    · iframe Hc Hd; ipureintro; exact ⟨ht, Hb1, Hb2⟩
    try wp_auto
    rw [Hj]
    cases hj : r.joint
    · rw [hj] at Ht'
      cases Except.ok.inj Ht'
      try wp_auto
      iapply HΦ
      iunfold confRO
      isplitr
      · iexact Hu
      iunfold strsRO
      iapply ownSlice_nil
    · rw [hj] at Ht'
      cases Except.ok.inj Ht'
      try wp_auto
      iapply HΦ
      iunfold confRO
      iframe Hu Hin
  · rw [hl] at Ht'
    cases Except.ok.inj Ht'
    try wp_auto
    iapply HΦ
    iunfold confRO
    isplitr
    · iexact Hin
    iunfold strsRO
    iapply ownSlice_nil

end proof

end AntCheck
end EtcdGrove
end Perennial
