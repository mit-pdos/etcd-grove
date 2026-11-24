/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Target`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Target
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value__rec
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SetOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Union
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Minus

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

theorem Target_setAdd_len (s : SSet) (x : Str) : (setAdd s x).length ≤ s.length + 1 := by
  unfold setAdd
  simp only
  split
  · omega
  · simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
    omega

theorem Target_foldl_setAdd_len (t s : SSet) : (t.foldl setAdd s).length ≤ s.length + t.length := by
  induction t generalizing s with
  | nil => simp
  | cons x t ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (setAdd s x)
    have := Target_setAdd_len s x
    omega

theorem Target_setOf_len (xs : List Str) : (setOf xs).length ≤ xs.length := by
  have := Target_foldl_setAdd_len xs []
  unfold setOf; simpa using this

theorem Target_union_len (s t : SSet) : (s.union t).length ≤ s.length + t.length :=
  Target_foldl_setAdd_len t s

theorem Target_minus_len (s t : SSet) : (s.minus t).length ≤ s.length := List.length_filter_le _ _

theorem Target.wp_proof (wp_rec : Value.rec.spec (GF := GF) (hG := hG))
    (wp_SetOf : SetOf.spec (GF := GF) (hG := hG))
    (wp_Union : Set.Union.spec (GF := GF) (hG := hG))
    (wp_Minus : Set.Minus.spec (GF := GF) (hG := hG)) :
    Target.spec (GF := GF) (hG := hG) := by
  intro g c h d t
  wp_start as ⟨#Hc, #Hd, %Ht, %Hb1, %Hb2⟩
  iunfold confRO at Hc
  icases Hc with ⟨#Hin, #Hout⟩
  unfold target at Ht
  cases hr : d.asRec with
  | error _ => rw [hr] at Ht; cases Ht
  | ok r =>
  rw [hr] at Ht
  have hrd : r = d := by
    unfold Value.asRec at hr
    split at hr
    · cases hr
    · exact (Except.ok.inj hr).symm
  subst hrd
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value.TypeAssumptions.ptr_rec_unfold.method_unfold]
  try wp_auto
  wp_apply wp_rec h r r $$ [Hd] as #Hr
  · iframe Hd; ipureintro; exact hr
  try wp_auto
  iunfold valueRO at Hr
  icases Hr with ⟨%Hrf, #Hadd, #Hrem⟩
  wp_apply wp_SetOf h.Remove' r.remove $$ [Hrem] as %u1 #Hu1
  · iframe Hrem; ipureintro; omega
  try wp_auto
  wp_apply wp_SetOf h.Add' r.add $$ [Hadd] as %u2 #Hu2
  · iframe Hadd; ipureintro; omega
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set''.TypeAssumptions.ptr_Union_unfold.method_unfold]
  try wp_auto
  have h1 := Target_setOf_len r.add
  wp_apply wp_Union g.In' c.cin u2 (setOf r.add) $$ [Hin Hu2] as %u3 #Hu3
  · iframe Hin Hu2; ipureintro; omega
  try wp_auto
  wp_apply wp_Minus u3 _ u1 (setOf r.remove) $$ [Hu3 Hu1] as %u4 #Hu4
  · iframe Hu3 Hu1
  try wp_auto
  cases Except.ok.inj Ht
  iapply HΦ
  iexact Hu4

end proof

end AntCheck
end EtcdGrove
end Perennial
