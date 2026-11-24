/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Legal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Legal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value__rec
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Target
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Minus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Union

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

theorem Legal_asRec (d r : Value) (h : d.asRec = .ok r) : r = d := by
  unfold Value.asRec at h
  split at h
  · cases h
  · exact (Except.ok.inj h).symm

theorem Legal_setAdd_len (s : SSet) (x : Str) : (setAdd s x).length ≤ s.length + 1 := by
  unfold setAdd
  simp only
  split
  · omega
  · simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
    omega

theorem Legal_foldl_setAdd_len (t s : SSet) : (t.foldl setAdd s).length ≤ s.length + t.length := by
  induction t generalizing s with
  | nil => simp
  | cons x t ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (setAdd s x)
    have := Legal_setAdd_len s x
    omega

theorem Legal_setOf_len (xs : List Str) : (setOf xs).length ≤ xs.length := by
  have := Legal_foldl_setAdd_len xs []
  unfold setOf; simpa using this

theorem Legal_union_len (s t : SSet) : (s.union t).length ≤ s.length + t.length :=
  Legal_foldl_setAdd_len t s

theorem Legal_minus_len (s t : SSet) : (s.minus t).length ≤ s.length := List.length_filter_le _ _

theorem Legal.wp_proof (wp_rec : Value.rec.spec (GF := GF) (hG := hG))
    (wp_Target : Target.spec (GF := GF) (hG := hG))
    (wp_Minus : Set.Minus.spec (GF := GF) (hG := hG))
    (wp_Union : Set.Union.spec (GF := GF) (hG := hG)) :
    Legal.spec (GF := GF) (hG := hG) := by
  intro g c h d b
  wp_start as ⟨#Hc, #Hd, %Ht, %Hb1, %Hb2⟩
  ihave #Hc' := Hc
  iunfold confRO at Hc'
  icases Hc' with ⟨#Hin, #Hout⟩
  ihave #Hout' := Hout
  iunfold strsRO at Hout'
  ihave %Hol := ownSlice_len $$ Hout'
  ihave #Hd' := Hd
  iunfold valueRO at Hd'
  icases Hd' with ⟨%Hdf, -, -⟩
  obtain ⟨_, _, Hj, Hl⟩ := Hdf
  unfold legal at Ht
  cases hr : d.asRec with
  | error _ => rw [hr] at Ht; cases Ht
  | ok r =>
  rw [hr] at Ht
  have hrd := Legal_asRec d r hr
  subst hrd
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value.TypeAssumptions.ptr_rec_unfold.method_unfold]
  try wp_auto
  wp_apply wp_rec h r r $$ [Hd] as #Hr
  · iframe Hd; ipureintro; exact hr
  try wp_auto
  rw [Hl]
  have Ht' : (if r.leave = true then (pure (c.cout.length != 0) : EvalM Bool) else do
      if c.cout.length != 0 then return false
      let t ← target c r
      if t.length == 0 then return false
      return r.joint || decide (((c.cin.minus t).union (t.minus c.cin)).length ≤ 1)) = .ok b := Ht
  cases hl : r.leave
  · rw [hl] at Ht'
    simp only [Bool.false_eq_true, ↓reduceIte] at Ht'
    try wp_auto
    have hz : (g.Out'.len = W64 0) ↔ c.cout.length = 0 := by
      constructor
      · intro h0; rw [Hol.1, h0]; rfl
      · intro h0; rw [h0] at Hol; word
    by_cases ho : c.cout.length = 0
    · rw [decide_eq_true (hz.2 ho)]
      have : (c.cout.length != 0) = false := by simp [ho]
      rw [this] at Ht'
      simp only [Bool.false_eq_true, ↓reduceIte] at Ht'
      cases ht : target c r with
      | error _ => rw [ht] at Ht'; cases Ht'
      | ok t =>
      rw [ht] at Ht'
      change (if (t.length == 0) = true then (pure false : EvalM Bool)
        else pure (r.joint || decide (((c.cin.minus t).union (t.minus c.cin)).length ≤ 1))) = .ok b at Ht'
      try wp_auto
      wp_apply wp_Target g c h r t $$ [Hc Hd] as %u #Hu
      · iframe Hc Hd; ipureintro; exact ⟨ht, Hb1, Hb2⟩
      try wp_auto
      ihave #Hu' := Hu
      iunfold strsRO at Hu'
      ihave %Hul := ownSlice_len $$ Hu'
      have htl : t.length ≤ c.cin.length + r.add.length := by
        unfold target at ht
        rw [hr] at ht
        have := Except.ok.inj ht
        subst this
        have h1 := Legal_minus_len (c.cin.union (setOf r.add)) (setOf r.remove)
        have h2 := Legal_union_len c.cin (setOf r.add)
        have h3 := Legal_setOf_len r.add
        omega
      wp_if_destruct
      · have : (t.length == 0) = true := by
          rw [beq_iff_eq, Hul.1, Hif]; rfl
        rw [this] at Ht'
        cases Except.ok.inj Ht'
        try wp_auto
        iapply HΦ; ipureintro; trivial
      · have : (t.length == 0) = false := by
          rw [beq_eq_false_iff_ne]; intro h0; apply Hif; rw [h0] at Hul; word
        rw [this] at Ht'
        simp only [Bool.false_eq_true, ↓reduceIte] at Ht'
        rw [Hj]
        cases hj : r.joint
        · rw [hj] at Ht'
          simp only [Bool.false_or] at Ht'
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set''.TypeAssumptions.ptr_Minus_unfold.method_unfold]
          try wp_auto
          wp_apply wp_Minus u t g.In' c.cin $$ [Hu Hin] as %u1 #Hu1
          · iframe Hu Hin
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set''.TypeAssumptions.ptr_Minus_unfold.method_unfold]
          try wp_auto
          wp_apply wp_Minus g.In' c.cin u t $$ [Hu Hin] as %u2 #Hu2
          · iframe Hu Hin
          try wp_auto
          have h1 := Legal_minus_len c.cin t
          have h2 := Legal_minus_len t c.cin
          wp_apply wp_Union u2 _ u1 _ $$ [Hu1 Hu2] as %u3 #Hu3
          · iframe Hu1 Hu2; ipureintro; omega
          try wp_auto
          ihave #Hu3' := Hu3
          iunfold strsRO at Hu3'
          ihave %Hu3l := ownSlice_len $$ Hu3'
          have h4 := Legal_union_len (c.cin.minus t) (t.minus c.cin)
          have : decide (sint.Z u3.len ≤ sint.Z (W64 1)) = b := by
            rw [← Except.ok.inj Ht', show sint.Z (W64 1) = 1 from rfl]
            simp only [decide_eq_decide]
            have : sint.Z u3.len = (((c.cin.minus t).union (t.minus c.cin)).length : Int) := by
              rw [Hu3l.1]; word
            omega
          rw [this]
          iapply HΦ; ipureintro; trivial
        · rw [hj] at Ht'
          cases Except.ok.inj Ht'
          try wp_auto
          simp only [Bool.true_or]
          iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false (fun h0 => ho (hz.1 h0))]
      have : (c.cout.length != 0) = true := by simp [ho]
      rw [this] at Ht'
      cases Except.ok.inj Ht'
      try wp_auto
      iapply HΦ; ipureintro; trivial
  · rw [hl] at Ht'
    cases Except.ok.inj Ht'
    try wp_auto
    have : decide (g.Out'.len = W64 0) = !(c.cout.length != 0) := by
      by_cases ho : c.cout.length = 0
      · rw [decide_eq_true (by rw [ho] at Hol; word)]; simp [ho]
      · rw [decide_eq_false (by intro h0; apply ho; rw [Hol.1, h0]; rfl)]; simp [ho]
    rw [this]
    try wp_auto
    simp only [Bool.not_not]
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
