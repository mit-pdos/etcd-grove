/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `ConfOf`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ConfOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.At
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.NextConf

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

theorem ConfOf_setAdd_len (s : SSet) (x : Str) : (setAdd s x).length ≤ s.length + 1 := by
  unfold setAdd
  simp only
  split
  · omega
  · simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
    omega

theorem ConfOf_foldl_setAdd_len (t s : SSet) : (t.foldl setAdd s).length ≤ s.length + t.length := by
  induction t generalizing s with
  | nil => simp
  | cons x t ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (setAdd s x)
    have := ConfOf_setAdd_len s x
    omega

theorem ConfOf_setOf_len (xs : List Str) : (setOf xs).length ≤ xs.length := by
  have := ConfOf_foldl_setAdd_len xs []
  unfold setOf; simpa using this

theorem ConfOf_union_len (s t : SSet) : (s.union t).length ≤ s.length + t.length :=
  ConfOf_foldl_setAdd_len t s

theorem ConfOf_minus_len (s t : SSet) : (s.minus t).length ≤ s.length := List.length_filter_le _ _

/-- The step of `confOf`'s fold. -/
def ConfOf_f (l : List Entry) : Conf → Nat → EvalM Conf := fun c (i : Nat) => do
  let e ← atE l ((i : Int) + 1); if isConf e then nextConf c e.value else pure c

theorem ConfOf_eq (l : List Entry) (a : Int) (c0 : Conf) (h : ¬ a < 0) :
    confOf l a c0 = (List.range a.toNat).foldlM (ConfOf_f l) c0 := by
  unfold confOf
  rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
  rfl

theorem ConfOf_atE (l : List Entry) (k : Int) (x : Entry) (h : atE l k = .ok x) :
    1 ≤ k ∧ k ≤ l.length ∧ l[(k - 1).toNat]? = some x := by
  unfold atE at h
  split at h
  · cases h
  · rename_i hk
    have hx := (Except.ok.inj h)
    refine ⟨by omega, by omega, ?_⟩
    rw [← hx, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

theorem ConfOf_sum_take (l : List Entry) (n : Nat) :
    ((l.take n).map Entry.chgSize).sum ≤ (l.map Entry.chgSize).sum := by
  conv => rhs; rw [← List.take_append_drop n l]
  rw [List.map_append, List.sum_append]
  omega

theorem ConfOf_sum_take_succ (l : List Entry) (n : Nat) (x : Entry) (h : l[n]? = some x) :
    ((l.take (n + 1)).map Entry.chgSize).sum = ((l.take n).map Entry.chgSize).sum + x.chgSize := by
  rw [List.take_add_one, h]
  simp

theorem ConfOf_nextConf_len (c c' : Conf) (d : Value) (h : nextConf c d = .ok c') :
    c'.cin.length ≤ c.cin.length + d.add.length := by
  unfold nextConf at h
  cases hr : d.asRec with
  | error _ => rw [hr] at h; cases h
  | ok r =>
  rw [hr] at h
  have hrd : r = d := by
    unfold Value.asRec at hr
    split at hr
    · cases hr
    · exact (Except.ok.inj hr).symm
  subst hrd
  change (if r.leave = true then (pure { cin := c.cin, cout := [] } : EvalM Conf) else do
      let t ← target c r
      if r.joint = true then pure { cin := t, cout := c.cin } else pure { cin := t, cout := [] }) = .ok c' at h
  have ht : ∀ t, target c r = .ok t → t.length ≤ c.cin.length + r.add.length := by
    intro t ht
    unfold target at ht
    rw [hr] at ht
    have := Except.ok.inj ht
    subst this
    have h1 := ConfOf_minus_len (c.cin.union (setOf r.add)) (setOf r.remove)
    have h2 := ConfOf_union_len c.cin (setOf r.add)
    have h3 := ConfOf_setOf_len r.add
    omega
  cases hl : r.leave
  · rw [hl] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases ht' : target c r with
    | error _ => rw [ht'] at h; cases h
    | ok t =>
    rw [ht'] at h
    have := ht t ht'
    cases hj : r.joint
    · rw [hj] at h; cases Except.ok.inj h; simpa using this
    · rw [hj] at h; cases Except.ok.inj h; simpa using this
  · rw [hl] at h; cases Except.ok.inj h; simp

theorem ConfOf_arith (kv a : w64) (ha : sint.Z a < 2 ^ 63 - 1) (hq0 : 1 ≤ sint.Z kv) (hqk : sint.Z kv ≤ sint.Z a) :
    sint.nat (kv + W64 1) - 1 = (sint.nat kv - 1) + 1 ∧
      (sint.Z a).toNat - (sint.nat kv - 1) = ((sint.Z a).toNat - (sint.nat kv - 1) - 1) + 1 ∧
      (sint.Z a).toNat - (sint.nat kv - 1 + 1) = (sint.Z a).toNat - (sint.nat kv - 1) - 1 ∧
      sint.Z (kv + W64 1) = sint.Z kv + 1 ∧ ((sint.nat kv - 1 : Nat) : Int) + 1 = sint.Z kv ∧
      (sint.Z kv - 1).toNat = sint.nat kv - 1 := by
  refine ⟨by word, by word, by word, by word, by word, by word⟩

theorem ConfOf_natZ (x : w64) (h : 0 ≤ sint.Z x) : (sint.nat x : Int) = sint.Z x := by word

theorem ConfOf.wp_proof (wp_At : At.spec (GF := GF) (hG := hG)) (wp_IsConf : IsConf.spec (GF := GF) (hG := hG))
    (wp_NextConf : NextConf.spec (GF := GF) (hG := hG)) :
    ConfOf.spec (GF := GF) (hG := hG) := by
  intro sl l a g c0 c
  wp_start as ⟨#Hl, #Hc0, %Hk, %Ha, %Hbd⟩
  have ha0 : ¬ sint.Z a < 0 := by
    intro h; unfold confOf at Hk; rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at Hk; cases Hk
  rw [ConfOf_eq l _ c0 ha0] at Hk
  unfold ConfOf.Bounded at Hbd
  wp_auto
  rw [decide_eq_false (by rw [show sint.Z (W64 0) = 0 from rfl]; exact ha0)]
  try wp_auto
  ihave IH : iprop(∃ (kv : w64) (gc : G.Conf) (cur : Conf),
      "k" ∷ k_ptr ↦ kv ∗ "c" ∷ c_ptr ↦ gc ∗ "#Hcur" ∷ confRO gc cur ∗
      "%Hq" ∷ ⌜1 ≤ sint.Z kv ∧ (sint.Z kv ≤ sint.Z a + 1 ∨ sint.Z kv = 1) ∧
        (List.range' (sint.nat kv - 1) ((sint.Z a).toNat - (sint.nat kv - 1))).foldlM
          (ConfOf_f l) cur = .ok c ∧
        cur.cin.length ≤ c0.cin.length + ((l.take (sint.nat kv - 1)).map Entry.chgSize).sum⌝)
      $$ [k c]
  · iexists _, _, c0
    iframe
    iframe Hc0
    ipureintro
    refine ⟨by rw [show sint.Z (W64 1) = 1 from rfl]; omega, Or.inr rfl, ?_, ?_⟩
    · rw [show sint.nat (W64 1) - 1 = 0 from rfl, Nat.sub_zero, ← List.range_eq_range']
      exact Hk
    · simp
  wp_for IH
  obtain ⟨hq0, hq1, hqb, hcin⟩ := Hq
  wp_if_destruct
  · obtain ⟨hn1, hn2, hn3, hpq1, hqi, hqn⟩ := ConfOf_arith kv a Ha hq0 Hif
    rw [hn2, List.range'_succ, List.foldlM_cons] at hqb
    cases hx : atE l (sint.Z kv) with
    | error err =>
      have : ConfOf_f l cur (sint.nat kv - 1) = .error err := by
        unfold ConfOf_f; rw [hqi, hx]; rfl
      rw [this] at hqb; cases hqb
    | ok x =>
    obtain ⟨_, hxl, hxe⟩ := ConfOf_atE l _ x hx
    rw [hqn] at hxe
    have hsum := ConfOf_sum_take_succ l _ x hxe
    have hall := ConfOf_sum_take l (sint.nat kv - 1 + 1)
    rw [hsum] at hall
    have hcs : x.chgSize = x.value.add.length + x.value.remove.length := rfl
    wp_apply wp_At sl l kv x $$ [Hl] as %e #He
    · iframe Hl; ipureintro; exact hx
    try wp_auto
    wp_apply wp_IsConf e x $$ [He]
    · iexact He
    try wp_auto
    cases hc : isConf x
    · have hf : ConfOf_f l cur (sint.nat kv - 1) = .ok cur := by
        unfold ConfOf_f; rw [hqi, hx]; show (if isConf x then nextConf cur x.value else pure cur) = _; rw [hc]; rfl
      rw [hf] at hqb
      have hqb' : List.foldlM (ConfOf_f l) cur
          (List.range' (sint.nat kv - 1 + 1) ((sint.Z a).toNat - (sint.nat kv - 1) - 1)) = Except.ok c := hqb
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, cur
      iframe
      iframe Hcur
      ipureintro
      refine ⟨by omega, by left; omega, ?_, ?_⟩
      · rw [hn1, hn3]; exact hqb'
      · rw [hn1, hsum]; omega
    · cases hnc : nextConf cur x.value with
      | error err =>
        have : ConfOf_f l cur (sint.nat kv - 1) = .error err := by
          unfold ConfOf_f; rw [hqi, hx]; show (if isConf x then nextConf cur x.value else pure cur) = _; rw [hc]; exact hnc
        rw [this] at hqb; cases hqb
      | ok cur' =>
      have hf : ConfOf_f l cur (sint.nat kv - 1) = .ok cur' := by
        unfold ConfOf_f; rw [hqi, hx]; show (if isConf x then nextConf cur x.value else pure cur) = _; rw [hc]; exact hnc
      rw [hf] at hqb
      have hqb' : List.foldlM (ConfOf_f l) cur'
          (List.range' (sint.nat kv - 1 + 1) ((sint.Z a).toNat - (sint.nat kv - 1) - 1)) = Except.ok c := hqb
      have hlen' := ConfOf_nextConf_len cur cur' x.value hnc
      iunfold entryRO at He
      icases He with ⟨-, #Hev⟩
      try wp_auto
      wp_apply wp_NextConf gc cur e.Value' x.value cur' $$ [Hcur Hev] as %gc' #Hgc'
      · iframe Hcur Hev; ipureintro; refine ⟨hnc, by omega, by omega⟩
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, cur'
      iframe
      iframe Hgc'
      ipureintro
      refine ⟨by omega, by left; omega, ?_, ?_⟩
      · rw [hn1, hn3]; exact hqb'
      · rw [hn1, hsum]; omega
  · try wp_auto
    have h0 : (sint.Z a).toNat - (sint.nat kv - 1) = 0 := by
      have e1 := ConfOf_natZ kv (by omega)
      omega
    rw [h0] at hqb
    cases Except.ok.inj hqb
    iapply HΦ
    iexact Hcur

end proof

end AntCheck
end EtcdGrove
end Perennial
