/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `Matching` (B 132-134).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Matching
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Min
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Entry__Equal
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

/-- One step of `matching`'s fold (the Lean's lambda). -/
def matchStep (a b : List Entry) (ok : Bool) (i : Nat) : EvalM Bool := do
  if !ok then return false
  if (a[i]!).term == (b[i]!).term then
    if !(← (a[i]!).equal (b[i]!)) then return false
    if i > 0 && (a[i - 1]!).term != (b[i - 1]!).term then return false
  return true

theorem matching_eq (a b : List Entry) :
    matching a b = (List.range (min a.length b.length)).foldlM (matchStep a b) true := rfl

theorem matchStep_fold_false (a b : List Entry) (l : List Nat) : l.foldlM (matchStep a b) false = .ok false := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.foldlM_cons, matchStep, ih]

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Matching.wp_proof (wp_Min : Min.spec (GF := GF) (hG := hG))
    (wp_EntryEqual : Entry.Equal.spec (GF := GF) (hG := hG)) :
    Matching.spec (GF := GF) (hG := hG) := by
  intro al a bl b r
  wp_start as ⟨#Ha, #Hb, %Hr⟩
  obtain ⟨Hr, Hal⟩ := Hr
  rw [matching_eq] at Hr
  iunfold logRO at Ha Hb
  icases Ha with ⟨%es, #Hes, #Hae⟩
  icases Hb with ⟨%fs, #Hfs, #Hbf⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hfl := ownSlice_len $$ Hfs
  ihave %Hael := BigSepL2.bigSepL2_length $$ Hae
  ihave %Hbfl := BigSepL2.bigSepL2_length $$ Hbf
  wp_auto
  have ha : (a.length : Int) = sint.Z al.len := by rw [← Hael, Hel.1]; exact sint_nat_cast Hel.2
  have hb : (b.length : Int) = sint.Z bl.len := by rw [← Hbfl, Hfl.1]; exact sint_nat_cast Hfl.2
  have hm : ((min a.length b.length : Nat) : Int) = imin (sint.Z al.len) (sint.Z bl.len) := by
    unfold imin; rw [← ha, ← hb]
    rcases Nat.le_total a.length b.length with h | h
    · rw [Nat.min_eq_left h, ite_eq_left_of_eq_true _ _ (eq_true (by exact_mod_cast h))]
    · rcases Nat.lt_or_ge b.length a.length with h' | h'
      · rw [Nat.min_eq_right h, ite_eq_right_of_eq_false _ _ (eq_false (by exact_mod_cast Nat.not_le.2 h'))]
      · have : a.length = b.length := Nat.le_antisymm h' h
        rw [this, Nat.min_self, ite_eq_left_of_eq_true _ _ (eq_true (Int.le_refl _))]
  ihave IH : iprop(∃ (kv : w64),
      "k" ∷ k_ptr ↦ kv ∗
      "%Hk" ∷ ⌜1 ≤ sint.Z kv ∧ sint.Z kv ≤ (min a.length b.length : Int) + 1 ∧
        ((List.range (min a.length b.length)).drop (sint.nat kv - 1)).foldlM (matchStep a b) true = .ok r⌝)
      $$ [k]
  · have h1 : sint.Z (W64 1) = 1 := rfl
    have h2 : (1 : Int) ≤ (min a.length b.length : Int) + 1 := by omega
    have h3 : sint.nat (W64 1) - 1 = 0 := rfl
    iexists _
    iframe
    ipureintro
    rw [h1, h3]
    exact ⟨Int.le_refl _, h2, by simpa using Hr⟩
  wp_for IH
  obtain ⟨hk1, hk2, hkr⟩ := Hk
  have hkn : (sint.nat kv : Int) = sint.Z kv := sint_nat_cast (by omega)
  wp_apply wp_Min al.len bl.len as %w %Hw
  rw [← hm] at Hw
  try wp_auto
  wp_if_destruct
  · -- `k <= Min(len(a), len(b))`: entry `j = k - 1`
    have hle : sint.Z kv ≤ sint.Z w := of_decide_eq_true (go.intoVal_inj (V := Bool) Hif)
    have hj : sint.nat kv - 1 < min a.length b.length := by
      have h4 : (sint.nat kv : Int) - 1 < ((min a.length b.length : Nat) : Int) := by omega
      omega
    have hja : sint.nat kv - 1 < a.length := by omega
    have hjb : sint.nat kv - 1 < b.length := by omega
    have hjes : sint.nat kv - 1 < es.length := by omega
    have hjfs : sint.nat kv - 1 < fs.length := by omega
    have hs1 := sint_sub_one hk1
    have hz1 : 0 ≤ sint.Z (kv - W64 1) := by omega
    obtain ⟨e, He⟩ : ∃ e, es[sint.nat kv - 1]? = some e := ⟨_, List.getElem?_eq_getElem hjes⟩
    obtain ⟨f, Hf⟩ : ∃ f, fs[sint.nat kv - 1]? = some f := ⟨_, List.getElem?_eq_getElem hjfs⟩
    have Hx : a[sint.nat kv - 1]? = some a[sint.nat kv - 1]! := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hja]; rfl
    have Hy : b[sint.nat kv - 1]? = some b[sint.nat kv - 1]! := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hjb]; rfl
    ihave #Hex := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) He Hx $$ Hae
    ihave #Hfy := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hf Hy $$ Hbf
    have hkj : sint.Z (kv - W64 1) = ((sint.nat kv - 1 : Nat) : Int) := by omega
    have hkj' : (sint.Z (kv - W64 1)).toNat = sint.nat kv - 1 := by omega
    icases ownSlice_elem_acc (sint.Z (kv - W64 1)) e al DFrac.discard es hz1 (by rw [hkj']; exact He) $$ Hes
      with ⟨Hea, -⟩
    icases ownSlice_elem_acc (sint.Z (kv - W64 1)) f bl DFrac.discard fs hz1 (by rw [hkj']; exact Hf) $$ Hfs
      with ⟨Hfb, -⟩
    ihave #Hea' := Hea
    ihave #Hfb' := Hfb
    iStructNamed Hea'
    iStructNamed Hfb'
    have hia : 0 ≤ sint.Z (kv - W64 1) ∧ sint.Z (kv - W64 1) < sint.Z al.len := by omega
    have hib : 0 ≤ sint.Z (kv - W64 1) ∧ sint.Z (kv - W64 1) < sint.Z bl.len := by omega
    have hTa := eq_true hia
    have hTb := eq_true hib
    rw [ite_eq_left_of_eq_true _ _ hTa]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ hTb]
    try wp_auto
    rw [range_drop_cons _ _ hj, List.foldlM_cons] at hkr
    ihave #Hex0 := Hex
    ihave #Hfy0 := Hfy
    iunfold entryRO at Hex Hfy
    icases Hex with ⟨%Hea1, #Hev⟩
    icases Hfy with ⟨%Hfb1, #Hfv⟩
    wp_if_destruct
    · -- equal terms
      have hterm : (a[sint.nat kv - 1]!).term = (b[sint.nat kv - 1]!).term := by rw [← Hea1.1, ← Hfb1.1, Hif]
      cases hc : (a[sint.nat kv - 1]!).equal (b[sint.nat kv - 1]!) with
      | error _ => simp only [matchStep, Bool.not_true, Bool.false_eq_true, ite_false, hterm, beq_self_eq_true, ite_true, hc, error_bind] at hkr; cases hkr
      | ok c =>
      rw [ite_eq_left_of_eq_true _ _ hTb]
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ hTa]
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Entry.TypeAssumptions.ptr_unfold'Equal.method_unfold]
      try wp_auto
      wp_apply wp_EntryEqual e _ f _ c $$ [Hex0 Hfy0]
      · iframe Hex0 Hfy0; ipureintro; exact hc
      cases c
      · -- not equal: `Matching` is false
        try wp_auto
        wp_for_post
        try wp_auto
        have hstep : matchStep a b true (sint.nat kv - 1) = .ok false := by
          simp only [matchStep, Bool.not_true, Bool.false_eq_true, ite_false, hterm, beq_self_eq_true, ite_true, hc,
            ok_bind, Bool.not_false]; rfl
        rw [hstep, ok_bind, matchStep_fold_false] at hkr
        cases hkr
        iapply HΦ; ipureintro; trivial
      try wp_auto
      wp_if_destruct
      · -- `k > 1`: the predecessors' terms
        have h1 : sint.Z (W64 1) = 1 := rfl
        have hi : 0 < sint.nat kv - 1 := by omega
        have hjes2 : sint.nat kv - 1 - 1 < es.length := by omega
        have hjfs2 : sint.nat kv - 1 - 1 < fs.length := by omega
        have hja2 : sint.nat kv - 1 - 1 < a.length := by omega
        have hjb2 : sint.nat kv - 1 - 1 < b.length := by omega
        have hs2 := sint_sub_two (show 2 ≤ sint.Z kv by omega)
        have hz2 : 0 ≤ sint.Z (kv - W64 2) := by omega
        obtain ⟨e', He'⟩ : ∃ e, es[sint.nat kv - 1 - 1]? = some e := ⟨_, List.getElem?_eq_getElem hjes2⟩
        obtain ⟨f', Hf'⟩ : ∃ f, fs[sint.nat kv - 1 - 1]? = some f := ⟨_, List.getElem?_eq_getElem hjfs2⟩
        have Hx' : a[sint.nat kv - 1 - 1]? = some a[sint.nat kv - 1 - 1]! := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hja2]; rfl
        have Hy' : b[sint.nat kv - 1 - 1]? = some b[sint.nat kv - 1 - 1]! := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hjb2]; rfl
        ihave #Hex' := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) He' Hx' $$ Hae
        ihave #Hfy' := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hf' Hy' $$ Hbf
        iunfold entryRO at Hex' Hfy'
        icases Hex' with ⟨%Hea2, #-⟩
        icases Hfy' with ⟨%Hfb2, #-⟩
        have hkj2 : sint.Z (kv - W64 2) = ((sint.nat kv - 1 - 1 : Nat) : Int) := by omega
        have hkj2' : (sint.Z (kv - W64 2)).toNat = sint.nat kv - 1 - 1 := by omega
        icases ownSlice_elem_acc (sint.Z (kv - W64 2)) e' al DFrac.discard es hz2 (by rw [hkj2']; exact He') $$ Hes
          with ⟨Hea3, -⟩
        icases ownSlice_elem_acc (sint.Z (kv - W64 2)) f' bl DFrac.discard fs hz2 (by rw [hkj2']; exact Hf') $$ Hfs
          with ⟨Hfb3, -⟩
        iStructNamed Hea3
        iStructNamed Hfb3
        have hia2 : 0 ≤ sint.Z (kv - W64 2) ∧ sint.Z (kv - W64 2) < sint.Z al.len := by omega
        have hib2 : 0 ≤ sint.Z (kv - W64 2) ∧ sint.Z (kv - W64 2) < sint.Z bl.len := by omega
        have hTa2 := eq_true hia2
        have hTb2 := eq_true hib2
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ hTa2]
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ hTb2]
        try wp_auto
        have hpos : (sint.nat kv - 1 > 0) = True := eq_true hi
        wp_if_destruct
        · -- equal predecessors' terms: the step holds
          have hterm2 : (a[sint.nat kv - 1 - 1]!).term = (b[sint.nat kv - 1 - 1]!).term := by
            rw [← Hea2.1, ← Hfb2.1, Hif]
          have hstep : matchStep a b true (sint.nat kv - 1) = .ok true := by
            simp only [matchStep, Bool.not_true, Bool.false_eq_true, ite_false, hterm, beq_self_eq_true, ite_true, hc,
              ok_bind, Bool.not_false, hterm2, bne_self_eq_false, Bool.and_false]; rfl
          try wp_auto
          wp_for_post
          iframe
          iexists _
          iframe
          ipureintro
          have hk' : sint.Z (kv + W64 1) = sint.Z kv + 1 := sint_add_one (by omega)
          have hkn' := sint_nat_cast (k := kv + W64 1) (by omega)
          have hk'' : sint.nat (kv + W64 1) - 1 = sint.nat kv - 1 + 1 := by omega
          rw [hk', hk'']
          have hb1 : 1 ≤ sint.Z kv + 1 := by omega
          have hb2 : sint.Z kv + 1 ≤ min (a.length : Int) b.length + 1 := by omega
          refine ⟨hb1, hb2, ?_⟩
          rw [hstep] at hkr; exact hkr
        · -- different predecessors' terms: `Matching` is false
          have hterm2 : ((a[sint.nat kv - 1 - 1]!).term != (b[sint.nat kv - 1 - 1]!).term) = true := by
            simp only [bne_iff_ne, ne_eq]; intro h; apply Hif
            have : sint.Z e'.Term' = sint.Z f'.Term' := by rw [Hea2.1, Hfb2.1, h]
            word
          have hstep : matchStep a b true (sint.nat kv - 1) = .ok false := by
            simp only [matchStep, Bool.not_true, Bool.false_eq_true, ite_false, hterm, beq_self_eq_true, ite_true, hc,
              ok_bind, Bool.not_false, hterm2, Bool.and_true, decide_eq_true hi]; rfl
          try wp_auto
          wp_for_post
          try wp_auto
          rw [hstep, ok_bind, matchStep_fold_false] at hkr
          cases hkr
          iapply HΦ; ipureintro; trivial
      · -- `k = 1`: the step holds
        have h1 : sint.Z (W64 1) = 1 := rfl
        have hi : sint.nat kv - 1 = 0 := by omega
        have hstep : matchStep a b true (sint.nat kv - 1) = .ok true := by
          rw [hi]
          rw [hi] at hterm hc
          simp only [matchStep, Bool.not_true, Bool.false_eq_true, ite_false, hterm, beq_self_eq_true, ite_true, hc,
            ok_bind, Bool.not_false, Nat.lt_irrefl, decide_false, Bool.false_and]; rfl
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        have hk' : sint.Z (kv + W64 1) = sint.Z kv + 1 := sint_add_one (by omega)
        have hkn' := sint_nat_cast (k := kv + W64 1) (by omega)
        have hk'' : sint.nat (kv + W64 1) - 1 = sint.nat kv - 1 + 1 := by omega
        rw [hk', hk'']
        have hb1 : 1 ≤ sint.Z kv + 1 := by omega
        have hb2 : sint.Z kv + 1 ≤ min (a.length : Int) b.length + 1 := by omega
        refine ⟨hb1, hb2, ?_⟩
        rw [hstep] at hkr; exact hkr

    · -- different terms: the step holds
      have hterm : ((a[sint.nat kv - 1]!).term == (b[sint.nat kv - 1]!).term) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply Hif
        have : sint.Z e.Term' = sint.Z f.Term' := by rw [Hea1.1, Hfb1.1, h]
        word
      have hstep : matchStep a b true (sint.nat kv - 1) = .ok true := by
        simp only [matchStep, Bool.not_true, Bool.false_eq_true, ite_false, hterm]; rfl
      try wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      have hk' : sint.Z (kv + W64 1) = sint.Z kv + 1 := sint_add_one (by omega)
      have hkn' := sint_nat_cast (k := kv + W64 1) (by omega)
      have hk'' : sint.nat (kv + W64 1) - 1 = sint.nat kv - 1 + 1 := by omega
      rw [hk', hk'']
      have hb1 : 1 ≤ sint.Z kv + 1 := by omega
      have hb2 : sint.Z kv + 1 ≤ min (a.length : Int) b.length + 1 := by omega
      refine ⟨hb1, hb2, ?_⟩
      rw [hstep] at hkr; exact hkr

  · have hlt : ¬ (sint.Z kv ≤ sint.Z w) := fun h => Hif (by rw [decide_eq_true h])
    rw [decide_eq_false hlt]
    simp only [Bool.false_eq_true, ite_false]
    try wp_auto
    have hdone : sint.nat kv - 1 = min a.length b.length := by omega
    rw [hdone, List.drop_eq_nil_of_le (by simp)] at hkr
    cases hkr
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
