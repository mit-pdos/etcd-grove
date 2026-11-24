/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.HasFirst`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__HasFirst
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.At
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

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

/-- `s.Log[k]`. -/
theorem State.HasFirst_logsRO_at (sl : GoSlice) (ls : List (List Entry)) (k : w64)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k < ls.length) :
    logsRO (GF := GF) sl ls ⊢ ∃ v : GoSlice, sliceAt sl k v ∗ logRO v ls[sint.nat k]! := by
  iintro #H
  iunfold logsRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_at (fun g l => logRO (GF := GF) g l) sl gs ls k hk
  iframe Hgs Hb

/-- A log's length. -/
theorem State.HasFirst_logRO_len (sl : GoSlice) (l : List Entry) :
    logRO (GF := GF) sl l ⊢ ⌜sint.Z sl.len = (l.length : Int)⌝ := by
  iintro #H
  iunfold logRO at H
  icases H with ⟨%es, #Hes, #Hle⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hle
  ipureintro
  rw [← Hll, Hel.1]; word

/-- The step of `State.hasFirst`'s fold. -/
def State.HasFirst_f (s : State) (j : Nat) (m : AppendFact) : Bool → Nat → EvalM Bool := fun ok (q : Nat) => do
    if !ok then return false
    let q : Int := (q : Int) + 1
    andM (pure (decide (m.prevLogIndex + q ≤ (s.log[j]!).length)))
      (do pure ((← atE (s.log[j]!) (m.prevLogIndex + q)).term == (← atE m.entries q).term))

theorem State.HasFirst_eq (s : State) (j : Nat) (m : AppendFact) (k : Int) :
    s.hasFirst j m k = (List.range k.toNat).foldlM (State.HasFirst_f s j m) true := rfl

theorem State.HasFirst_false (s : State) (j : Nat) (m : AppendFact) :
    ∀ l : List Nat, l.foldlM (State.HasFirst_f s j m) false = .ok false
  | [] => rfl
  | q :: l => by
    rw [List.foldlM_cons]
    exact State.HasFirst_false s j m l

theorem State.HasFirst_f_gt (s : State) (j : Nat) (m : AppendFact) (i : Nat)
    (h : ¬ m.prevLogIndex + ((i : Int) + 1) ≤ (s.log[j]!).length) :
    State.HasFirst_f s j m true i = .ok false := by
  unfold State.HasFirst_f andM
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_false h]
  rfl

theorem State.HasFirst_f_le (s : State) (j : Nat) (m : AppendFact) (i : Nat)
    (h : m.prevLogIndex + ((i : Int) + 1) ≤ (s.log[j]!).length) :
    State.HasFirst_f s j m true i = (do pure ((← atE (s.log[j]!) (m.prevLogIndex + ((i : Int) + 1))).term ==
      (← atE m.entries ((i : Int) + 1)).term)) := by
  unfold State.HasFirst_f andM
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_true h]
  rfl

theorem State.HasFirst_arith (qv k pi : w64) (hp : -2 ^ 61 < sint.Z pi ∧ sint.Z pi < 2 ^ 61)
    (hq0 : 1 ≤ sint.Z qv) (hqk : sint.Z qv ≤ sint.Z k) (hk : -2 ^ 61 < sint.Z k ∧ sint.Z k < 2 ^ 61) :
    sint.nat (qv + W64 1) - 1 = (sint.nat qv - 1) + 1 ∧
      (sint.Z k).toNat - (sint.nat qv - 1) = ((sint.Z k).toNat - (sint.nat qv - 1) - 1) + 1 ∧
      (sint.Z k).toNat - (sint.nat (qv + W64 1) - 1) = (sint.Z k).toNat - (sint.nat qv - 1) - 1 ∧
      sint.Z (pi + qv) = sint.Z pi + sint.Z qv ∧
      sint.Z (qv + W64 1) = sint.Z qv + 1 ∧ ((sint.nat qv - 1 : Nat) : Int) + 1 = sint.Z qv := by
  refine ⟨by word, by word, by word, by word, by word, by word⟩

theorem State.HasFirst_natZ (x : w64) (h : 0 ≤ sint.Z x) : (sint.nat x : Int) = sint.Z x := by word

theorem State.HasFirst.wp_proof (wp_At : At.spec (GF := GF) (hG := hG)) :
    State.HasFirst.spec (GF := GF) (hG := hG) := by
  intro p s j gm m k b
  wp_start as ⟨#Hs, #Hm, %Hj0, %Hj1, %Hb, %Hpok, %Hkok⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  icases State.HasFirst_logsRO_at g.Log' s.log j ⟨Hj0, by rw [HWf.len_log]; exact Hj1⟩ $$ HLog with ⟨%v, #Hva, #Hv⟩
  ihave %Hvl := State.HasFirst_logRO_len v _ $$ Hv
  iunfold appendFactRO at Hm
  icases Hm with ⟨%Hmf, #Hent⟩
  obtain ⟨_, _, _, Hpi, Hpt, _⟩ := Hmf
  rw [State.HasFirst_eq] at Hb
  wp_auto
  ihave IH : iprop(∃ (qv : w64),
      "q" ∷ q_ptr ↦ qv ∗
      "%Hq" ∷ ⌜1 ≤ sint.Z qv ∧ (sint.Z qv ≤ sint.Z k + 1 ∨ sint.Z qv = 1) ∧
        (List.range' (sint.nat qv - 1) ((sint.Z k).toNat - (sint.nat qv - 1))).foldlM
          (State.HasFirst_f s (sint.nat j) m) true = .ok b⌝)
      $$ [q]
  · iexists _
    iframe
    ipureintro
    refine ⟨by rw [show sint.Z (W64 1) = 1 from rfl]; omega, Or.inr rfl, ?_⟩
    rw [show sint.nat (W64 1) - 1 = 0 from rfl, Nat.sub_zero, ← List.range_eq_range']
    exact Hb
  wp_for IH
  obtain ⟨hq0, hq1, hqb⟩ := Hq
  have hkb := Hkok
  unfold numOk numBound at hkb Hpok
  wp_if_destruct
  · obtain ⟨hn1, hn2, hn3, hpq, hpq1, hqi⟩ := State.HasFirst_arith qv k gm.PrevLogIndex' (by omega) hq0 Hif hkb
    rw [hn2, List.range'_succ, List.foldlM_cons] at hqb
    wp_apply wp_load_at _ _ v Hj0 $$ [Hva]
    · iexact Hva
    try wp_auto
    rw [hpq]
    by_cases hle : sint.Z gm.PrevLogIndex' + sint.Z qv ≤ sint.Z v.len
    · rw [decide_eq_true hle]
      have hle' : m.prevLogIndex + (((sint.nat qv - 1 : Nat) : Int) + 1) ≤ (s.log[sint.nat j]!).length := by
        rw [hqi, ← Hpi, ← Hvl]; exact hle
      rw [State.HasFirst_f_le s _ m _ hle', hqi] at hqb
      cases hx : atE s.log[sint.nat j]! (m.prevLogIndex + sint.Z qv) with
      | error _ => rw [hx] at hqb; cases hqb
      | ok x =>
      cases hy : atE m.entries (sint.Z qv) with
      | error _ => rw [hx, hy] at hqb; cases hqb
      | ok y =>
      rw [hx, hy] at hqb
      try wp_auto
      wp_apply wp_load_at _ _ v Hj0 $$ [Hva]
      · iexact Hva
      try wp_auto
      wp_apply wp_At v _ (gm.PrevLogIndex' + qv) x $$ [Hv] as %e #He
      · iframe Hv; ipureintro; rw [hpq, Hpi]; exact hx
      iunfold entryRO at He
      icases He with ⟨%Hex, -⟩
      try wp_auto
      wp_apply wp_At gm.Entries' _ qv y $$ [Hent] as %e2 #He2
      · iframe Hent; ipureintro; exact hy
      iunfold entryRO at He2
      icases He2 with ⟨%Hey, -⟩
      try wp_auto
      have hqb' : List.foldlM (State.HasFirst_f s (sint.nat j) m) (x.term == y.term)
          (List.range' (sint.nat qv - 1 + 1) ((sint.Z k).toNat - (sint.nat qv - 1) - 1)) = Except.ok b := hqb
      by_cases ht : e.Term' = e2.Term'
      · rw [decide_eq_true ht]
        have hxy : (x.term == y.term) = true := by rw [beq_iff_eq, ← Hex.1, ← Hey.1, ht]
        rw [hxy] at hqb'
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        refine ⟨by omega, by left; omega, ?_⟩
        rw [hn1, show (sint.Z k).toNat - (sint.nat qv - 1 + 1) = (sint.Z k).toNat - (sint.nat qv - 1) - 1 by omega]; exact hqb'
      · rw [decide_eq_false ht]
        have hxy : (x.term == y.term) = false := by
          rw [beq_eq_false_iff_ne, ← Hex.1, ← Hey.1]; intro h; exact ht (BitVec.toInt_inj.mp h)
        rw [hxy, State.HasFirst_false] at hqb'
        cases Except.ok.inj hqb'
        try wp_auto
        wp_for_post
        try wp_auto
        iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false hle]
      have hle' : ¬ m.prevLogIndex + (((sint.nat qv - 1 : Nat) : Int) + 1) ≤ (s.log[sint.nat j]!).length := by
        rw [hqi, ← Hpi, ← Hvl]; exact hle
      rw [State.HasFirst_f_gt s _ m _ hle'] at hqb
      have hb : b = false := by
        have := State.HasFirst_false s (sint.nat j) m (List.range' (sint.nat qv - 1 + 1) ((sint.Z k).toNat - (sint.nat qv - 1) - 1))
        have h2 : List.foldlM (State.HasFirst_f s (sint.nat j) m) false (List.range' (sint.nat qv - 1 + 1) ((sint.Z k).toNat - (sint.nat qv - 1) - 1)) = Except.ok b := hqb
        rw [this] at h2; exact (Except.ok.inj h2).symm
      subst hb
      try wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ; ipureintro; trivial
  · try wp_auto
    have h0 : (sint.Z k).toNat - (sint.nat qv - 1) = 0 := by
      have e1 := State.HasFirst_natZ qv (by omega)
      omega
    rw [h0] at hqb
    cases Except.ok.inj hqb
    iapply HΦ; ipureintro; trivial
