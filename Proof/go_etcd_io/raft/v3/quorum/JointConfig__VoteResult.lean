/-
Port of election_proof/proof_JointConfig__VoteResult.v.

Lean notes: Perennial's `array_acc_same` (`v3_proof/readonly.lean`, which cannot be
imported here) is restated locally as `array_acc_same'` (as in
`Proof/JointConfig__CommittedIndex.lean`). Rocq's `w8_absurd` is `decide` on the two
`VoteResult` constants.
-/
module

public import Spec.go_etcd_io.raft.v3.quorum.JointConfig__VoteResult
public import Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__VoteResult

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
/-- `array_acc`, putting back the same element. -/
private theorem array_acc_same' {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc)
    (i : Int) (dq : DFrac) (n : Int) (a : GoArray V n) (v : V)
    (hpos : 0 ≤ i) (hlookup : a.arr[i.toNat]? = some v) :
    typedPointsto (GF := GF) p a dq ⊢
      iprop(typedPointsto (arrayIndexRef V i p) v dq ∗
        (typedPointsto (arrayIndexRef V i p) v dq -∗ typedPointsto p a dq)) := by
  have hset : a.arr.set i.toNat v = a.arr := by
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hlookup
    exact List.set_getElem_self h
  iintro Ha
  icases array_acc (GF := GF) p i dq n a v hpos hlookup $$ Ha with ⟨Hv, Ha⟩
  iframe Hv
  iintro Hv
  ihave Ha := Ha $$ %v Hv
  rw [hset]
  iexact Ha

/-- What one half's answer says, as `MajQ` (pure). -/
theorem majVote_facts (r : w8) (s q q' : GSet w64)
    (Hr : r = VoteWon ∨ r = VoteLost ∨ r = VotePending)
    (Hemp : s = ∅ → r = VoteWon) (Hw : s ≠ ∅ → (r = VoteWon ↔ IsQuorum s q))
    (Hl : s ≠ ∅ → (r = VoteLost ↔ ¬ IsQuorum s q')) :
    (r = VoteWon ↔ MajQ s q) ∧ (r = VoteLost ↔ ¬ MajQ s q') := by
  by_cases hs : s = ∅
  · have := Hemp hs
    subst this
    refine ⟨⟨fun _ => .inl hs, fun _ => rfl⟩, ⟨fun h => absurd h (by decide), fun h => absurd (.inl hs) h⟩⟩
  · rw [MajQ_of_ne _ hs, MajQ_of_ne _ hs]
    exact ⟨Hw hs, Hl hs⟩

/-- The combination of the two halves' answers (pure). -/
theorem jointVote_facts (r1 r2 : w8)
    (Hr1 : r1 = VoteWon ∨ r1 = VoteLost ∨ r1 = VotePending)
    (Hr2 : r2 = VoteWon ∨ r2 = VoteLost ∨ r2 = VotePending) :
    let res := if r1 = r2 then r1 else if r1 = VoteLost ∨ r2 = VoteLost then VoteLost else VotePending
    (res = VoteWon ∨ res = VoteLost ∨ res = VotePending) ∧
    (res = VoteWon ↔ r1 = VoteWon ∧ r2 = VoteWon) ∧
    (res = VoteLost ↔ r1 = VoteLost ∨ r2 = VoteLost) := by
  rcases Hr1 with rfl | rfl | rfl <;> rcases Hr2 with rfl | rfl | rfl <;> decide

/-- Both halves asked, through `array_acc_same'` (each half's id set lent to
`MajorityConfig.VoteResult` and given back), the answers combined (`jointVote_facts`). -/
theorem quorum.JointConfig.VoteResult.wp_proof
    (wp_MajorityConfig_VoteResult : quorum.MajorityConfig.VoteResult.spec (GF := GF) (hG := hG)) :
    quorum.JointConfig.VoteResult.spec (GF := GF) (hG := hG) := by
  intro cp dqc a v0 v1 s0 s1 vm dqv votes Harr Hsz0 Hsz1
  wp_start as ⟨Hc, Hv0, Hv1, Hvotes⟩
  wp_auto
  wp_method_call
  wp_call
  wp_call
  wp_auto
  icases array_acc_same' (GF := GF) _ (sint.Z (W64 0)) _ _ _ v0 (by decide)
      (by simp [Harr]) $$ c with ⟨Hc0, Hcback⟩
  ihave Hv0 := ownIdsetQ_toMaj _ _ $$ Hv0
  wp_apply wp_MajorityConfig_VoteResult s0 $$ [$Hc0 $Hvotes $Hv0]
    as %r1 ⟨Hc0, Hvotes, Hv0, %Hr1, %Hemp1, %Hwon1, %Hlost1⟩
  · ipureintro; exact Hsz0
  ihave c := Hcback $$ Hc0
  icases array_acc_same' (GF := GF) _ (sint.Z (W64 1)) _ _ _ v1 (by decide)
      (by simp [Harr]) $$ c with ⟨Hc1, Hcback⟩
  ihave Hv1 := ownIdsetQ_toMaj _ _ $$ Hv1
  wp_apply wp_MajorityConfig_VoteResult s1 $$ [$Hc1 $Hvotes $Hv1]
    as %r2 ⟨Hc1, Hvotes, Hv1, %Hr2, %Hemp2, %Hwon2, %Hlost2⟩
  · ipureintro; exact Hsz1
  ihave c := Hcback $$ Hc1
  ihave Hv0 := ownIdsetQ_ofMaj _ _ $$ Hv0
  ihave Hv1 := ownIdsetQ_ofMaj _ _ $$ Hv1
  obtain ⟨Hw1, Hl1⟩ := majVote_facts r1 s0 _ _ Hr1 Hemp1 Hwon1 Hlost1
  obtain ⟨Hw2, Hl2⟩ := majVote_facts r2 s1 _ _ Hr2 Hemp2 Hwon2 Hlost2
  rw [show quorum.VoteLost = #VoteLost from rfl, show quorum.VotePending = #VotePending from rfl]
  have Hf := jointVote_facts r1 r2 Hr1 Hr2
  by_cases h12 : r1 = r2
  · rw [decide_eq_true h12]
    wp_auto
    iapply HΦ
    iframe Hc Hv0 Hv1 Hvotes
    ipureintro
    rw [if_pos h12] at Hf
    exact ⟨Hf.1, Hf.2.1.trans (and_congr Hw1 Hw2), Hf.2.2.trans (or_congr Hl1 Hl2)⟩
  · rw [decide_eq_false h12]
    wp_auto
    rw [if_neg h12] at Hf
    by_cases h1L : r1 = VoteLost
    · rw [decide_eq_true h1L]
      wp_auto
      iapply HΦ
      iframe Hc Hv0 Hv1 Hvotes
      ipureintro
      rw [if_pos (Or.inl h1L : r1 = VoteLost ∨ r2 = VoteLost)] at Hf
      exact ⟨Hf.1, Hf.2.1.trans (and_congr Hw1 Hw2), Hf.2.2.trans (or_congr Hl1 Hl2)⟩
    · rw [decide_eq_false h1L]
      wp_auto
      by_cases h2L : r2 = VoteLost
      · rw [decide_eq_true h2L]
        wp_auto
        iapply HΦ
        iframe Hc Hv0 Hv1 Hvotes
        ipureintro
        rw [if_pos (Or.inr h2L : r1 = VoteLost ∨ r2 = VoteLost)] at Hf
        exact ⟨Hf.1, Hf.2.1.trans (and_congr Hw1 Hw2), Hf.2.2.trans (or_congr Hl1 Hl2)⟩
      · rw [decide_eq_false h2L]
        wp_auto
        iapply HΦ
        iframe Hc Hv0 Hv1 Hvotes
        ipureintro
        have hn : ¬ (r1 = VoteLost ∨ r2 = VoteLost) := fun h => h.elim h1L h2L
        rw [if_neg hn] at Hf
        exact ⟨Hf.1, Hf.2.1.trans (and_congr Hw1 Hw2), Hf.2.2.trans (or_congr Hl1 Hl2)⟩

end proof

end EtcdGrove
end Perennial
