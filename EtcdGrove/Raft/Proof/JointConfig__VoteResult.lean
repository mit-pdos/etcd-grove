/-
Port of election_proof/proof_JointConfig__VoteResult.v.

Lean notes: Perennial's `array_acc_same` (`v3_proof/readonly.lean`, which cannot be
imported here) is restated locally as `array_acc_same'` (as in
`Proof/JointConfig__CommittedIndex.lean`). Rocq's `w8_absurd` is `decide` on the two
`VoteResult` constants.
-/
import EtcdGrove.Raft.Spec.JointConfig__VoteResult
import EtcdGrove.Raft.Spec.MajorityConfig__VoteResult

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

/-- Both components are asked, and the second is `map.nil` -- an empty config, whose
result is `VoteWon` by convention -- so the combination returns `r1` on all three
paths. The array element reads go through `array_acc_same'`
(`Perennial/Golang/Theory/Array.lean`), exactly as in `Proof/JointConfig__CommittedIndex.lean`;
`Hvoters_arr` says element 0 is `voters_ref` and element 1 is `map.nil`. -/
theorem quorum.JointConfig.VoteResult.wp_proof
    (wp_MajorityConfig_VoteResult : quorum.MajorityConfig.VoteResult.spec (GF := GF) (hG := hG)) :
    quorum.JointConfig.VoteResult.spec (GF := GF) (hG := hG) := by
  intro cfg trk tv t Hcfg_ne
  obtain ⟨votes, prs, pvs⟩ := t
  wp_start as ⟨Htrk, Hown⟩
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  wp_auto
  wp_method_call
  wp_call
  wp_call
  wp_auto
  icases array_acc_same' (GF := GF) _ (sint.Z (W64 0)) _ _ _ voters_ref (by decide)
      (by simp [Hvoters_arr]) $$ c with ⟨Hc0, Hcback⟩
  wp_apply wp_MajorityConfig_VoteResult cfg $$ [$Hc0 $Hvotes Hvoters]
    as %r1 ⟨Hc0, Hvotes, Hv, %Hr1, -, %Hwon1, %Hlost1⟩
  · isplitr
    · ipureintro; omega
    iright
    iexists voters
    iframe
    ipureintro; exact Hvoters_dom
  -- the first component is the real voter set, so the `map.nil` disjunct of
  -- `MajorityConfig.VoteResult`'s postcondition would give `cfg = ∅`
  icases Hv with (⟨-, %Hemp⟩ | ⟨%voters', %Hvoters'_dom, Hvoters⟩)
  · exact absurd Hemp Hcfg_ne
  -- `c[1]`: the nil component of a simple configuration
  ihave c := Hcback $$ Hc0
  icases array_acc_same' (GF := GF) _ (sint.Z (W64 1)) _ _ _ map.nil (by decide)
      (by simp [Hvoters_arr]) $$ c with ⟨Hc1, Hcback⟩
  wp_apply wp_MajorityConfig_VoteResult ∅ $$ [$Hc1 $Hvotes]
    as %r2 ⟨Hc1, Hvotes, -, %Hr2, %Hr2won, -, -⟩
  · isplitr
    · ipureintro; rw [GMap.map_size_empty]; decide
    ileft
    ipureintro; exact ⟨rfl, rfl⟩
  -- "elections on an empty config win": `r2` is `VoteWon`, so the joint answer is `r1`
  -- on every path
  have HN2 : r2 = VoteWon := Hr2won rfl
  subst HN2
  ihave c := Hcback $$ Hc1
  rw [show quorum.VoteLost = #VoteLost from rfl, show quorum.VotePending = #VotePending from rfl]
  ihave Hown := ownTracker_intro cfg tv votes prs pvs voters_ref voters' learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hvoters'_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext
  rcases Hr1 with rfl | rfl | rfl
  · -- `r1 == r2`: both won
    rw [decide_eq_true rfl]
    wp_auto
    iapply HΦ
    iframe Htrk Hown
    ipureintro
    exact ⟨Or.inl rfl, Hwon1 Hcfg_ne, Hlost1 Hcfg_ne⟩
  · -- `r1` lost, `r2` won: the second test fires on `r1`
    rw [decide_eq_false (by decide)]
    wp_auto
    iapply HΦ
    iframe Htrk Hown
    ipureintro
    exact ⟨Or.inr (Or.inl rfl), Hwon1 Hcfg_ne, Hlost1 Hcfg_ne⟩
  · -- `r1` still pending: neither test fires
    rw [decide_eq_false (by decide)]
    wp_auto
    iapply HΦ
    iframe Htrk Hown
    ipureintro
    exact ⟨Or.inr (Or.inr rfl), Hwon1 Hcfg_ne, Hlost1 Hcfg_ne⟩

end proof

end EtcdGrove
end Perennial
