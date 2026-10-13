/-
`tracker.ProgressTracker.QuorumActive`, Lean-first.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__QuorumActive
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Visit
public import Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__VoteResult

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `array_acc`, putting back the same element (as in `JointConfig__VoteResult.lean`). -/
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

/-- `Visit`, with the caller invariant that the local `votes` map has the visited ids as its
domain (and the `Progress` values are unchanged: the closure only reads its `Progress`,
whose `IsLearner` is false by `ownProgress`); then `VoteResult` on the tracker's
`JointConfig`.

`JointConfig.VoteResult` is **inlined** and its two `MajorityConfig.VoteResult` calls are
the callees: `JointConfig.VoteResult.spec` is stated for the tracker's own vote map
(`tv.Votes'`, what `TallyVotes` passes) and cannot be used on the fresh `votes` map here.
The inlined body is that spec's proof (`Proof/.../quorum/JointConfig__VoteResult.lean`)
without its `cfg ≠ ∅` premise: for `cfg = ∅` the first component answers `VoteWon` too. -/
theorem tracker.ProgressTracker.QuorumActive.wp_proof
    (wp_ProgressTracker_Visit : tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG))
    (wp_MajorityConfig_VoteResult : quorum.MajorityConfig.VoteResult.spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.QuorumActive.spec (GF := GF) (hG := hG) := by
  intro cfg trk tv t
  wp_start as ⟨Htrk, Hown⟩
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := Bool) as %vref Hvm
  wp_apply wp_ProgressTracker_Visit cfg _ tv t _
      (fun D pvsx => iprop(∃ (vm : GMap w64 Bool),
        "votes" ∷ votes_ptr ↦ vref ∗
        "Hvm" ∷ vref ↦$ vm ∗
        "%Hdom" ∷ ⌜domSet vm = D⌝ ∗
        "%Hpvs" ∷ ⌜pvsx = t.peers⌝))
    $$ [$Htrk $Hown votes Hvm]
  · isplitl [votes Hvm]
    · iexists ∅
      simp only [named]
      iframe votes Hvm
      ipureintro
      constructor <;> first | exact GMap.dom_empty | trivial
    imodintro
    unfold visitClosure
    iintro %i %pr %tv0 %pvs0 %p %D
    wp_start as ⟨%Hicfg, %Hpri, %Hpvi, %HmaxI, Htrkf, Hpr, Hback, HI⟩
    iNamed HI
    iunfold ownProgress at Hpr
    iNamed Hpr
    have Habs' := (progressAbs_Some _ _ _).1 Habs
    wp_auto
    rw [Habs'.1]
    wp_auto
    wp_apply wp_mapInsert $$ [$Hvm] as Hvm
    ihave Hpr := ownProgress_intro pr pv p $$ Hpv Hinfl []
    · ipureintro; exact Habs
    ihave Htrk := Hback $$ Hpr
    rw [GMap.insert_id pvs0 i p Hpvi]
    iapply HΦ
    iexists tv0, pvs0
    iframe Htrkf Htrk
    iexists (<[i := pv.RecentActive']> vm)
    simp only [named]
    iframe votes Hvm
    ipureintro
    exact ⟨by rw [GMap.dom_insert, Hdom], Hpvs⟩
  iintro ⟨%tvfin, %pvsfin, Htrk, Hown, HI⟩
  iNamed HI
  subst Hpvs
  iNamed Hown
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave %Hvnn := ownMap_not_nil $$ Hvoters
  icases array_acc_same' (GF := GF) _ (sint.Z (W64 0)) _ _ _ voters_ref (by decide)
      (by simp [Hvoters_arr]) $$ c with ⟨Hc0, Hcback⟩
  wp_apply wp_MajorityConfig_VoteResult cfg $$ [$Hc0 $Hvm Hvoters]
    as %r1 ⟨Hc0, Hvm, Hv, %Hr1, %Hemp1, %Hwon1, -⟩
  · isplitr
    · ipureintro; omega
    iright
    iexists voters
    iframe
    ipureintro; exact Hvoters_dom
  icases Hv with (⟨%Hn, -⟩ | ⟨%voters', %Hvoters'_dom, Hvoters⟩)
  · exact absurd Hn Hvnn
  ihave c := Hcback $$ Hc0
  icases array_acc_same' (GF := GF) _ (sint.Z (W64 1)) _ _ _ map.nil (by decide)
      (by simp [Hvoters_arr]) $$ c with ⟨Hc1, Hcback⟩
  wp_apply wp_MajorityConfig_VoteResult ∅ $$ [$Hc1 $Hvm]
    as %r2 ⟨Hc1, Hvm, -, %Hr2, %Hr2won, -, -⟩
  · isplitr
    · ipureintro; rw [GMap.map_size_empty]; decide
    ileft
    ipureintro; exact ⟨rfl, rfl⟩
  have HN2 : r2 = VoteWon := Hr2won rfl
  subst HN2
  ihave Hown := ownTracker_intro cfg tvfin t.votes t.prs t.peers voters_ref voters' learners
    learnersNext Hprs_dom Hvoters_arr Hautoleave Hvoters'_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext
  rw [show quorum.VoteLost = #VoteLost from rfl, show quorum.VotePending = #VotePending from rfl,
    show quorum.VoteWon = #VoteWon from rfl]
  have Hsub : granted vm ⊆ cfg := by
    rw [GMap.elem_of_subseteq]
    intro x hx
    rw [elem_of_granted] at hx
    rw [← Hdom, GMap.elem_of_dom]
    exact ⟨_, hx⟩
  rcases Hr1 with rfl | rfl | rfl
  · rw [decide_eq_true rfl]
    wp_auto
    iapply HΦ $$ %true %tvfin %(granted vm)
    iframe Htrk Hown
    ipureintro
    refine ⟨Hsub, ?_⟩
    simp only [true_iff]
    by_cases Hc : cfg = ∅
    · exact Or.inl Hc
    · exact Or.inr ((Hwon1 Hc).1 rfl)
  · rw [decide_eq_false (by decide)]
    wp_auto
    iapply HΦ $$ %false %tvfin %(granted vm)
    iframe Htrk Hown
    ipureintro
    refine ⟨Hsub, ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    intro H
    by_cases Hc : cfg = ∅
    · exact absurd (Hemp1 Hc) (by decide)
    · rcases H with H | H
      · exact Hc H
      · exact absurd ((Hwon1 Hc).2 H) (by decide)
  · rw [decide_eq_false (by decide)]
    wp_auto
    iapply HΦ $$ %false %tvfin %(granted vm)
    iframe Htrk Hown
    ipureintro
    refine ⟨Hsub, ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    intro H
    by_cases Hc : cfg = ∅
    · exact absurd (Hemp1 Hc) (by decide)
    · rcases H with H | H
      · exact Hc H
      · exact absurd ((Hwon1 Hc).2 H) (by decide)

end proof

end EtcdGrove
end Perennial
