/-
Port of election_proof/proof_ProgressTracker__TallyVotes.v.
-/
import EtcdGrove.Raft.Spec.ProgressTracker__TallyVotes
import EtcdGrove.Raft.Spec.JointConfig__VoteResult

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

/-- The range over `trk.Progress` counts granted and rejected votes (Lean note: the
counters are not in the postcondition, so their final values -- `nsat` over the
enumeration, which `nsat_granted`/`nsat_rejected` turn into set sizes -- are not
needed); the verdict is `JointConfig.VoteResult`'s. -/
theorem tracker.ProgressTracker.TallyVotes.wp_proof
    (wp_JointConfig_VoteResult : quorum.JointConfig.VoteResult.spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.TallyVotes.spec (GF := GF) (hG := hG) := by
  intro cfg trk tv t Hcfg_ne
  obtain ⟨votes, prs, pvs⟩ := t
  wp_start as ⟨Htrk, Hown⟩
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  dsimp only at Hprs_dom
  -- the `var _ quorum.VoteResult` declaration Go emits for the named return
  -- is an *anonymous* `GoAlloc`, which `wp_auto` will not step past.
  wp_alloc res0 as Hres0
  wp_auto
  -- `pr` and `id` are the range's own loop variables: the body assigns them
  -- on every iteration, so they must be existentially quantified *inside*
  -- the invariant -- the same trap `raft.campaign` documents for
  -- `slice.for_range`.
  let Pgr : w64 → Prop := fun k => votes !! k = some true
  let Prj : w64 → Prop := fun k => votes !! k = some false
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (prv : Loc) (idv : w64),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "Htrk" ∷ trk ↦ tv ∗
      "Hvotes" ∷ tv.Votes' ↦$ votes ∗
      "Hprogs" ∷ ([∗map] _k ↦ pr;p ∈ prs;pvs, ownProgress pr p) ∗
      "p" ∷ p_ptr ↦ trk ∗
      "pr" ∷ pr_ptr ↦ prv ∗
      "id" ∷ id_ptr ↦ idv ∗
      "granted" ∷ granted_ptr ↦ W64 (nsat Pgr (keys.take i.toNat)) ∗
      "rejected" ∷ rejected_ptr ↦ W64 (nsat Prj (keys.take i.toNat)))) $$ Hprs
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Htrk Hvotes Hprogs p pr id granted rejected]
  · iexists null, W64 0
    simp only [Int.toNat_zero, List.take_zero]
    iframe
    ipureintro
    omega
  isplitr
  · imodintro
    iintro %i %key %prl ⟨%Hkey, %Hprl⟩ HP
    iNamed HP
    dsimp only at Hprl Hkset Hklen
    ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
    obtain ⟨pk, Hpvk⟩ := Option.isSome_iff_exists.1
      ((Hiff key).1 (by show (prs !! key).isSome = true; rw [Hprl]; rfl))
    icases BigSepM2.bigSepM2_lookup_acc (Φ := fun _ pr p => ownProgress (GF := GF) pr p)
      (m1 := prs) (m2 := pvs) Hprl Hpvk $$ Hprogs with ⟨Hpr, Hback⟩
    iNamed Hpr
    have Hnolearner := ((progressAbs_Some _ _ _).1 Habs).1
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    have Hszprs : GMap.size prs = GMap.size cfg := by rw [← Hprs_dom, GMap.size_dom]
    -- the counters are bounded by `size cfg`, which is what lets `word` see
    -- that `granted + 1` does not wrap
    have HgB : nsat Pgr (keys.take i.toNat) ≤ GMap.size cfg := by
      refine Nat.le_trans (nsat_le _ _) ?_
      rw [List.length_take]; omega
    have HrB : nsat Prj (keys.take i.toNat) ≤ GMap.size cfg := by
      refine Nat.le_trans (nsat_le _ _) ?_
      rw [List.length_take]; omega
    wp_auto
    -- `if pr.IsLearner { continue }`: no voter is a learner, and without
    -- `Hnolearner` the `if` scrutinee is not a literal and `wp_auto` parks.
    rw [Hnolearner]
    wp_auto
    wp_apply wp_map_lookup2 $$ Hvotes as Hvotes
    ihave Hprogs := Hback $$ [Hpv Hinfl]
    · unfold ownProgress
      iexists pv
      iframe Hpv Hinfl
      ipureintro; exact Habs
    unfold forMapPostcondition
    cases Hvk : votes !! key with
    | some b =>
      cases b with
      | true =>
        -- granted
        have HPg : Pgr key := Hvk
        have HPr : ¬ Prj key := by simp only [Prj, Hvk]; decide
        simp only [Option.isSome_some, decide_true, Option.getD_some]
        wp_auto
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists prl, key
        rw [Htake, nsat_snoc, nsat_snoc]
        simp only [HPg, HPr, ↓reduceIte, Nat.add_zero]
        rw [show (W64 ((nsat Pgr (keys.take i.toNat) + 1 : Nat) : Int) : w64) =
            W64 (nsat Pgr (keys.take i.toNat) : Int) + W64 1 by word]
        iframe
        ipureintro; omega
      | false =>
        -- rejected
        have HPg : ¬ Pgr key := by simp only [Pgr, Hvk]; decide
        have HPr : Prj key := Hvk
        simp only [Option.isSome_some, decide_true, Option.getD_some]
        wp_auto
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists prl, key
        rw [Htake, nsat_snoc, nsat_snoc]
        simp only [HPg, HPr, ↓reduceIte, Nat.add_zero]
        rw [show (W64 ((nsat Prj (keys.take i.toNat) + 1 : Nat) : Int) : w64) =
            W64 (nsat Prj (keys.take i.toNat) : Int) + W64 1 by word]
        iframe
        ipureintro; omega
    | none =>
      -- this voter has not answered: `continue`, both counters unchanged
      have HPg : ¬ Pgr key := by simp only [Pgr, Hvk]; decide
      have HPr : ¬ Prj key := by simp only [Prj, Hvk]; decide
      simp only [Option.isSome_none]
      wp_auto
      ileft
      isplitr
      · ipureintro; rfl
      iexists prl, key
      rw [Htake, nsat_snoc, nsat_snoc]
      simp only [HPg, HPr, ↓reduceIte, Nat.add_zero]
      iframe
      ipureintro; omega
  -- the range is over, so the counters hold the whole tally
  iintro HP -
  iNamed HP
  dsimp only at Hklen
  rw [← Hklen, Int.toNat_natCast, List.take_length]
  wp_auto
  -- `p.Config.Voters.VoteResult(p.Votes)`: re-seal the tracker and ask the
  -- joint quorum. The two counters already hold the model's numbers.
  ihave Hown := ownTracker_intro cfg tv votes prs pvs voters_ref voters
    learners learnersNext Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size
    HmaxInfl $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext
  wp_apply wp_JointConfig_VoteResult cfg trk tv ⟨votes, prs, pvs⟩ Hcfg_ne $$ [$Htrk $Hown]
    as %res ⟨Htrk, Hown, %Hres, %Hwon, %Hlost⟩
  iapply HΦ
  iframe Htrk Hown
  ipureintro
  exact ⟨Hres, Hwon.1, Hlost.1⟩

end proof

end EtcdGrove
end Perennial
