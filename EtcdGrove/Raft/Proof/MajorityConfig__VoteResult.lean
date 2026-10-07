/-
Port of election_proof/proof_MajorityConfig__VoteResult.v.

Lean notes: Rocq's helper file `proof_MajorityConfig__VoteResult_helpers/majority_len.v`
is not ported: Perennial's `wp_map_len` and `pure_wp_map_nil_len` are stated at any
type whose underlying type is a map, so they apply at `quorum.MajorityConfig.ty`
directly (its `wp_MajorityConfig_len` and `wp_MajorityConfig_nil_len`).
-/
import EtcdGrove.Raft.Spec.MajorityConfig__VoteResult

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

/-- The three exits of `MajorityConfig.VoteResult`, in the order the body
takes them: `len(c) == 0` (both for the nil map and for a real empty
one), then `votedCnt >= q`, then `votedCnt + missing >= q`, then
`VoteLost`. The map range counts two things at once: `nsat Pgr` is
`votedCnt` and `nsat Pms` is `missing`, and `nsat_granted` /
`nsat_missing` (`InvTracker.lean`) turn them into set cardinalities when
the range is over. See `Spec/MajorityConfig__VoteResult.lean` for the
arithmetic.

Lean notes: Rocq's `wp_MajorityConfig_len` is Perennial's `wp_map_len` at
`t := quorum.MajorityConfig.ty`, and `wp_MajorityConfig_nil_len` is the `PureWp`
instance `pure_wp_map_nil_len`, which `wp_auto` uses. -/
theorem quorum.MajorityConfig.VoteResult.wp_proof :
    quorum.MajorityConfig.VoteResult.spec (GF := GF) (hG := hG) := by
  intro s cref mref votes_ref dq votes
  wp_start as ⟨%Hsz, Hc, Hvotes, Hm⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  icases Hm with (⟨%Hnil, %Hs⟩ | ⟨%ids, %Hids, Hids⟩)
  · -- the nil component of a simple config: `len(c) == 0`, so `VoteWon`.
    subst Hnil Hs
    wp_auto
    rw [show quorum.VoteWon = #VoteWon from rfl]
    iapply HΦ $$ %VoteWon
    iframe Hc Hvotes
    isplitr
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
    ipureintro
    exact ⟨Or.inl rfl, fun _ => rfl, fun h => absurd rfl h, fun h => absurd rfl h⟩
  wp_apply wp_map_len (t := quorum.MajorityConfig.ty) $$ Hids as Hids
  have Hsize : GMap.size ids = GMap.size s := by rw [← Hids, GMap.size_dom]
  rw [Hsize]
  by_cases Hne : s = ∅
  · -- a real but *empty* map: `len(c) == 0` too, so `VoteWon` again
    subst Hne
    rw [GMap.map_size_empty]
    wp_auto
    rw [show quorum.VoteWon = #VoteWon from rfl]
    iapply HΦ $$ %VoteWon
    iframe Hc Hvotes
    isplitl [Hids]
    · iright
      iexists ids
      iframe Hids
      ipureintro; exact Hids
    ipureintro
    exact ⟨Or.inl rfl, fun _ => rfl, fun h => absurd rfl h, fun h => absurd rfl h⟩
  -- `len(c) == 0` is false: this component is non-empty
  have Hpos : 0 < GMap.size s := by
    rcases Nat.eq_zero_or_pos (GMap.size s) with h | h
    · exact absurd (GMap.map_size_empty_inv _ h) Hne
    · exact h
  rw [decide_eq_false (by word)]
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (idv : w64),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "Hvotes" ∷ votes_ref ↦${dq} votes ∗
      "votes" ∷ votes_ptr ↦ votes_ref ∗
      "id" ∷ id_ptr ↦ idv ∗
      "votedCnt" ∷ votedCnt_ptr ↦ W64 (nsat (fun k => votes !! k = some true) (keys.take i.toNat)) ∗
      "missing" ∷ missing_ptr ↦ W64 (nsat (fun k => votes !! k = none) (keys.take i.toNat)))) $$ Hids
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hvotes votes id votedCnt missing]
  · iexists zero_val w64
    simp only [Int.toNat_zero, List.take_zero]
    iframe
    ipureintro
    omega
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    have Hilt : i.toNat < keys.length := (List.getElem?_eq_some_iff.1 Hkey).1
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    have Hlen : (keys.take i.toNat).length < GMap.size s := by
      rw [List.length_take]; omega
    have HgB := nsat_le (fun k => votes !! k = some true) (keys.take i.toNat)
    have HmB := nsat_le (fun k => votes !! k = none) (keys.take i.toNat)
    wp_auto
    wp_apply wp_map_lookup2 $$ Hvotes as Hvotes
    rw [Htake, nsat_snoc, nsat_snoc]
    cases Hvk : votes !! key with
    | none =>
      -- no answer: `missing++; continue`
      wp_auto
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists key
      simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero]
      rw [show (W64 ((nsat (fun k => votes !! k = none) (keys.take i.toNat) + 1 : Nat) : Int)) =
          W64 ((nsat (fun k => votes !! k = none) (keys.take i.toNat) : Nat) : Int) + W64 1 by word]
      iframe
      ipureintro
      omega
    | some b =>
      cases b with
      | true =>
        -- granted
        simp only [Option.getD_some]
        wp_auto
        unfold forMapPostcondition
        iright
        ileft
        isplitr
        · ipureintro; rfl
        iexists key
        simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero]
        rw [show (W64 ((nsat (fun k => votes !! k = some true) (keys.take i.toNat) + 1 : Nat) : Int)) =
            W64 ((nsat (fun k => votes !! k = some true) (keys.take i.toNat) : Nat) : Int) + W64 1
            by word]
        iframe
        ipureintro
        omega
      | false =>
        -- rejected: neither counter moves
        simp only [Option.getD_some]
        wp_auto
        unfold forMapPostcondition
        iright
        ileft
        isplitr
        · ipureintro; rfl
        iexists key
        simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero, Option.some.injEq, Bool.false_eq_true]
        iframe
        ipureintro
        omega
  -- the range is over: the two counters hold the whole tally
  iintro HP Hids
  iNamed HP
  rw [show ((GMap.size ids : Int)).toNat = keys.length by omega, List.take_length]
  have Hks : GMap.listToSet keys = s := by
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_list_to_set, Hkset, ← Hids, GMap.elem_of_dom']
    rfl
  have Hgfin := nsat_granted s votes keys Hknodup Hks
  have Hmfin := nsat_missing s votes keys Hknodup Hks
  wp_auto
  wp_apply wp_map_len (t := quorum.MajorityConfig.ty) $$ Hids as Hids
  rw [Hsize]
  -- `q := len(c)/2 + 1`, then the two comparisons. Everything below is
  -- arithmetic: `IsQuorum_alt` is the bridge to the model.
  have Hgm : nsat (fun k => votes !! k = some true) keys + nsat (fun k => votes !! k = none) keys
      = GMap.size (s \ rejected votes) := by
    rw [Hgfin, Hmfin, size_cfg_minus_rejected]
  have Hsub : GMap.size (s \ rejected votes) ≤ GMap.size s :=
    GMap.subseteq_size (GMap.difference_subseteq _ _)
  have HgB : GMap.size (granted votes ∩ s) ≤ GMap.size s := by
    apply GMap.subseteq_size
    rw [GMap.elem_of_subseteq]; intro k Hk; exact ((GMap.elem_of_intersection _ _ _).1 Hk).2
  have Hint : (s \ rejected votes) ∩ s = s \ rejected votes := by
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_intersection, GMap.elem_of_difference]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  rw [Hgfin] at Hgm ⊢
  have HM := Hgm
  by_cases Hwon : GMap.size s / 2 + 1 ≤ GMap.size (granted votes ∩ s)
  · -- `votedCnt >= q`: a quorum granted
    rw [decide_eq_true (by word)]
    wp_auto
    rw [show quorum.VoteWon = #VoteWon from rfl]
    iapply HΦ $$ %VoteWon
    iframe Hc Hvotes
    isplitl [Hids]
    · iright; iexists ids; iframe Hids; ipureintro; exact Hids
    ipureintro
    refine ⟨Or.inl rfl, fun h => absurd h Hne,
      fun _ => ⟨fun _ => (IsQuorum_alt s _).2 Hwon, fun _ => rfl⟩,
      fun _ => ⟨fun h => absurd h (by decide),
        fun Hnq => absurd ((IsQuorum_alt s _).2 (by rw [Hint]; omega)) Hnq⟩⟩
  rw [decide_eq_false (by word)]
  wp_auto
  by_cases Hpend : GMap.size s / 2 + 1 ≤ GMap.size (s \ rejected votes)
  · -- `votedCnt + missing >= q`: the election is still winnable
    rw [decide_eq_true (by word)]
    wp_auto
    rw [show quorum.VotePending = #VotePending from rfl]
    iapply HΦ $$ %VotePending
    iframe Hc Hvotes
    isplitl [Hids]
    · iright; iexists ids; iframe Hids; ipureintro; exact Hids
    ipureintro
    refine ⟨Or.inr (Or.inr rfl), fun h => absurd h Hne,
      fun _ => ⟨fun h => absurd h (by decide),
        fun Hqg => absurd ((IsQuorum_alt s _).1 Hqg) (by omega)⟩,
      fun _ => ⟨fun h => absurd h (by decide),
        fun Hnq => absurd ((IsQuorum_alt s _).2 (by rw [Hint]; omega)) Hnq⟩⟩
  rw [decide_eq_false (by word)]
  wp_auto
  -- `votedCnt + missing < q`: the candidate cannot still win
  rw [show quorum.VoteLost = #VoteLost from rfl]
  iapply HΦ $$ %VoteLost
  iframe Hc Hvotes
  isplitl [Hids]
  · iright; iexists ids; iframe Hids; ipureintro; exact Hids
  ipureintro
  refine ⟨Or.inr (Or.inl rfl), fun h => absurd h Hne,
    fun _ => ⟨fun h => absurd h (by decide),
      fun Hqg => absurd ((IsQuorum_alt s _).1 Hqg) (by omega)⟩,
    fun _ => ⟨fun _ => fun Hq' => absurd ((IsQuorum_alt s _).1 Hq') (by rw [Hint]; omega),
      fun _ => rfl⟩⟩

end proof

end EtcdGrove
end Perennial
