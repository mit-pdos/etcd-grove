module

public import RaftWitness.Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__VoteResultWithDifference

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `array_acc`, putting back the same element (as `JointConfig__VoteResult.lean`'s). -/
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

theorem quorum.MajorityConfig.VoteResultWithDifference.wp_proof :
    quorum.MajorityConfig.VoteResultWithDifference.spec (GF := GF) (hG := hG) := by
  intro s cref mref votes_ref dq votes
  wp_start as ⟨%Hsz, Hc, Hvotes, Hm⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  icases Hm with (⟨%Hnil, %Hs⟩ | ⟨%ids, %Hids, Hids⟩)
  · subst Hnil Hs
    wp_auto
    rw [show quorum.VoteWon = #VoteWon from rfl]
    wp_auto
    iapply HΦ $$ %VoteWon %(W64 0)
    iframe Hc Hvotes
    isplitr
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
    ipureintro
    refine ⟨Or.inl rfl, fun _ => rfl, fun h => absurd rfl h, fun h => absurd rfl h, ?_⟩
    simp [votesToWin, MajQ]
  wp_apply wp_map_len (t := quorum.MajorityConfig.ty) $$ Hids as Hids
  have Hsize : GMap.size ids = GMap.size s := by rw [← Hids, GMap.size_dom]
  rw [Hsize]
  by_cases Hne : s = ∅
  · subst Hne
    rw [GMap.map_size_empty]
    wp_auto
    rw [show quorum.VoteWon = #VoteWon from rfl]
    wp_auto
    iapply HΦ $$ %VoteWon %(W64 0)
    iframe Hc Hvotes
    isplitl [Hids]
    · iright
      iexists ids
      iframe Hids
      ipureintro; exact Hids
    ipureintro
    refine ⟨Or.inl rfl, fun _ => rfl, fun h => absurd rfl h, fun h => absurd rfl h, ?_⟩
    simp [votesToWin, MajQ]
  have Hpos : 0 < GMap.size s := by
    rcases Nat.eq_zero_or_pos (GMap.size s) with h | h
    · exact absurd (GMap.map_size_empty_inv _ h) Hne
    · exact h
  rw [decide_eq_false (by word)]
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (idv nno : w64),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "Hvotes" ∷ votes_ref ↦${dq} votes ∗
      "votes" ∷ votes_ptr ↦ votes_ref ∗
      "id" ∷ id_ptr ↦ idv ∗
      "ny" ∷ ny_ptr ↦ (array.mk 2 [nno,
          W64 (nsat (fun k => votes !! k = some true) (keys.take i.toNat))] : GoArray w64 2) ∗
      "missing" ∷ missing_ptr ↦ W64 (nsat (fun k => votes !! k = none) (keys.take i.toNat)))) $$ Hids
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hvotes votes id ny missing]
  · iexists zero_val w64, W64 0
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
      wp_auto
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists key, nno
      simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero]
      rw [show (W64 ((nsat (fun k => votes !! k = none) (keys.take i.toNat) + 1 : Nat) : Int)) =
          W64 ((nsat (fun k => votes !! k = none) (keys.take i.toNat) : Nat) : Int) + W64 1 by word]
      iframe
      ipureintro
      omega
    | some b =>
      cases b with
      | true =>
        simp only [Option.getD_some]
        wp_auto
        icases array_acc (GF := GF) ny_ptr (sint.Z (W64 1)) _ _ _ _ (by decide) (by rfl) $$ ny
          with ⟨Hny1, Hnyback⟩
        wp_auto
        ihave ny := Hnyback $$ Hny1
        unfold forMapPostcondition
        iright
        ileft
        isplitr
        · ipureintro; rfl
        iexists key, nno
        simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero]
        rw [show (W64 ((nsat (fun k => votes !! k = some true) (keys.take i.toNat) + 1 : Nat) : Int)) =
            W64 ((nsat (fun k => votes !! k = some true) (keys.take i.toNat) : Nat) : Int) + W64 1
            by word]
        iframe
        ipureintro; omega
      | false =>
        simp only [Option.getD_some]
        wp_auto
        icases array_acc (GF := GF) ny_ptr (sint.Z (W64 0)) _ _ _ _ (by decide) (by rfl) $$ ny
          with ⟨Hny0, Hnyback⟩
        wp_auto
        ihave ny := Hnyback $$ Hny0
        unfold forMapPostcondition
        iright
        ileft
        isplitr
        · ipureintro; rfl
        iexists key, nno + W64 1
        simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero, Option.some.injEq, Bool.false_eq_true]
        iframe
        ipureintro
        omega
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
  icases array_acc_same' (GF := GF) ny_ptr (sint.Z (W64 1)) _ _ _ _ (by decide) (by rfl) $$ ny
    with ⟨Hny1, Hnyback⟩
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
  have HQg : MajQ s (granted votes) ↔ GMap.size s / 2 + 1 ≤ GMap.size (granted votes ∩ s) := by
    rw [MajQ_of_ne _ Hne, IsQuorum_alt]
  have HQr : MajQ s (s \ rejected votes) ↔ GMap.size s / 2 + 1 ≤ GMap.size (s \ rejected votes) := by
    rw [MajQ_of_ne _ Hne, IsQuorum_alt, Hint]
  wp_auto
  by_cases Hwon : GMap.size s / 2 + 1 ≤ GMap.size (granted votes ∩ s)
  · rw [decide_eq_true (by word)]
    wp_auto
    rw [show quorum.VoteWon = #VoteWon from rfl]
    wp_auto
    iapply HΦ $$ %VoteWon %(W64 0)
    iframe Hc Hvotes
    isplitl [Hids]
    · iright; iexists ids; iframe Hids; ipureintro; exact Hids
    ipureintro
    refine ⟨Or.inl rfl, fun h => absurd h Hne,
      fun _ => ⟨fun _ => (IsQuorum_alt s _).2 Hwon, fun _ => rfl⟩,
      fun _ => ⟨fun h => absurd h (by decide),
        fun Hnq => absurd ((IsQuorum_alt s _).2 (by rw [Hint]; omega)) Hnq⟩, ?_⟩
    unfold votesToWin
    rw [if_pos (Or.inl (HQg.2 Hwon))]; rfl
  rw [decide_eq_false (by word)]
  wp_auto
  by_cases Hpend : GMap.size s / 2 + 1 ≤ GMap.size (s \ rejected votes)
  · rw [decide_eq_true (by word)]
    wp_auto
    rw [show quorum.VotePending = #VotePending from rfl]
    wp_auto
    iapply HΦ $$ %VotePending
    iframe Hc Hvotes
    isplitl [Hids]
    · iright; iexists ids; iframe Hids; ipureintro; exact Hids
    ipureintro
    refine ⟨Or.inr (Or.inr rfl), fun h => absurd h Hne,
      fun _ => ⟨fun h => absurd h (by decide),
        fun Hqg => absurd ((IsQuorum_alt s _).1 Hqg) (by omega)⟩,
      fun _ => ⟨fun h => absurd h (by decide),
        fun Hnq => absurd ((IsQuorum_alt s _).2 (by rw [Hint]; omega)) Hnq⟩, ?_⟩
    unfold votesToWin
    rw [if_neg (by rw [HQg, HQr]; omega)]
    word
  rw [decide_eq_false (by word)]
  wp_auto
  rw [show quorum.VoteLost = #VoteLost from rfl]
  wp_auto
  iapply HΦ $$ %VoteLost %(W64 0)
  iframe Hc Hvotes
  isplitl [Hids]
  · iright; iexists ids; iframe Hids; ipureintro; exact Hids
  ipureintro
  refine ⟨Or.inr (Or.inl rfl), fun h => absurd h Hne,
    fun _ => ⟨fun h => absurd h (by decide),
      fun Hqg => absurd ((IsQuorum_alt s _).1 Hqg) (by omega)⟩,
    fun _ => ⟨fun _ => fun Hq' => absurd ((IsQuorum_alt s _).1 Hq') (by rw [Hint]; omega),
      fun _ => rfl⟩, ?_⟩
  unfold votesToWin
  rw [if_pos (Or.inr (by rw [HQr]; omega))]; rfl

end proof

end EtcdGrove
end Perennial
