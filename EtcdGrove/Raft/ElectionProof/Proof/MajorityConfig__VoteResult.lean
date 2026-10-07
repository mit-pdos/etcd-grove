/-
Port of election_proof/proof_MajorityConfig__VoteResult.v.

Lean notes: Rocq's helper file `proof_MajorityConfig__VoteResult_helpers/majority_len.v`
is not ported: its `wp_MajorityConfig_len` is `wp_map_len` here, and its
`wp_MajorityConfig_nil_len` cannot be proved over Perennial's Lean `len_map`, which reads
the map pointer unconditionally (so the nil-map branch is a `sorry`). The local
`wp_map_for_range_keep` is Perennial's `wp_map_for_range` returning the map points-to.
-/
import EtcdGrove.Raft.ElectionProof.Spec.MajorityConfig__VoteResult

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

/-- `wp_map_for_range` (`Perennial/Golang/Theory/Map.lean`), with the map points-to
handed back when the range runs to completion. Perennial's Lean lemma (a port of an
older Rocq `wp_map_for_range`) drops it after the final `FinishRead`; the Rocq proof
at feb5c73d4 uses a version that returns it (`iIntros "HP Hids"`), and this proof
needs it, since `len(c)` is read again after the loop and the postcondition hands
`mref ↦$ ids` back. The proof is Perennial's, with the points-to re-sealed at the end.
(A `break`/`return` from the body still drops it, as there.) -/
private theorem wp_map_for_range_keep {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V]
    [go.IntoValInj K] {s : Stuckness} {E : CoPset} (P : List K → Int → IProp GF) (body : GoFunc)
    (key_type elem_type : go.GoType) (mref : Loc) (m : GMap K V) (dq : DFrac)
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K key_type] (Φ : val → IProp GF) :
    (mref ↦${dq} m : IProp GF) -∗
    (∀ keys : List K,
      ⌜(∀ k, k ∈ keys ↔ (m !! k).isSome) ∧ keys.length = GMap.size m ∧ keys.Nodup⌝ -∗
      (P keys 0 ∗
       □ (∀ (i : Int) (key : K) (v : V), ⌜keys[i.toNat]? = some key ∧ m !! key = some v⌝ -∗
          P keys i -∗
          WP (App (App (Val #body) (Val #key)) (Val #v)) @ s; E
            {{ v, forMapPostcondition (P keys (i + 1)) Φ v }}) ∗
       (P keys (GMap.size m) -∗ mref ↦${dq} m -∗ Φ executeVal))) -∗
    WP (App (App (Val (map.forRange key_type elem_type)) (Val #mref)) (Val #body)) @ s; E {{ Φ }} := by
  iintro Hm HΦ
  ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
  wp_call
  rw [decide_eq_false Hnn]
  wp_pures
  rw [ownMap_unseal]
  iNamed Hm
  wp_apply wp_start_read $$ Hown with ⟨Hown, Hclose⟩
  wp_bind (App (Val (GoInstruction (InternalMapForRange key_type elem_type))) _)
  iapply wp_InternalMapForRange mv mp #body key_type elem_type _ $$ %His_map
  iintro %e' %He'
  rw [go.internal_map_domain_literal_step_pure mv mp #body key_type elem_type His_map] at He'
  obtain ⟨ks, hks, rfl⟩ := He'
  obtain ⟨Hnodup, Hks⟩ := go.is_map_domain_pure mv mp ks His_map hks
  obtain ⟨keys, rfl⟩ := list_exists_map_of_forall (intoVal (V := K)) ks
    (fun kv hkv => Hdom kv ((Hks kv).2 hkv))
  have Hmem : ∀ k, k ∈ keys ↔ (m !! k).isSome := by
    intro k
    rw [← list_mem_map_inj (intoVal (V := K)) go.intoVal_inj, ← Hks, Hagree k]
    cases m !! k <;> simp
  have Hnd : keys.Nodup := list_nodup_of_map _ _ Hnodup
  have Hsize : keys.length = GMap.size m := (GMap.size_eq_length m keys Hnd Hmem).symm
  icases HΦ $$ %keys %(⟨Hmem, Hsize, Hnd⟩) with ⟨HP, #Hiter, HΦ⟩
  obtain ⟨i, hi⟩ : ∃ i : Nat, i = 0 := ⟨0, rfl⟩
  have hile : i ≤ keys.length := by omega
  rw [show List.map intoVal keys = List.map intoVal (keys.drop i) by rw [hi, List.drop_zero],
    show P keys 0 = P keys (i : Int) by rw [hi]; rfl]
  clear hi
  iloeb as IH generalizing %i %hile
  by_cases hlt : i < keys.length
  · have hkey : keys[i]? = some keys[i] := List.getElem?_eq_getElem hlt
    obtain ⟨v, hv⟩ : ∃ v, m !! keys[i] = some v :=
      Option.isSome_iff_exists.1 ((Hmem _).1 (List.getElem_mem hlt))
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.foldr_cons]
    simp only [Hagree keys[i], hv]
    ihave Hb := Hiter $$ %(i : Int) %(keys[i]) %v %(⟨by simpa using hkey, hv⟩) HP
    wp_bind (App (App (Val #body) (Val #(keys[i]))) (Val #v))
    iapply wp_wand $$ Hb
    iintro %bv Hpost
    unfold forMapPostcondition
    have hcast : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by push_cast; rfl
    icases Hpost with (⟨%hbv, HP⟩ | ⟨%hbv, HP⟩ | ⟨%hbv, HΦ'⟩ | ⟨%v', %hbv, HΦ'⟩)
    · subst hbv
      rw [continueVal_unseal]; simp only [continueValDef]
      wp_auto
      rw [← hcast]
      iapply IH $$ %(i + 1) %(by omega) Hown Hclose HP HΦ
    · subst hbv
      rw [executeVal_unseal]; simp only [executeValDef]
      wp_auto
      rw [← hcast]
      iapply IH $$ %(i + 1) %(by omega) Hown Hclose HP HΦ
    · subst hbv
      rw [breakVal_unseal]; simp only [breakValDef]
      wp_auto
      wp_apply wp_finish_read $$ [Hown Hclose] with _
      · iframe Hown Hclose
      iexact HΦ'
    · subst hbv
      rw [returnVal_unseal]; simp only [returnValDef]
      wp_auto
      wp_apply wp_finish_read $$ [Hown Hclose] with _
      · iframe Hown Hclose
      iexact HΦ'
  · rw [List.drop_of_length_le (by omega)]
    simp only [List.map_nil, List.foldr_nil]
    wp_auto
    wp_apply wp_finish_read $$ [Hown Hclose] with Hown
    · iframe Hown Hclose
    have hsz : (i : Int) = (GMap.size m : Int) := by omega
    rw [hsz]
    iapply HΦ $$ HP
    unfold ownMapDef
    iexists mv, mp
    simp only [named]
    iframe Hown
    ipureintro
    exact ⟨His_map, Hagree, Hdom, Hdefault⟩


/-- The three exits of `MajorityConfig.VoteResult`, in the order the body
takes them: `len(c) == 0` (both for the nil map and for a real empty
one), then `votedCnt >= q`, then `votedCnt + missing >= q`, then
`VoteLost`. The map range counts two things at once: `nsat Pgr` is
`votedCnt` and `nsat Pms` is `missing`, and `nsat_granted` /
`nsat_missing` (`InvTracker.lean`) turn them into set cardinalities when
the range is over. See `Spec/MajorityConfig__VoteResult.lean` for the
arithmetic.

Lean notes: Rocq's `wp_MajorityConfig_len` is Perennial's `wp_map_len` at
`t := quorum.MajorityConfig.ty` (stated at any type whose underlying type is a map).
Rocq's `wp_MajorityConfig_nil_len` has no Lean counterpart (see the `sorry` in the nil
case). The range uses `wp_map_for_range_keep` above. -/
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
    -- NOT PROVABLE in the Lean semantics as it stands: Perennial's Lean `len_map`
    -- (`Perennial/Golang/Defn/Map.lean`) unfolds `len(m)` to
    -- `InternalMapLength (Read m)`, which reads the map pointer unconditionally, so
    -- `len` of `map.nil` (a null pointer, nothing owned) is stuck; Rocq at feb5c73d4
    -- steps it with `pure_wp_map_nil_len` (`wp_MajorityConfig_nil_len`,
    -- `proof_MajorityConfig__VoteResult_helpers/majority_len.v`), which the Lean port of
    -- Perennial does not have (`wp_map_len`'s docstring: "`len` of a nil map is not
    -- covered"). What is left: `WP` of the body at `mref = map.nil`, `s = ∅`; the rest
    -- would be the `VoteWon` exit as in the empty-map case below.
    sorry
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
  iapply wp_map_for_range_keep (fun (keys : List w64) (i : Int) => iprop(∃ (idv : w64),
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
