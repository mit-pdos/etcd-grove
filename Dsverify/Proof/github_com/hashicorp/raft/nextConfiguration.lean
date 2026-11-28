/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/nextConfiguration.lean (241f27e).
-/
/-
The proof of `raft.nextConfiguration` (stage 4): the `prevIndex` check, `Clone` (with its capacity), the
switch over the four in-scope changes (`okRes`), then `checkConfiguration`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.nextConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.checkConfiguration
public import Perennial.Proof.fmt.Link
public import Dsverify.Proof.github_com.hashicorp.raft.FmtErrorf

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

/-- (helper) What the switch of `nextConfiguration` leaves (before `checkConfiguration`): servers
`ss2` with distinct IDs among `S`, each valid, fewer than `2^32`, whose voters are adjacent to those of
`ss` (`srvsOkIn` but for having a voter). -/
def nextConfiguration.okRes (S : List SID) (ss ss2 : List Server) : Prop :=
  (srvIds ss2).Nodup ∧ (∀ j ∈ srvIds ss2, j ∈ S) ∧
  (∀ s ∈ ss2, (s.Suffrage' = W64 0 ∨ s.Suffrage' = W64 1) ∧ s.Address' = s.ID' ∧ s.ID' ≠ [] ∧
    s.ID'.length < 2 ^ 63) ∧
  ss2.length < 2 ^ 32 ∧ adjV (srvVoters ss) (srvVoters ss2)

/-- (helper) Membership in the voters. -/
theorem nextConfiguration.mem_srvVoters (l : List Server) (y : SID) :
    y ∈ srvVoters l ↔ ∃ s ∈ l, s.Suffrage' = W64 0 ∧ (s.ID' : List w8) = y := by
  unfold srvVoters
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨s, ⟨hs, hv⟩, he⟩; exact ⟨s, hs, hv, he⟩
  · rintro ⟨s, hs, hv, he⟩; exact ⟨s, ⟨hs, hv⟩, he⟩

/-- (helper) Voter lists that agree but for `x` are adjacent (the first non-empty). -/
theorem nextConfiguration.adjV_of_agree (A B : List SID) (x : SID) (h : ∀ y, y ≠ x → (y ∈ B ↔ y ∈ A))
    (hA : A ≠ []) : adjV A B := by
  by_cases hxB : x ∈ B
  · refine ⟨x, Or.inl fun y => ?_⟩
    by_cases hy : y = x
    · subst hy; simp [hxB]
    · rw [h y hy]; simp [hy]
  by_cases hxA : x ∈ A
  · refine ⟨x, Or.inr fun y => ?_⟩
    by_cases hy : y = x
    · subst hy; simp [hxA]
    · rw [h y hy]; simp [hy]
  · obtain ⟨z, hz⟩ : ∃ z, z ∈ A := by
      cases A with
      | nil => exact absurd rfl hA
      | cons a _ => exact ⟨a, List.mem_cons_self⟩
    have hzx : z ≠ x := fun e => hxA (e ▸ hz)
    refine ⟨z, Or.inl fun y => ?_⟩
    by_cases hy : y = x
    · subst hy
      simp only [hxB, hxA, false_or, false_iff]
      exact fun e => hzx e.symm
    · rw [h y hy]
      constructor
      · exact Or.inl
      · rintro (h' | rfl)
        · exact h'
        · exact hz

/-- (helper) The four shapes of the switch's result (unchanged, one server replaced, one removed,
one appended). -/
theorem nextConfiguration.okRes_same (S : List SID) (ss : List Server) (h : srvsOkIn S ss) : nextConfiguration.okRes S ss ss := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h5, nextConfiguration.adjV_of_agree _ _ [] (fun _ _ => Iff.rfl) h4⟩

theorem nextConfiguration.okRes_set (S : List SID) (ss : List Server) (k : Nat) (sk s' : Server)
    (h : srvsOkIn S ss) (hk : ss[k]? = some sk) (hid : s'.ID' = sk.ID')
    (hsuf : s'.Suffrage' = W64 0 ∨ s'.Suffrage' = W64 1) (hadr : s'.Address' = s'.ID') :
    nextConfiguration.okRes S ss (ss.set k s') := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hskm : sk ∈ ss := List.mem_of_getElem? hk
  have hids : srvIds (ss.set k s') = srvIds ss := by
    apply List.ext_getElem?
    intro i
    unfold srvIds
    simp only [List.getElem?_map, List.getElem?_set]
    by_cases hi : k = i
    · subst hi
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hk
      simp [hid, hlt, heq]
    · simp [hi]
  refine ⟨hids ▸ h1, hids ▸ h2, ?_, by simpa using h5, ?_⟩
  · intro s hs
    rcases List.mem_or_eq_of_mem_set hs with hs | rfl
    · exact h3 s hs
    · obtain ⟨_, _, hne, hlt⟩ := h3 sk hskm
      exact ⟨hsuf, hadr, hid ▸ hne, hid ▸ hlt⟩
  · apply nextConfiguration.adjV_of_agree _ _ (sk.ID' : List w8) _ h4
    intro y hy
    rw [nextConfiguration.mem_srvVoters, nextConfiguration.mem_srvVoters]
    constructor
    · rintro ⟨s, hs, hv, he⟩
      rcases List.mem_or_eq_of_mem_set hs with hs | rfl
      · exact ⟨s, hs, hv, he⟩
      · exact absurd (he ▸ hid) hy
    · rintro ⟨s, hs, hv, he⟩
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hs
      have hik : k ≠ i := by
        rintro rfl
        rw [hk] at hi; cases hi; exact hy he.symm
      exact ⟨s, List.mem_of_getElem? (by rw [List.getElem?_set_ne hik]; exact hi), hv, he⟩

theorem nextConfiguration.okRes_erase (S : List SID) (ss : List Server) (k : Nat) (sk : Server)
    (h : srvsOkIn S ss) (hk : ss[k]? = some sk) :
    nextConfiguration.okRes S ss (ss.eraseIdx k) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hsub : (srvIds (ss.eraseIdx k)).Sublist (srvIds ss) :=
    (List.eraseIdx_sublist ss k).map _
  refine ⟨h1.sublist hsub, fun j hj => h2 j (hsub.subset hj),
    fun s hs => h3 s (List.mem_of_mem_eraseIdx hs), ?_, ?_⟩
  · exact Nat.lt_of_le_of_lt (List.eraseIdx_sublist ss k).length_le h5
  · apply nextConfiguration.adjV_of_agree _ _ (sk.ID' : List w8) _ h4
    intro y hy
    rw [nextConfiguration.mem_srvVoters, nextConfiguration.mem_srvVoters]
    constructor
    · rintro ⟨s, hs, hv, he⟩
      exact ⟨s, List.mem_of_mem_eraseIdx hs, hv, he⟩
    · rintro ⟨s, hs, hv, he⟩
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hs
      have hik : i ≠ k := by
        rintro rfl
        rw [hk] at hi; cases hi; exact hy he.symm
      exact ⟨s, List.mem_eraseIdx_iff_getElem?.mpr ⟨i, hik, hi⟩, hv, he⟩

theorem nextConfiguration.okRes_append (S : List SID) (ss : List Server) (s' : Server)
    (h : srvsOkIn S ss) (hnin : (s'.ID' : List w8) ∉ srvIds ss) (hS : (s'.ID' : List w8) ∈ S)
    (hsuf : s'.Suffrage' = W64 0 ∨ s'.Suffrage' = W64 1) (hadr : s'.Address' = s'.ID')
    (hne : s'.ID' ≠ []) (hlt : s'.ID'.length < 2 ^ 63) (hlen : ss.length + 1 < 2 ^ 32) :
    nextConfiguration.okRes S ss (ss ++ [s']) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hids : srvIds (ss ++ [s']) = srvIds ss ++ [(s'.ID' : List w8)] := by
    simp [srvIds]
  refine ⟨?_, ?_, ?_, by simpa using hlen, ?_⟩
  · rw [hids, List.nodup_append]
    refine ⟨h1, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
    intro a ha b hb e
    simp only [List.mem_singleton] at hb
    subst hb; subst e; exact hnin ha
  · rw [hids]; intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact h2 j hj
    · simp only [List.mem_singleton] at hj; subst hj; exact hS
  · intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact h3 s hs
    · simp only [List.mem_singleton] at hs; subst hs; exact ⟨hsuf, hadr, hne, hlt⟩
  · apply nextConfiguration.adjV_of_agree _ _ (s'.ID' : List w8) _ h4
    intro y hy
    rw [nextConfiguration.mem_srvVoters, nextConfiguration.mem_srvVoters]
    constructor
    · rintro ⟨s, hs, hv, he⟩
      rcases List.mem_append.mp hs with hs | hs
      · exact ⟨s, hs, hv, he⟩
      · simp only [List.mem_singleton] at hs; subst hs; exact absurd he.symm hy
    · rintro ⟨s, hs, hv, he⟩
      exact ⟨s, List.mem_append_left _ hs, hv, he⟩

/-- (helper) A duplicate-free list within `S` is no longer than `S`. -/
theorem nextConfiguration.nodup_length_le {α : Type} [DecidableEq α] (l S : List α) (hnd : l.Nodup) (hsub : ∀ a ∈ l, a ∈ S) :
    l.length ≤ S.length := by
  induction l generalizing S with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    have ha : a ∈ S := hsub a List.mem_cons_self
    have := ih (S.erase a) hnd.2 (fun y hy => by
      have hne : y ≠ a := fun e => hnd.1 (e ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hsub y (List.mem_cons_of_mem _ hy)))
    rw [List.length_erase_of_mem ha] at this
    have : 0 < S.length := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

/-- (helper) `(*Configuration).Clone` (its code, as `Configuration.Clone.wp_proof`), also giving the
copy's capacity (the frozen `Configuration.Clone.spec` drops it; `nextConfiguration` appends to the
copy). -/
theorem nextConfiguration.wp_Clone_cap (p : Loc) (c : Configuration) (ss : List Server) (dq dq' : DFrac) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ p ↦{dq'} c ∗ c.Servers' ↦*{dq} ss }}
    (App (Val (p @!! go.GoType.PointerType Configuration.ty @!! go!"Clone")) (Val #()))
  {{ (c' : Configuration), RET #c'; p ↦{dq'} c ∗ c.Servers' ↦*{dq} ss ∗ c'.Servers' ↦* ss ∗
      ownSliceCap Server c'.Servers' (DFrac.own 1) }} := by
  wp_start as ⟨Hp, Hs⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hpn⟩
  iStructNamed Hp
  wp_auto
  wp_apply (wp_slice_append slice.nil ([] : List Server) c.Servers' ss dq) $$ [Hs] as %s' ⟨Hs', Hcap, Hs⟩
  · iframe Hs
    isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  iapply HΦ
  iframe Hs Hcap
  isplitl [Servers]
  · iapply typedPointsto_combine _ _ _ Hpn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · simp only [List.nil_append]; iexact Hs'

theorem github_com.hashicorp.raft.nextConfiguration.wp_proof
    (wp_checkConfiguration : github_com.hashicorp.raft.checkConfiguration.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.nextConfiguration.spec (GF := GF) (hG := hG) := by
  intro γ c ss dq ci rq
  wp_start as ⟨Hs, %Hok, %Hrq⟩
  wp_auto
  -- the `prevIndex` check
  wp_bind (If (Val _) _ (Val #false))
  iapply (wp_wand (Φ := fun v => iprop(∃ bad : Bool, ⌜v = #bad ∧
      (bad = true ↔ (uint.Z (W64 0) < uint.Z rq.prevIndex' ∧ rq.prevIndex' ≠ ci))⌝ ∗
      change_ptr ↦ rq ∗ currentIndex_ptr ↦ ci))) $$ [change currentIndex] [-]
  · wp_if_destruct
    · try wp_auto
      iexists _; iframe; ipureintro
      refine ⟨rfl, ?_⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨fun h => ⟨Hif, h⟩, fun h => h.2⟩
    · try wp_auto
      iexists false; iframe; ipureintro
      refine ⟨rfl, ?_⟩
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro h; exact absurd h Hif
  iintro %v ⟨%bad, ⟨%hv, %hbad⟩, change, currentIndex⟩
  subst hv
  cases bad
  case true =>
    -- `prevIndex` is stale: an `fmt.Errorf` error
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.any)
      [interface.mkOk go.uint64 #rq.prevIndex', interface.mkOk go.uint64 #ci]
    wp_auto
    isplitl []; · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_auto
    wp_apply (fmt.wp_Errorf_nextCfgErr _ _ _) $$ [$Hasl] as %e2 #He2
    iapply HΦ
    iframe
    iright
    isplitl
    · unfold errOk
      iexists _
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %Ψ HΨ
      iapply He2
      inext
      iexact HΨ
    · ipureintro; exact ⟨e2, rfl⟩
  wp_auto
  wp_apply (nextConfiguration.wp_Clone_cap current_ptr c ss dq (DFrac.own 1)) $$ [$current $Hs]
    as %c1 ⟨current, Hs, Hc1, Hcap⟩
  try wp_auto
  wp_bind (If (Val _) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (c2 : Configuration) (ss2 : List Server),
      configuration_ptr ↦ c2 ∗ c2.Servers' ↦* ss2 ∗ change_ptr ↦ rq ∗
      ⌜nextConfiguration.okRes γ.srvs ss ss2⌝))) $$ [configuration Hc1 Hcap change] [-]
  · obtain ⟨Hcmd, HS, Hadr, Hidok⟩ := Hrq
    ihave %Hsllen := ownSlice_len $$ Hc1
    wp_if_destruct
    · -- AddVoter
      try wp_auto
      rename_i ikey_ptr
      irename: (ikey_ptr ↦ (zero_val w64)) => ikey
      have hxa : rq.serverAddress' = rq.serverID' := Hadr (Or.inl Hif)
      ihave HI : (∃ (k : Nat) (sv : Server) (kv : w64),
          "i" ∷ i_ptr ↦ W64 k ∗ "server" ∷ server_ptr ↦ sv ∗ "ikey" ∷ ikey_ptr ↦ kv ∗
          "found" ∷ found_ptr ↦ false ∗
          "%Hk" ∷ ⌜k ≤ ss.length ∧ ∀ s ∈ ss.take k, s.ID' ≠ rq.serverID'⌝ : IProp GF)
          $$ [i server ikey found]
      · iexists 0, _, _; iframe; ipureintro; simp
      wp_for HI
      wp_if_destruct
      · obtain ⟨Hk, Hnot⟩ := Hk
        have Hc : sint.Z (W64 (k : Int)) < sint.Z c1.Servers'.len := by
          first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
        have hk : k < ss.length := by word
        list_elem ss k as sk
        rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
        wp_apply (wp_load_slice_index c1.Servers' (sint.Z (W64 k)) ss (DFrac.own 1) sk (by word))
          $$ [$Hc1] with Hc1
        · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact Hsk_lookup
        wp_if_destruct
        · -- found
          have hid : sk.ID' = rq.serverID' := Hif
          have hkz : (sint.Z (W64 (k : Int))).toNat = k := by word
          wp_if_destruct
          · rw [if_pos (by constructor <;> word)]
            icases ownSlice_elem_acc (sint.Z (W64 k)) sk c1.Servers' (DFrac.own 1) ss (by word)
              (by rw [hkz]; exact Hsk_lookup) $$ Hc1 with ⟨Hel, Hcl⟩
            try wp_auto
            ihave Hc1 := Hcl $$ Hel
            rw [hkz]
            wp_for_post
            try wp_auto
            isplitr
            · ipureintro; rfl
            iexists c1, _
            iframe
            ipureintro
            exact nextConfiguration.okRes_set _ ss k sk _ Hok Hsk_lookup rfl (Or.inl Hif)
              (by simp only; rw [hxa, hid])
          · rw [if_pos (by constructor <;> word)]
            wp_apply (wp_store_slice_index (V := Server) (t := Server.ty) c1.Servers' (sint.Z (W64 k)) ss
              (Server.mk (W64 0) rq.serverID' rq.serverAddress')) $$ [$Hc1] as Hc1
            · ipureintro; constructor <;> word
            rw [hkz]
            try wp_auto
            wp_for_post
            try wp_auto
            isplitr
            · ipureintro; rfl
            iexists c1, _
            iframe
            ipureintro
            exact nextConfiguration.okRes_set _ ss k sk _ Hok Hsk_lookup hid.symm (Or.inl rfl) hxa
        · wp_for_post
          iframe
          iexists k + 1, sk, W64 k
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe
          ipureintro
          refine ⟨by omega, fun s hs => ?_⟩
          rw [List.take_add_one, Hsk_lookup] at hs
          simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hs
          rcases hs with hs | rfl
          · exact Hnot s hs
          · exact Hif
      · obtain ⟨Hk, Hnot⟩ := Hk
        have Hc : ¬ sint.Z (W64 (k : Int)) < sint.Z c1.Servers'.len := by
          first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
        have hk : k = ss.length := by word
        subst hk
        rw [List.take_length] at Hnot
        try wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType Server.ty))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := Server) (t := Server.ty)
          [Server.mk (W64 0) rq.serverID' rq.serverAddress']
        try wp_auto
        isplitl []; · ipureintro; rfl
        iintro %nsl ⟨Hnsl, -⟩
        try wp_auto
        wp_apply (wp_slice_append (V := Server) c1.Servers' ss _ _ (DFrac.own 1))
          $$ [$Hc1 $Hcap $Hnsl] as %s' ⟨Hs', -, -⟩
        try wp_auto
        isplitr
        · ipureintro; rfl
        iexists _, _
        iframe
        ipureintro
        have hnin : (rq.serverID' : List w8) ∉ srvIds ss := by
          unfold srvIds; simp only [List.mem_map, not_exists, not_and]
          exact fun s hs he => Hnot s hs he
        obtain ⟨hne, hlt, hS32⟩ : (rq.serverID' : List w8) ≠ [] ∧ rq.serverID'.length < 2 ^ 63 ∧
            γ.srvs.length < 2 ^ 32 := by
          exact Hidok
        have hlen : ss.length + 1 < 2 ^ 32 := by
          have := nextConfiguration.nodup_length_le ((rq.serverID' : List w8) :: srvIds ss) γ.srvs
            (List.nodup_cons.mpr ⟨hnin, Hok.1⟩) (by
              intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · exact HS
              · exact Hok.2.1 a ha)
          simp only [List.length_cons, srvIds, List.length_map] at this
          omega
        exact nextConfiguration.okRes_append _ ss _ Hok hnin HS (Or.inl rfl) hxa hne hlt hlen
    try wp_auto
    wp_if_destruct
    · -- AddNonvoter
      try wp_auto
      rename_i ikey_ptr
      irename: (ikey_ptr ↦ (zero_val w64)) => ikey
      have hxa : rq.serverAddress' = rq.serverID' := Hadr (Or.inr Hif)
      ihave HI : (∃ (k : Nat) (sv : Server) (kv : w64),
          "i" ∷ i_ptr ↦ W64 k ∗ "server" ∷ server_ptr ↦ sv ∗ "ikey" ∷ ikey_ptr ↦ kv ∗
          "found" ∷ found_ptr ↦ false ∗
          "%Hk" ∷ ⌜k ≤ ss.length ∧ ∀ s ∈ ss.take k, s.ID' ≠ rq.serverID'⌝ : IProp GF)
          $$ [i server ikey found]
      · iexists 0, _, _; iframe; ipureintro; simp
      wp_for HI
      wp_if_destruct
      · obtain ⟨Hk, Hnot⟩ := Hk
        have Hc : sint.Z (W64 (k : Int)) < sint.Z c1.Servers'.len := by
          first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
        have hk : k < ss.length := by word
        list_elem ss k as sk
        rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
        wp_apply (wp_load_slice_index c1.Servers' (sint.Z (W64 k)) ss (DFrac.own 1) sk (by word))
          $$ [$Hc1] with Hc1
        · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact Hsk_lookup
        wp_if_destruct
        · -- found
          have hid : sk.ID' = rq.serverID' := Hif
          have hkz : (sint.Z (W64 (k : Int))).toNat = k := by word
          wp_if_destruct
          · rw [if_pos (by constructor <;> word)]
            icases ownSlice_elem_acc (sint.Z (W64 k)) sk c1.Servers' (DFrac.own 1) ss (by word)
              (by rw [hkz]; exact Hsk_lookup) $$ Hc1 with ⟨Hel, Hcl⟩
            try wp_auto
            ihave Hc1 := Hcl $$ Hel
            rw [hkz]
            wp_for_post
            try wp_auto
            isplitr
            · ipureintro; rfl
            iexists c1, _
            iframe
            ipureintro
            exact nextConfiguration.okRes_set _ ss k sk _ Hok Hsk_lookup hid.symm (Or.inr rfl) hxa
          · rw [if_pos (by constructor <;> word)]
            icases ownSlice_elem_acc (sint.Z (W64 k)) sk c1.Servers' (DFrac.own 1) ss (by word)
              (by rw [hkz]; exact Hsk_lookup) $$ Hc1 with ⟨Hel, Hcl⟩
            try wp_auto
            ihave Hc1 := Hcl $$ Hel
            rw [hkz]
            wp_for_post
            try wp_auto
            isplitr
            · ipureintro; rfl
            iexists c1, _
            iframe
            ipureintro
            exact nextConfiguration.okRes_set _ ss k sk _ Hok Hsk_lookup rfl
              ((Hok.2.2.1 sk (List.mem_of_getElem? Hsk_lookup)).1) (by simp only; rw [hxa, hid])
        · wp_for_post
          iframe
          iexists k + 1, sk, W64 k
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe
          ipureintro
          refine ⟨by omega, fun s hs => ?_⟩
          rw [List.take_add_one, Hsk_lookup] at hs
          simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hs
          rcases hs with hs | rfl
          · exact Hnot s hs
          · exact Hif
      · obtain ⟨Hk, Hnot⟩ := Hk
        have Hc : ¬ sint.Z (W64 (k : Int)) < sint.Z c1.Servers'.len := by
          first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
        have hk : k = ss.length := by word
        subst hk
        rw [List.take_length] at Hnot
        try wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType Server.ty))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := Server) (t := Server.ty)
          [Server.mk (W64 1) rq.serverID' rq.serverAddress']
        try wp_auto
        isplitl []; · ipureintro; rfl
        iintro %nsl ⟨Hnsl, -⟩
        try wp_auto
        wp_apply (wp_slice_append (V := Server) c1.Servers' ss _ _ (DFrac.own 1))
          $$ [$Hc1 $Hcap $Hnsl] as %s' ⟨Hs', -, -⟩
        try wp_auto
        isplitr
        · ipureintro; rfl
        iexists _, _
        iframe
        ipureintro
        have hnin : (rq.serverID' : List w8) ∉ srvIds ss := by
          unfold srvIds; simp only [List.mem_map, not_exists, not_and]
          exact fun s hs he => Hnot s hs he
        obtain ⟨hne, hlt, hS32⟩ : (rq.serverID' : List w8) ≠ [] ∧ rq.serverID'.length < 2 ^ 63 ∧
            γ.srvs.length < 2 ^ 32 := by
          exact Hidok
        have hlen : ss.length + 1 < 2 ^ 32 := by
          have := nextConfiguration.nodup_length_le ((rq.serverID' : List w8) :: srvIds ss) γ.srvs
            (List.nodup_cons.mpr ⟨hnin, Hok.1⟩) (by
              intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · exact HS
              · exact Hok.2.1 a ha)
          simp only [List.length_cons, srvIds, List.length_map] at this
          omega
        exact nextConfiguration.okRes_append _ ss _ Hok hnin HS (Or.inr rfl) hxa hne hlt hlen
    try wp_auto
    wp_if_destruct
    · -- DemoteVoter
      try wp_auto
      rename_i ikey_ptr
      irename: (ikey_ptr ↦ (zero_val w64)) => ikey
      ihave HI : (∃ (k : Nat) (sv : Server) (kv : w64),
          "i" ∷ i_ptr ↦ W64 k ∗ "server" ∷ server_ptr ↦ sv ∗ "ikey" ∷ ikey_ptr ↦ kv ∗
          "%Hk" ∷ ⌜k ≤ ss.length⌝ : IProp GF)
          $$ [i server ikey]
      · iexists 0, _, _; iframe; ipureintro; simp
      wp_for HI
      wp_if_destruct
      · have Hc : sint.Z (W64 (k : Int)) < sint.Z c1.Servers'.len := by
          first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
        have hk : k < ss.length := by word
        list_elem ss k as sk
        rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
        wp_apply (wp_load_slice_index c1.Servers' (sint.Z (W64 k)) ss (DFrac.own 1) sk (by word))
          $$ [$Hc1] with Hc1
        · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact Hsk_lookup
        have hkz : (sint.Z (W64 (k : Int))).toNat = k := by word
        wp_if_destruct
        · -- found
          rw [if_pos (by constructor <;> word)]
          icases ownSlice_elem_acc (sint.Z (W64 k)) sk c1.Servers' (DFrac.own 1) ss (by word)
            (by rw [hkz]; exact Hsk_lookup) $$ Hc1 with ⟨Hel, Hcl⟩
          simp only [Nonvoter]
          try wp_auto
          ihave Hc1 := Hcl $$ Hel
          rw [hkz]
          wp_for_post
          try wp_auto
          isplitr
          · ipureintro; rfl
          iexists c1, _
          iframe
          ipureintro
          exact nextConfiguration.okRes_set _ ss k sk _ Hok Hsk_lookup rfl (Or.inr rfl)
            (Hok.2.2.1 sk (List.mem_of_getElem? Hsk_lookup)).2.1
        · wp_for_post
          iframe
          iexists k + 1, sk, W64 k
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe
          ipureintro
          omega
      · have Hc : ¬ sint.Z (W64 (k : Int)) < sint.Z c1.Servers'.len := by
          first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
        have hk : k = ss.length := by word
        try wp_auto
        try (rw [if_pos (by rw [decide_eq_false (by word)])])
        isplitr
        · ipureintro; trivial
        iexists c1, ss
        iframe
        ipureintro
        exact nextConfiguration.okRes_same _ ss Hok
    try wp_auto
    wp_if_destruct
    · -- RemoveServer
      try wp_auto
      rename_i ikey_ptr
      irename: (ikey_ptr ↦ (zero_val w64)) => ikey
      ihave HI : (∃ (k : Nat) (sv : Server) (kv : w64),
          "i" ∷ i_ptr ↦ W64 k ∗ "server" ∷ server_ptr ↦ sv ∗ "ikey" ∷ ikey_ptr ↦ kv ∗
          "%Hk" ∷ ⌜k ≤ ss.length⌝ : IProp GF)
          $$ [i server ikey]
      · iexists 0, _, _; iframe; ipureintro; simp
      wp_for HI
      wp_if_destruct
      · have Hc : sint.Z (W64 (k : Int)) < sint.Z c1.Servers'.len := by
          first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
        have hk : k < ss.length := by word
        list_elem ss k as sk
        rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
        wp_apply (wp_load_slice_index c1.Servers' (sint.Z (W64 k)) ss (DFrac.own 1) sk (by word))
          $$ [$Hc1] with Hc1
        · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact Hsk_lookup
        have hkz : (sint.Z (W64 (k : Int))).toNat = k := by word
        wp_if_destruct
        · -- found
          ihave %Hwf := ownSlice_wf _ _ _ $$ Hc1
          rw [if_pos (by constructor <;> word)]
          try wp_auto
          rw [if_pos (by constructor <;> word)]
          wp_apply (wp_slice_delete (V := Server) (st := Server.ty.SliceType) (t := Server.ty)
            c1.Servers' ss (W64 k) ⟨by word, by word⟩) $$ [$Hc1 $Hcap] as %s' ⟨Hs', -⟩
          try wp_auto
          wp_for_post
          try wp_auto
          isplitr
          · ipureintro; rfl
          iexists _, _
          iframe
          ipureintro
          rw [show sint.nat (W64 (k : Int)) = k by word]
          exact nextConfiguration.okRes_erase _ ss k sk Hok Hsk_lookup
        · wp_for_post
          iframe
          iexists k + 1, sk, W64 k
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe
          ipureintro
          omega
      · have Hc : ¬ sint.Z (W64 (k : Int)) < sint.Z c1.Servers'.len := by
          first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
        have hk : k = ss.length := by word
        try wp_auto
        try (rw [if_pos (by rw [decide_eq_false (by word)])])
        isplitr
        · ipureintro; trivial
        iexists c1, ss
        iframe
        ipureintro
        exact nextConfiguration.okRes_same _ ss Hok
    exfalso
    rename_i h0 h1 h2
    rcases Hcmd with h | h | h | h
    · exact h0 h
    · exact h1 h
    · exact h2 h
    · exact Hif h
  iintro %v ⟨%hv, %c2, %ss2, configuration, Hc2, change, %Hres⟩
  subst hv
  try wp_auto
  obtain ⟨Hnd2, Hin2, Hsv2, Hlen2, Hadj⟩ := Hres
  wp_apply (wp_checkConfiguration c2 ss2 (DFrac.own 1)) $$ [$Hc2] as %err ⟨Hc2, Herr⟩
  · ipureintro
    exact ⟨fun s hs => ⟨(Hsv2 s hs).2.1, (Hsv2 s hs).2.2.1⟩, Hnd2⟩
  icases Herr with (⟨%he, %hv⟩ | ⟨%hv, #Herr, %Hleaf⟩)
  · subst he
    try wp_auto
    iapply HΦ
    iframe Hs
    ileft
    isplitr
    · ipureintro; rfl
    iexists ss2
    iframe Hc2
    ipureintro
    exact ⟨⟨Hnd2, Hin2, Hsv2, hv, Hlen2⟩, Hadj⟩
  · try wp_auto
    ihave #Herr' := Herr
    unfold errOk
    icases Herr' with ⟨%x, %hx, -⟩
    subst hx
    try wp_auto
    iapply HΦ
    iframe Hs
    iright
    isplitl
    · iexact Herr
    · ipureintro; exact Hleaf

end proof

end Perennial
