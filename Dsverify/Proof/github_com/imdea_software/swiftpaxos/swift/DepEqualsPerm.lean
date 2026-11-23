/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DepEqualsPerm.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**Round 54 (D74 (3), 53-2):** `(&dep1).Equals(dep2)` returning `true` gives a permutation, when
`dep2` has no duplicates (defs.go:194-222). The loop's maps `seen1`/`seen2` are, for the prefixes
`p1`/`p2` read so far, `p1 \ p2` and `p2 \ p1` (`swift.depEq_eqInv`); at the end both are empty.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckCallees
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSeq
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure -/

/-- The loop's invariant after `n` steps: `seen2` is `p2 \ p1`, `seen1` is `p1 \ p2` (one
inclusion each way). -/
def swift.depEq_eqInv (l1 l2 : List swift.CommandId) (n : Nat) (s1 s2 : GMap swift.CommandId Unit) : Prop :=
  (∀ z, (s2 !! z).isSome ↔ (z ∈ l2.take n ∧ z ∉ l1.take n)) ∧
  (∀ z, (s1 !! z).isSome → z ∈ l1.take n) ∧
  (∀ z, z ∈ l1.take n → z ∉ l2.take n → (s1 !! z).isSome)

theorem swift.depEq_eqInv_nil (l1 l2 : List swift.CommandId) : swift.depEq_eqInv l1 l2 0 ∅ ∅ := by
  refine ⟨fun z => ?_, fun z h => ?_, fun z h _ => ?_⟩ <;> simp_all

theorem swift.depEq_take_not_mem {l : List swift.CommandId} {n : Nat} {x : swift.CommandId}
    (h : l.Nodup) (hx : l[n]? = some x) : x ∉ l.take n := by
  intro hm
  have hl := List.take_append_drop n l
  have hd : l.drop n = x :: l.drop (n + 1) := by
    rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hx).1]
    rw [(List.getElem?_eq_some_iff.mp hx).2]
  rw [← hl, hd, List.nodup_append] at h
  exact h.2.2 x hm x (by simp) rfl

theorem swift.depEq_take_succ_of {l : List swift.CommandId} {n : Nat} {x : swift.CommandId}
    (hx : l[n]? = some x) : l.take (n + 1) = l.take n ++ [x] := by
  rw [List.take_add_one, hx]; rfl

theorem swift.depEq_eqInv_same {l1 l2 : List swift.CommandId} {n : Nat} {s1 s2 : GMap swift.CommandId Unit}
    {x : swift.CommandId} (hnd : l2.Nodup) (h1 : l1[n]? = some x) (h2 : l2[n]? = some x)
    (h : swift.depEq_eqInv l1 l2 n s1 s2) : swift.depEq_eqInv l1 l2 (n + 1) s1 s2 := by
  have hx2 := swift.depEq_take_not_mem hnd h2
  obtain ⟨hb, hc, hd⟩ := h
  rw [swift.depEq_eqInv, swift.depEq_take_succ_of h1, swift.depEq_take_succ_of h2]
  refine ⟨fun z => ?_, fun z hz => ?_, fun z hz hz2 => ?_⟩
  · rw [hb z]; simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨hp, hn⟩; exact ⟨Or.inl hp, fun hh => hn (hh.resolve_right (fun e => hx2 (e ▸ hp)))⟩
    · rintro ⟨hp, hn⟩
      exact ⟨hp.resolve_right (fun e => hn (Or.inr e)), fun hh => hn (Or.inl hh)⟩
  · exact List.mem_append_left _ (hc z hz)
  · simp only [List.mem_append, List.mem_singleton, not_or] at hz hz2
    exact hd z (hz.resolve_right hz2.2) hz2.1

theorem swift.depEq_eqInv_diff {l1 l2 : List swift.CommandId} {n : Nat} {s1 s2 : GMap swift.CommandId Unit}
    {x y : swift.CommandId} (hnd : l2.Nodup) (h1 : l1[n]? = some x) (h2 : l2[n]? = some y)
    (hxy : x ≠ y) (h : swift.depEq_eqInv l1 l2 n s1 s2) (s1' s2' : GMap swift.CommandId Unit)
    (e1 : s1' = if (s2 !! x).isSome then s1 else <[x := ()]> s1)
    (e2 : s2' = if (s2 !! x).isSome then GMap.delete x s2 else s2) :
    swift.depEq_eqInv l1 l2 (n + 1)
      (if (s1' !! y).isSome then GMap.delete y s1' else s1')
      (if (s1' !! y).isSome then s2' else <[y := ()]> s2') := by
  have hy2 := swift.depEq_take_not_mem hnd h2
  obtain ⟨hb, hc, hd⟩ := h
  have hs1' : ∀ z, (s1' !! z).isSome ↔ ((s1 !! z).isSome ∨ (z = x ∧ ¬ (s2 !! x).isSome)) := by
    intro z; rw [e1]
    split <;> rename_i hh
    · simp [hh]
    · by_cases e : z = x
      · subst e; simp [hh]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; simp [e]
  have hs2' : ∀ z, (s2' !! z).isSome ↔ ((s2 !! z).isSome ∧ z ≠ x) := by
    intro z; rw [e2]
    split <;> rename_i hh
    · by_cases e : z = x
      · subst e; simp
      · rw [GMap.lookup_delete_ne _ (Ne.symm e)]; simp [e]
    · by_cases e : z = x
      · subst e; simp [hh]
      · simp [e]
  rw [swift.depEq_eqInv, swift.depEq_take_succ_of h1, swift.depEq_take_succ_of h2]
  simp only [List.mem_append, List.mem_singleton]
  refine ⟨fun z => ?_, fun z hz => ?_, fun z hz hz2 => ?_⟩
  · split <;> rename_i hy
    · rw [hs2', hb]
      by_cases e : z = y
      · subst e
        have : z ∈ l1.take n := by
          rcases (hs1' z).1 hy with h0 | ⟨h0, -⟩
          · exact hc z h0
          · exact absurd h0 (Ne.symm hxy)
        simp [this, hy2]
      · by_cases ex : z = x
        · subst ex; simp
        · simp [e, ex]
    · by_cases e : z = y
      · subst e
        simp only [GMap.lookup_insert, Option.isSome_some, true_iff]
        refine ⟨by simp, ?_⟩
        rintro (hm | hm)
        · exact hy ((hs1' z).2 (Or.inl (hd z hm hy2)))
        · exact hxy hm.symm
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), hs2', hb]
        by_cases ex : z = x
        · subst ex; simp
        · simp [e, ex]
  · split at hz <;> rename_i hy
    · by_cases e : z = y
      · subst e; simp at hz
      · rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hz
        rcases (hs1' z).1 hz with h0 | ⟨h0, -⟩
        · exact Or.inl (hc z h0)
        · exact Or.inr h0
    · rcases (hs1' z).1 hz with h0 | ⟨h0, -⟩
      · exact Or.inl (hc z h0)
      · exact Or.inr h0
  · simp only [not_or] at hz2
    have hzy : z ≠ y := hz2.2
    have key : (s1' !! z).isSome := by
      rcases hz with hz | hz
      · exact (hs1' z).2 (Or.inl (hd z hz hz2.1))
      · subst hz
        by_cases hh : (s2 !! z).isSome
        · exact absurd ((hb z).1 hh).1 hz2.1
        · exact (hs1' z).2 (Or.inr ⟨rfl, hh⟩)
    split
    · rw [GMap.lookup_delete_ne _ (Ne.symm hzy)]; exact key
    · exact key

theorem swift.depEq_eqInv_perm {l1 l2 : List swift.CommandId} {s1 s2 : GMap swift.CommandId Unit}
    (hnd : l2.Nodup) (hlen : l1.length = l2.length) (h : swift.depEq_eqInv l1 l2 l1.length s1 s2)
    (h0 : s2 = ∅) : l1.Perm l2 := by
  have hsub : l2 ⊆ l1 := by
    intro z hz
    refine Classical.byContradiction fun hn => ?_
    have := (h.1 z).2 ⟨by rw [hlen, List.take_length]; exact hz, by rw [List.take_length]; exact hn⟩
    rw [h0] at this; simp at this
  exact ((List.subperm_of_subset hnd hsub).perm_of_length_le (by omega)).symm


section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- `(&dep1).Equals(dep2)` with `dep2` without duplicates: `true` only for a permutation. -/
abbrev swift.Dep.Equals.specPerm : Prop :=
  ∀ (dp : Loc) (d1 d2 : GoSlice) (dq dq1 dq2 : DFrac) (l1 l2 : List swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      typedPointsto dp d1 dq ∗ d1 ↦*{dq1} l1 ∗ d2 ↦*{dq2} l2 ∗ ⌜l2.Nodup⌝ }}
    (App (Val (dp @!! go.GoType.PointerType swift.Dep.ty @!! go!"Equals")) (Val #d2))
  {{ (bb : Bool), RET #bb; typedPointsto dp d1 dq ∗ d1 ↦*{dq1} l1 ∗ d2 ↦*{dq2} l2 ∗
      ⌜bb = true → l1.Perm l2⌝ }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

theorem swift.Dep.Equals.wp_proofPerm : swift.Dep.Equals.specPerm (hG := hG) := by
  intro dp d1 d2 dq dq1 dq2 l1 l2
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨Hdp, Hd1, Hd2, %Hnd⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave %Hl1 := ownSlice_len $$ Hd1
  ihave %Hl2 := ownSlice_len $$ Hd2
  wp_if_destruct
  · have hlen : l1.length = l2.length := by rw [Hl1.1, Hl2.1, Hif]
    have hdl := Hif
    wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %m1 Hm1
    wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %m2 Hm2
    ihave HI : (∃ (i : w64) (s1 s2 : GMap swift.CommandId Unit), "i" ∷ i_ptr ↦ i ∗
        "Hm1" ∷ m1 ↦$ s1 ∗ "Hm2" ∷ m2 ↦$ s2 ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z d1.len⌝ ∗
        "%Hinv" ∷ ⌜swift.depEq_eqInv l1 l2 (sint.nat i) s1 s2⌝ :
        IProp netDistGF) $$ [i Hm1 Hm2]
    · iexists W64 0, ∅, ∅; iframe
      isplitr
      · ipureintro; refine ⟨by word, by word⟩
      ipureintro; exact swift.depEq_eqInv_nil l1 l2
    wp_for HI
    wp_if_destruct
    · have hsucc : sint.nat (i + W64 1) = sint.nat i + 1 := by have := Hi.1; word
      have hil1 : sint.nat i < l1.length := by have := Hi.1; word
      have hil2 : sint.nat i < l2.length := by have := Hi.1; word
      obtain ⟨x, hx⟩ : ∃ x, l1[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hil1⟩
      obtain ⟨y, hy⟩ : ∃ y, l2[sint.nat i]? = some y := ⟨_, List.getElem?_eq_getElem hil2⟩
      have hb1 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z d1.len := ⟨Hi.1, Hif⟩
      have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z d2.len := ⟨Hi.1, by rw [← hdl]; exact Hif⟩
      have hix : l1[(sint.Z i).toNat]? = some x := by rw [show (sint.Z i).toNat = sint.nat i by word, hx]
      have hiy : l2[(sint.Z i).toNat]? = some y := by rw [show (sint.Z i).toNat = sint.nat i by word, hy]
      rw [ite_eq_left hb1]
      wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
      · iframe; ipureintro; exact hix
      wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (x = y))⌝ ∗ d2 ↦*{dq2} l2))) $$ [Hd2]
      · rw [ite_eq_left hb2]
        wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
        · iframe; ipureintro; exact hiy
        wp_if_destruct
        · iframe; ipureintro; congr 2; cases x; cases y; simp_all
        · iframe; ipureintro; congr 2; cases x; cases y; simp_all
      iintro %v ⟨%hv, Hd2⟩
      subst hv
      wp_if_destruct
      · -- the same id at `i`
        wp_for_post
        iframe
        iexists i + W64 1, s1, s2
        iframe
        isplitr
        · ipureintro; refine ⟨by word, by word⟩
        ipureintro
        rw [hsucc]
        have hxy : x = y := by simpa using Hif
        subst hxy
        exact swift.depEq_eqInv_same Hnd hx hy Hinv
      · rw [ite_eq_left hb1]
        wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
        · iframe; ipureintro; exact hix
        wp_apply (wp_map_lookup2 _ _ m2 s2 x) $$ Hm2 as Hm2
        have hxy : x ≠ y := Hif
        let s1' := if (s2 !! x).isSome then s1 else <[x := ()]> s1
        let s2' := if (s2 !! x).isSome then GMap.delete x s2 else s2
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun v => iprop(m1 ↦$ s1' ∗ m2 ↦$ s2' ∗ d1 ↦*{dq1} l1 ∗
            seen1_ptr ↦ m1 ∗ seen2_ptr ↦ m2 ∗ dep1_ptr ↦ d1 ∗ i_ptr ↦ i ∗ ⌜v = executeVal⌝)))
          $$ [Hm1 Hm2 Hd1 seen1 seen2 dep1 i]
        · wp_if_destruct
          · rw [ite_eq_left hb1]
            wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
            · iframe; ipureintro; exact hix
            wp_apply (wp_mapDelete m2 s2 x) $$ Hm2 as Hm2
            simp only [s1', s2', Hif, ↓reduceIte]
            iframe
          · rw [ite_eq_left hb1]
            wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
            · iframe; ipureintro; exact hix
            wp_apply (wp_mapInsert _ m1 s1 x (zero_val Unit)) $$ Hm1 as Hm1
            have hc : (s2 !! x).isSome = false := by simpa using Hif
            simp only [s1', s2', hc, Bool.false_eq_true, ↓reduceIte]
            iframe
        iintro %v ⟨Hm1, Hm2, Hd1, seen1, seen2, dep1, i, %hv⟩
        subst hv
        wp_auto
        rw [ite_eq_left hb2]
        wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
        · iframe; ipureintro; exact hiy
        wp_apply (wp_map_lookup2 _ _ m1 s1' y) $$ Hm1 as Hm1
        wp_if_destruct
        · rw [ite_eq_left hb2]
          wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
          · iframe; ipureintro; exact hiy
          wp_apply (wp_mapDelete m1 s1' y) $$ Hm1 as Hm1
          wp_for_post
          iframe
          iexists i + W64 1, _, _
          iframe
          isplitr
          · ipureintro; refine ⟨by word, by word⟩
          ipureintro
          rw [hsucc]
          have hd := swift.depEq_eqInv_diff Hnd hx hy hxy Hinv s1' s2' rfl rfl
          have hc : (s1' !! y).isSome = true := by simpa using Hif
          rw [if_pos hc, if_pos hc] at hd
          exact hd
        · rw [ite_eq_left hb2]
          wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
          · iframe; ipureintro; exact hiy
          wp_apply (wp_mapInsert _ m2 s2' y (zero_val Unit)) $$ Hm2 as Hm2
          wp_for_post
          iframe
          iexists i + W64 1, _, _
          iframe
          isplitr
          · ipureintro; refine ⟨by word, by word⟩
          ipureintro
          rw [hsucc]
          have hd := swift.depEq_eqInv_diff Hnd hx hy hxy Hinv s1' s2' rfl rfl
          have hc : (s1' !! y).isSome = false := by simpa using Hif
          rw [if_neg (by simp [hc]), if_neg (by simp [hc])] at hd
          exact hd
    · wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m1 s1) $$ [$Hm1] as ⟨Hm1, %hs1⟩
      wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m2 s2) $$ [$Hm2] as ⟨Hm2, %hs2⟩
      have hiend : sint.nat i = l1.length := by have := Hi.2; word
      rw [hiend] at Hinv
      wp_if_destruct
      · wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m1 s1) $$ [$Hm1] as ⟨Hm1, -⟩
        iapply HΦ; iframe
        ipureintro
        intro hb
        have h1 : GMap.size s1 = 0 := by
          have := Hif; revert hb; simp only [decide_eq_true_eq]; intro hb; word
        have h2 : GMap.size s2 = 0 := by word
        exact swift.depEq_eqInv_perm Hnd hlen Hinv (GMap.map_size_empty_inv s2 h2)
      · iapply HΦ; iframe; ipureintro; intro hb; cases hb
  · iapply HΦ; iframe; ipureintro; intro hb; cases hb

end proofs

section ghost
variable [go_gctx : GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF]
variable {γ : sp.Names} {γc γm γl : GName}

/-- **The dependencies of a `locDeps` have no duplicates** (round 54, 53-2: `Dep.Equals`' second
list at a follower, the leader's ack's): `D ~ depsIn s x` over a `locLb` `s`, whose ids are a
prefix of the replica's sequence (`PInv.loc_ok`: no duplicates). -/
theorem sp.locDeps_nodup (E : CoPset) (hE : ↑sp.spN ⊆ E) (r b : Nat) (x : sp.CmdId)
    (D : List sp.CmdId) :
    sp.inv γ γc γm γl ∗ sp.locDeps γ r b x D ⊢ |={E}=> ⌜D.Nodup⌝ := by
  unfold sp.inv
  iintro ⟨#Hinv, #Hd⟩
  iunfold sp.locDeps at Hd
  icases Hd with ⟨%s, #Hlb, %Hs⟩
  iinv Hinv with Hi Hclose
  unfold sp.invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, >HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, HCl, HDom, Hslots, Hconns⟩
  ihave %Hlk := sp.locLb_lookups (γ := γ) r b s mL mC $$ [HL HC Hlb]
  · iframe HL HC Hlb
  have hpre : s.map Prod.fst <+: S.loc r b :=
    sp.prefix_of_lookups (fun i p hp => by rw [← Hrepr.loc]; exact (Hlk i p hp).1)
  have hfin : (s.map Prod.fst).Nodup → D.Nodup := fun hnd =>
    Hs.2.nodup_iff.mpr (sp.depsIn_nodup' s x hnd)
  icases Hproto with (>%Hemp | ⟨%N, %fr, %l, #Hcfg, >%HP⟩)
  · have hnd : (s.map Prod.fst).Nodup := by
      rw [Hemp.1.1 r b] at hpre
      rw [List.prefix_nil.mp hpre]; exact List.nodup_nil
    imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs HCl HDom Hslots Hconns] with -
    · inext
      iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
      iframe
      isplitr
      · ipureintro; exact Hrepr
      ileft; ipureintro; exact Hemp
    imodintro
    ipureintro; exact hfin hnd
  · have hnd : (s.map Prod.fst).Nodup := (HP.1.loc_ok r b).1.sublist hpre.sublist
    imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs HCl HDom Hslots Hconns Hcfg] with -
    · inext
      iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
      iframe
      isplitr
      · ipureintro; exact Hrepr
      iright
      iexists N, fr, l
      isplitr
      · iexact Hcfg
      ipureintro; exact HP
    imodintro
    ipureintro; exact hfin hnd

end ghost

end Perennial.github_com.imdea_software.swiftpaxos

end
