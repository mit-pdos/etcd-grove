/-
The definitions, specs and lemmas of `DepEqualsPerm.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckCalleesDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

end proofs

section ghost
variable [go_gctx : GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [SwiftNetPkgState netDistGF]
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
