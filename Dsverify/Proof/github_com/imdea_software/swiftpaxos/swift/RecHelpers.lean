/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecHelpers.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`recoveredSync`'s small callees (specs in Proof/swift/RecSync.lean): `keysOf`, `inConflict`
(over `state.Conflict`, proved here for non-`SCAN` commands), `Dep.Contains`, `Dep.Equals`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## `Dep.Equals`, pure -/

/-- `Equals`' maps after `i` positions: `seen1` the ids of `l1`'s prefix not in `l2`'s, and
`seen2` the converse. -/
def swift.eqInv (l1 l2 : List swift.CommandId) (i : Nat) (s1 s2 : GMap swift.CommandId Unit) : Prop :=
  ∀ a, ((s1 !! a).isSome ↔ a ∈ l1.take i ∧ a ∉ l2.take i) ∧
    ((s2 !! a).isSome ↔ a ∈ l2.take i ∧ a ∉ l1.take i)

theorem swift.eqInv_zero (l1 l2 : List swift.CommandId) : swift.eqInv l1 l2 0 ∅ ∅ := by
  intro a; simp

theorem swift.nodup_take_not_mem {l : List swift.CommandId} (hnd : l.Nodup) {i : Nat} {x : swift.CommandId}
    (hx : l[i]? = some x) : x ∉ l.take i := by
  have hd : x ∈ l.drop i := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by rw [List.getElem?_drop]; simpa using hx⟩
  have h := hnd
  rw [← List.take_append_drop i l, List.nodup_append] at h
  exact fun hm => h.2.2 x hm x hd rfl

theorem swift.take_succ_of {l : List swift.CommandId} {i : Nat} {x : swift.CommandId}
    (hx : l[i]? = some x) : l.take (i + 1) = l.take i ++ [x] := by
  rw [List.take_add_one, hx]; rfl

theorem swift.eqInv_same {l1 l2 : List swift.CommandId} {i : Nat} {s1 s2 : GMap swift.CommandId Unit}
    (H : swift.eqInv l1 l2 i s1 s2) (h1 : l1.Nodup) (h2 : l2.Nodup) {x : swift.CommandId}
    (hx : l1[i]? = some x) (hy : l2[i]? = some x) : swift.eqInv l1 l2 (i + 1) s1 s2 := by
  have nx1 := swift.nodup_take_not_mem h1 hx
  have nx2 := swift.nodup_take_not_mem h2 hy
  intro a
  rw [swift.take_succ_of hx, swift.take_succ_of hy]
  obtain ⟨H1, H2⟩ := H a
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rw [H1]; by_cases e : a = x
    · subst e; simp [nx1]
    · simp [e]
  · rw [H2]; by_cases e : a = x
    · subst e; simp [nx2]
    · simp [e]

theorem swift.eqInv_diff {l1 l2 : List swift.CommandId} {i : Nat} {s1 s2 : GMap swift.CommandId Unit}
    (H : swift.eqInv l1 l2 i s1 s2) (h1 : l1.Nodup) (h2 : l2.Nodup) {x y : swift.CommandId}
    (hx : l1[i]? = some x) (hy : l2[i]? = some y) (hxy : x ≠ y) :
    let s1' := if (s2 !! x).isSome then s1 else <[x := ()]> s1
    let s2' := if (s2 !! x).isSome then GMap.delete x s2 else s2
    swift.eqInv l1 l2 (i + 1)
      (if (s1' !! y).isSome then GMap.delete y s1' else s1')
      (if (s1' !! y).isSome then s2' else <[y := ()]> s2') := by
  intro s1' s2'
  have nx1 := swift.nodup_take_not_mem h1 hx
  have ny2 := swift.nodup_take_not_mem h2 hy
  have e1 : ∀ a, (s1' !! a).isSome ↔ (a ∈ l1.take i ∨ a = x) ∧ a ∉ l2.take i := by
    intro a
    simp only [s1']
    obtain ⟨H1, -⟩ := H a
    obtain ⟨-, H2x⟩ := H x
    by_cases hc : (s2 !! x).isSome
    · rw [if_pos hc, H1]; rw [H2x] at hc
      by_cases e : a = x
      · subst e; simp [hc.1]
      · simp [e]
    · rw [if_neg hc]; rw [H2x] at hc
      by_cases e : a = x
      · subst e; simp [nx1] at hc ⊢; exact hc
      · simp [GMap.lookup_insert_eq_iff, Ne.symm e, H1, e]
  have e2 : ∀ a, (s2' !! a).isSome ↔ a ∈ l2.take i ∧ ¬(a ∈ l1.take i ∨ a = x) := by
    intro a
    simp only [s2']
    obtain ⟨-, H2⟩ := H a
    obtain ⟨-, H2x⟩ := H x
    by_cases hc : (s2 !! x).isSome
    · rw [if_pos hc]
      by_cases e : a = x
      · subst e; simp
      · simp [GMap.lookup_delete_iff, Ne.symm e, H2, e]
    · rw [if_neg hc, H2]
      by_cases e : a = x
      · subst e; rw [H2x] at hc; simp [nx1] at hc ⊢; exact hc
      · simp [e]
  intro a
  rw [swift.take_succ_of hx, swift.take_succ_of hy]
  simp only [List.mem_append, List.mem_singleton]
  have ey := e1 y
  by_cases hc : (s1' !! y).isSome
  · rw [if_pos hc, if_pos hc]
    rw [ey] at hc
    constructor
    · by_cases e : a = y
      · subst e; simp
      · simp only [GMap.lookup_delete_iff, Ne.symm e, ↓reduceIte, e1, e, _root_.or_false]
    · rw [e2]; by_cases e : a = y
      · subst e; simp [hc.1]
      · simp [e]
  · rw [if_neg hc, if_neg hc]
    rw [ey] at hc
    constructor
    · rw [e1]; by_cases e : a = y
      · subst e; simp [ny2]
        exact ⟨fun h => hc ⟨Or.inl h, ny2⟩, fun h => hc ⟨Or.inr h, ny2⟩⟩
      · simp [e]
    · by_cases e : a = y
      · subst e; simp [GMap.lookup_insert_eq_iff]
        exact ⟨fun h => hc ⟨Or.inl h, ny2⟩, fun h => hxy h.symm⟩
      · simp only [GMap.lookup_insert_eq_iff, Ne.symm e, ↓reduceIte, e2, e, _root_.or_false]

theorem swift.eqInv_end {l1 l2 : List swift.CommandId} {s1 s2 : GMap swift.CommandId Unit}
    (H : swift.eqInv l1 l2 l1.length s1 s2) (hl : l1.length = l2.length) (h1 : l1.Nodup) (h2 : l2.Nodup) :
    (decide (GMap.size s1 = GMap.size s2) && decide (GMap.size s1 = 0)) =
      sp.depEq (l1.map toCmdId) (l2.map toCmdId) := by
  have hdep : sp.depEq (l1.map toCmdId) (l2.map toCmdId) = decide (l1.Perm l2) := by
    unfold sp.depEq
    rw [Bool.eq_iff_iff, List.isPerm_iff, decide_eq_true_iff]
    constructor
    · intro h
      have := h.map ofCmdId
      have hid : (ofCmdId ∘ toCmdId) = id := funext ofCmdId_toCmdId
      rw [List.map_map, List.map_map, hid, List.map_id, List.map_id] at this
      exact this
    · intro h; exact h.map _
  rw [hdep]
  unfold swift.eqInv at H
  rw [List.take_length] at H
  rw [show l1.length = l2.length from hl, List.take_length] at H
  have hz : ∀ s : GMap swift.CommandId Unit, GMap.size s = 0 ↔ ∀ a, (s !! a).isSome = false := by
    intro s
    constructor
    · intro h a
      cases e : s !! a with
      | none => rfl
      | some v => exact absurd h ((GMap.map_size_ne_0_lookup s).2 ⟨a, v, e⟩)
    · intro h
      apply Classical.byContradiction; intro hn
      obtain ⟨k, v, e⟩ := (GMap.map_size_ne_0_lookup s).1 hn
      have := h k; rw [e] at this; cases this
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [List.perm_ext_iff_of_nodup h1 h2]
  constructor
  · rintro ⟨hs, h0⟩
    rw [hs] at h0
    have z1 := (hz s1).1 (by rw [hs]; exact h0)
    have z2 := (hz s2).1 h0
    intro a
    obtain ⟨H1, H2⟩ := H a
    constructor
    · intro ha; apply Classical.byContradiction; intro hn; have := H1.2 ⟨ha, hn⟩; rw [z1 a] at this; cases this
    · intro ha; apply Classical.byContradiction; intro hn; have := H2.2 ⟨ha, hn⟩; rw [z2 a] at this; cases this
  · intro hp
    have z1 : ∀ a, (s1 !! a).isSome = false := by
      intro a; cases e : (s1 !! a).isSome
      · rfl
      · have := ((H a).1.1 e); exact absurd ((hp a).1 this.1) this.2
    have z2 : ∀ a, (s2 !! a).isSome = false := by
      intro a; cases e : (s2 !! a).isSome
      · rfl
      · have := ((H a).2.1 e); exact absurd ((hp a).2 this.1) this.2
    rw [(hz s1).2 z1, (hz s2).2 z2]
    exact ⟨rfl, rfl⟩

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- `state.Conflict(gamma, delta)` for commands that are not `SCAN`s: the model's
`Cmd.conflict`. -/
abbrev state.Conflict.specI : Prop :=
  ∀ (g d : Loc) (c1 c2 : sp.Cmd) (v1 v2 : GoSlice) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.state ∗
      g ↦{dq1} state.Command.mk c1.op c1.key v1 ∗ d ↦{dq2} state.Command.mk c2.op c2.key v2 ∗
      ⌜c1.op ≠ swift.opSCAN ∧ c2.op ≠ swift.opSCAN⌝ }}
    (App (App (Val (@! state.Conflict)) (Val #g)) (Val #d))
  {{ RET #(sp.Cmd.conflict c1 c2);
      g ↦{dq1} state.Command.mk c1.op c1.key v1 ∗ d ↦{dq2} state.Command.mk c2.op c2.key v2 }}

variable [state.Assumptions] [swift.Assumptions]

theorem state.Conflict.wp_proof : state.Conflict.specI (hG := hG) := by
  intro g d c1 c2 v1 v2 dq1 dq2
  wp_start as ⟨Hg, Hd, %Hop⟩
  ihave %Hgn := typedPointsto_not_null $$ Hg
  ihave %Hdn := typedPointsto_not_null $$ Hd
  iStructNamedSuffix Hg "g"
  iStructNamedSuffix Hd "d"
  have h1 : decide (c1.op = W8 3) = false := by simpa [swift.opSCAN] using Hop.1
  have h2 : decide (c2.op = W8 3) = false := by simpa [swift.opSCAN] using Hop.2
  wp_auto
  simp only [h1]
  wp_auto
  simp only [h1]
  wp_auto
  simp only [h2]
  wp_auto
  have hkeq : ∀ a b : w64, sint.Z b ≤ sint.Z a → sint.Z a ≤ sint.Z b → a = b := by
    intro a b h h'; word
  wp_if_destruct
  · have hA := Hif
    wp_if_destruct
    · have hk : c1.key = c2.key := hkeq _ _ hA Hif
      wp_if_destruct
      · have hc : c1.conflict c2 = true := by
          simp [sp.Cmd.conflict, sp.Cmd.isPut, sp.opPUT, hk, Hif]
        rw [hc]; iapply HΦ
        isplitl [Opg Kg Vg _g]
        · iapply typedPointsto_combine _ _ _ Hgn; simp only [TypedPointsto.typedPointstoDef]; iframe
        · iapply typedPointsto_combine _ _ _ Hdn; simp only [TypedPointsto.typedPointstoDef]; iframe
      · have hA' := Hif
        wp_if_destruct
        · have hc : c1.conflict c2 = true := by
            simp [sp.Cmd.conflict, sp.Cmd.isPut, sp.opPUT, hk, Hif]
          rw [hc]; iapply HΦ
          isplitl [Opg Kg Vg _g]
          · iapply typedPointsto_combine _ _ _ Hgn; simp only [TypedPointsto.typedPointstoDef]; iframe
          · iapply typedPointsto_combine _ _ _ Hdn; simp only [TypedPointsto.typedPointstoDef]; iframe
        · have hc : c1.conflict c2 = false := by
            simp only [sp.Cmd.conflict, sp.Cmd.isPut, sp.opPUT, Bool.and_eq_false_iff, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
            exact Or.inr ⟨hA', Hif⟩
          rw [hc]; iapply HΦ
          isplitl [Opg Kg Vg _g]
          · iapply typedPointsto_combine _ _ _ Hgn; simp only [TypedPointsto.typedPointstoDef]; iframe
          · iapply typedPointsto_combine _ _ _ Hdn; simp only [TypedPointsto.typedPointstoDef]; iframe
    · have hc : c1.conflict c2 = false := by
        simp only [sp.Cmd.conflict, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        left; intro h; rw [h] at Hif; exact Hif (Int.le_refl _)
      rw [hc]; iapply HΦ
      isplitl [Opg Kg Vg _g]
      · iapply typedPointsto_combine _ _ _ Hgn; simp only [TypedPointsto.typedPointstoDef]; iframe
      · iapply typedPointsto_combine _ _ _ Hdn; simp only [TypedPointsto.typedPointstoDef]; iframe
  · have hc : c1.conflict c2 = false := by
      simp only [sp.Cmd.conflict, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      left; intro h; rw [h] at Hif; exact Hif (Int.le_refl _)
    rw [hc]; iapply HΦ
    isplitl [Opg Kg Vg _g]
    · iapply typedPointsto_combine _ _ _ Hgn; simp only [TypedPointsto.typedPointstoDef]; iframe
    · iapply typedPointsto_combine _ _ _ Hdn; simp only [TypedPointsto.typedPointstoDef]; iframe

theorem swift.inConflict.wp_proof (wp_Conflict : state.Conflict.specI (hG := hG)) :
    swift.inConflict.specI (hG := hG) := by
  intro c1 c2 v1 v2
  wp_start as %Hop
  wp_auto
  wp_apply wp_Conflict $$ [c1 c2] as -
  · iframe; ipureintro; exact Hop
  wp_end

theorem swift.keysOf.wp_proof : swift.keysOf.specI (hG := hG) := by
  intro c vs
  wp_start as %Hop
  wp_auto
  have h1 : decide (c.op = W8 3) = false := by simpa [swift.opSCAN] using Hop
  rw [h1]
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.GoType.SliceType state.Key.ty)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := state.Key.ty) [c.key]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lsl ⟨Hl, -⟩
  wp_auto
  iapply HΦ $$ Hl

theorem swift.Dep.Contains.wp_proof : swift.Dep.Contains.specI (hG := hG) := by
  intro dp dsl dq dq' ds x
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨Hdp, Hds⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave %Hl := ownSlice_len $$ Hds
  ihave HI : (∃ (i : w64) (cv : swift.CommandId), "i" ∷ i_ptr ↦ i ∗ "c" ∷ c_ptr ↦ cv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z dsl.len ∧ ∀ j < sint.nat i, ds[j]? ≠ some x⌝ :
      IProp netDistGF) $$ [i c]
  · iexists W64 0, _; iframe; ipureintro; refine ⟨by word, by word, ?_⟩; intro j hj; word
  wp_for HI
  wp_if_destruct
  · have hil : sint.nat i < ds.length := by have := Hi.1; word
    obtain ⟨y, hy⟩ : ∃ y, ds[sint.nat i]? = some y := ⟨_, List.getElem?_eq_getElem hil⟩
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z dsl.len from ⟨Hi.1, Hif⟩)]
    wp_apply (wp_load_slice_index (V := swift.CommandId) dsl (sint.Z i) _ _ y Hi.1) $$ [Hds] as Hds
    · iframe; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word, hy]
    wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (y = x))⌝))) $$ []
    · wp_if_destruct
      · ipureintro; congr 2; cases x; cases y; simp_all
      · ipureintro; congr 2; cases x; cases y; simp_all
    iintro %v %hv
    subst hv
    wp_if_destruct
    · wp_for_post
      rw [decide_eq_true (show x ∈ ds from Hif ▸ List.mem_of_getElem? hy)]
      iapply HΦ; iframe
    · wp_for_post
      iframe
      iexists i + W64 1, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro j hj
      by_cases hji : j = sint.nat i
      · subst hji; rw [hy]; intro h; cases h; exact Hif rfl
      · exact Hi.2.2 j (by word)
  · have : decide (x ∈ ds) = false := by
      simp only [decide_eq_false_iff_not]
      intro hx
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
      have : j < ds.length := by
        rcases Nat.lt_or_ge j ds.length with h | h
        · exact h
        · rw [List.getElem?_eq_none_iff.mpr h] at hj; cases hj
      exact Hi.2.2 j (by word) hj
    rw [this]
    iapply HΦ; iframe

theorem swift.Dep.Equals.wp_proofG : swift.Dep.Equals.specG (hG := hG) := by
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
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z d1.len ∧ swift.eqInv l1 l2 (sint.nat i) s1 s2⌝ :
        IProp netDistGF) $$ [i Hm1 Hm2]
    · iexists W64 0, ∅, ∅; iframe; ipureintro; refine ⟨by word, by word, swift.eqInv_zero l1 l2⟩
    wp_for HI
    wp_if_destruct
    · have hil1 : sint.nat i < l1.length := by have := Hi.1; word
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
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
        exact swift.eqInv_same Hi.2.2 Hnd.1 Hnd.2 hx (by rw [Hif]; exact hy)
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
        have hD := swift.eqInv_diff Hi.2.2 Hnd.1 Hnd.2 hx hy hxy
        wp_if_destruct
        · rw [ite_eq_left hb2]
          wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
          · iframe; ipureintro; exact hiy
          wp_apply (wp_mapDelete m1 s1' y) $$ Hm1 as Hm1
          wp_for_post
          iframe
          iexists i + W64 1, _, _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
          simp only [] at hD
          rw [if_pos Hif, if_pos Hif] at hD
          exact hD
        · rw [ite_eq_left hb2]
          wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
          · iframe; ipureintro; exact hiy
          wp_apply (wp_mapInsert _ m2 s2' y (zero_val Unit)) $$ Hm2 as Hm2
          wp_for_post
          iframe
          iexists i + W64 1, _, _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
          simp only [] at hD
          rw [if_neg Hif, if_neg Hif] at hD
          exact hD
    · have hi : sint.nat i = l1.length := by have := Hi.1; word
      have hE := Hi.2.2
      rw [hi] at hE
      have hres := swift.eqInv_end hE hlen Hnd.1 Hnd.2
      wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m1 s1) $$ [$Hm1] as ⟨Hm1, %hs1⟩
      wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m2 s2) $$ [$Hm2] as ⟨Hm2, %hs2⟩
      have hw : ∀ a b : Nat, a < 2 ^ 63 → b < 2 ^ 63 → (W64 (a : Int) = W64 (b : Int) ↔ a = b) := by
        intro a b ha hb; constructor
        · intro h; have := congrArg (fun w : w64 => w.toNat) h; simp at this; omega
        · intro h; rw [h]
      wp_if_destruct
      · wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m1 s1) $$ [$Hm1] as ⟨Hm1, -⟩
        rw [← hres]
        have e1 : (GMap.size s1 = GMap.size s2) := (hw _ _ hs1 hs2).1 Hif
        have e2 : decide (W64 (GMap.size s1 : Int) = W64 0) = decide (GMap.size s1 = 0) := by
          have := hw (GMap.size s1) 0 hs1 (by omega); simpa using this
        rw [e2]
        simp only [e1, decide_true, Bool.true_and]
        iapply HΦ; iframe
      · have e1 : ¬ (GMap.size s1 = GMap.size s2) := fun h => Hif ((hw _ _ hs1 hs2).2 h)
        rw [← hres]
        simp only [e1, decide_false, Bool.false_and]
        iapply HΦ; iframe
  · -- different lengths
    have : sp.depEq (l1.map toCmdId) (l2.map toCmdId) = false := by
      unfold sp.depEq
      cases h : (l1.map toCmdId).isPerm (l2.map toCmdId)
      · rfl
      · have := (List.isPerm_iff.mp h).length_eq
        simp only [List.length_map] at this
        exfalso; apply Hif; word
    rw [this]
    iapply HΦ; iframe

end specs

end Perennial.github_com.imdea_software.swiftpaxos
