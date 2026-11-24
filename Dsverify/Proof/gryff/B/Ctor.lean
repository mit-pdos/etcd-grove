/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Ctor.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B: the constructors `NewReplica` calls in `gryffcommon` (`NewGryffParticipant`,
`NewGryffCoordinator`): the participant / coordinator at the initial model state.
-/
module

public import Dsverify.Proof.gryff.Replica2.State
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open model replica2

attribute [local instance] GooseGlobalGS.gooseInvGS

set_option goose.wp.extras true

/-- The coordinator's `allReplicas` loop's step. -/
theorem set_prefix (xs : List w32) (j : Nat) (hj : j < xs.length) {v : w32} (hv : v = W32 j)
    (h : ∀ m : Nat, m < j → xs.getD m (W32 0) = W32 m) (n : Nat) (hn : n = j + 1) :
    ∀ m : Nat, m < n → (xs.set j v).getD m (W32 0) = W32 m := by
  subst hn hv
  intro m hm
  rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h1 | rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
    exact h m h1
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hj]
    rfl

/-- The coordinator's `allReplicas` after the loop. -/
theorem prefix3 (xs : List w32) (hl : xs.length = 3)
    (h : ∀ m : Nat, m < 3 → xs.getD m (W32 0) = W32 m) : xs = [W32 0, W32 1, W32 2] := by
  match xs, hl with
  | [a, b, c], _ =>
    have h0 := h 0 (by omega)
    have h1 := h 1 (by omega)
    have h2 := h 2 (by omega)
    simp at h0 h1 h2
    subst h0 h1 h2
    rfl

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [wire.BufioSpecs GF]

/-- An empty Go map represents an empty association list. -/
theorem amapRep_nil {n : Nat} {V : Type} (mR : Loc) (am : AMap n V) (R : Loc → V → IProp GF)
    (h : ∀ key, am.get? key = none) :
    mR ↦$ (∅ : GMap (BitVec n) Loc) ⊢ amapRep mR am R := by
  iintro H
  unfold amapRep
  iexists ∅
  iframe
  isplitr
  · ipureintro; intro key; simp [h]
  · iapply BigSepM.bigSepM_empty.2
    iempintro

/-- `gryffcommon.NewGryffParticipant(id, iparti, false)`: the participant at the initial state
(no stored tag, no ongoing write). -/
theorem NewGryffParticipant_wp (k : Fin 3) (ip : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon }}
      (App (App (App (Val (@! gryff.src.gryffcommon.NewGryffParticipant)) (Val #(rid32 k)))
        (Val #ip)) (Val #false))
    {{ (pa : Loc), RET #pa; partiOwn pa ip k (RState.init k.val).tag
        (RState.init k.val).ongoing }} := by
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc) src.state.Key.ty
    (go.GoType.PointerType src.gryffcommon.StoreMetadata.ty)) as %smR Hsm
  wp_apply (wp_map_make1 (K := w32) (V := Loc) go.int32
    (go.GoType.PointerType src.gryffcommon.OngoingWriteOp.ty)) as %owR How
  iStructNamed «$r0»
  ipersist id
  ipersist iparti
  ipersist storeTag
  ipersist noConflicts
  ipersist OngoingWrites
  imodintro
  iapply HΦ
  unfold partiOwn
  iexists smR, owR, ∅, ∅
  iframe
  iframe #
  isimp
  isplitr
  · itrivial
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; intro c; rfl
  iempintro

/-- `gryffcommon.NewGryffCoordinator(id, icoord, false, 3, true, false, false)` (the kit's
configuration): the coordinator at the initial state. -/
theorem NewGryffCoordinator_wp (ρ : Repl2Names) (k : Fin 3) (ic : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon }}
      (App (App (App (App (App (App (App (Val (@! gryff.src.gryffcommon.NewGryffCoordinator))
        (Val #(rid32 k))) (Val #ic)) (Val #false)) (Val #(W64 3))) (Val #true)) (Val #false))
        (Val #false))
    {{ (co : Loc), RET #co; coordOwn ρ co ic k (RState.init k.val) }} := by
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc) go.int64
    (go.GoType.PointerType src.gryffcommon.ReadOp.ty)) as %ropsR Hrops
  wp_apply (wp_map_make1 (K := w64) (V := Loc) go.int64
    (go.GoType.PointerType src.gryffcommon.WriteOp.ty)) as %wopsR Hwops
  wp_apply (wp_slice_make2 (V := w32) (W64 3)) as %arS ⟨Har, -⟩
  · ipureintro; decide
  wp_apply (wp_map_make1 (K := w32) (V := Loc) go.int32
    (go.GoType.PointerType src.gryffcommon.OngoingOp.ty)) as %orR Hor
  wp_apply (wp_map_make1 (K := w64) (V := w32) src.state.Key.ty go.int32) as %fkR Hfk
  wp_apply (wp_map_make1 (K := w64) (V := Loc) src.state.Key.ty
    (go.GoType.PointerType src.gryffproto.Tag.ty)) as %mtR Hmt
  wp_apply (wp_slice_make2 (V := w64) (W64 0)) as %fkc ⟨Hfkc, -⟩
  · ipureintro; decide
  ihave IH : iprop(∃ (j : w64) (xs : List w32),
      "i" ∷ i_ptr ↦ j ∗ "Har" ∷ arS ↦* xs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 3 ∧ xs.length = 3 ∧
        ∀ m : Nat, m < sint.nat j → xs.getD m (W32 0) = W32 m⌝) $$ [i Har]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by decide, by decide, by simp, ?_⟩
    intro m hm
    simp at hm; omega
  wp_for IH
  wp_if_destruct
  · ihave %Hlen := ownSlice_len $$ Har
    obtain ⟨Hj0, Hj3, Hxl, Hxs⟩ := Hj
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z arS.len := by
      refine ⟨Hj0, ?_⟩
      have h1 := Hlen.1
      rw [Hxl] at h1
      have : sint.Z (W64 3) = 3 := by decide
      word
    rw [if_pos hb]
    wp_apply wp_store_slice_index arS (sint.Z j) xs (W32 (sint.Z j)) $$ [Har] as Har
    · iframe; ipureintro; exact ⟨Hj0, by word⟩
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    have hlt : sint.Z j < 3 := by rw [show sint.Z (W64 3) = 3 by decide] at Hif; exact Hif
    refine ⟨by word, by word, by simp [Hxl], ?_⟩
    have hjn : (sint.Z j).toNat = sint.nat j := rfl
    have hz : ((sint.nat j : Nat) : Int) = sint.Z j := by
      show ((sint.Z j).toNat : Int) = sint.Z j; omega
    rw [hjn]
    exact set_prefix xs (sint.nat j) (v := W32 (sint.Z j)) (by rw [Hxl]; omega) (by rw [hz]) Hxs
      _ (by word)
  · obtain ⟨Hj0, Hj3, Hxl, Hxs⟩ := Hj
    have hj3 : sint.nat j = 3 := by
      have : sint.Z (W64 3) = 3 := by decide
      show (sint.Z j).toNat = 3; omega
    rw [hj3] at Hxs
    have hx : xs = [W32 0, W32 1, W32 2] := prefix3 xs Hxl Hxs
    subst hx
    iStructNamed «$r0»
    ipersist id
    ipersist icoord
    ipersist regular
    ipersist numReplicas
    ipersist allReplicas
    ipersist proxy
    ipersist thrifty
    ipersist epaxosMode
    ipersist rops
    ipersist wops
    ipersist OngoingReqs
    ipersist MaxTags
    ipersist ForcedKeys
    ipersist Har
    imodintro
    iapply HΦ
    unfold coordOwn
    iexists ropsR, wopsR, orR, mtR, fkR, arS, _, _, fkc, ∅, ∅
    iframe
    iframe #
    isimp
    isplitr
    · itrivial
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact List.Pairwise.nil -- H1-R10: no write op at boot
    isplitr
    · ipureintro; intro _ _ h; cases h -- H1b-R1: no read op at boot
    isplitl [Hrops]
    · iapply amapRep_nil _ _ _ (fun _ => rfl) $$ Hrops
    isplitl [Hwops]
    · iapply amapRep_nil _ _ _ (fun _ => rfl) $$ Hwops
    · iapply amapRep_nil _ _ _ (fun _ => rfl) $$ Hor

end

end Perennial.gryff.unitB
