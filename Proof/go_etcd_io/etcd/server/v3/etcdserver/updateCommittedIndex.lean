/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/updateCommittedIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.updateCommittedIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A batch's last index (or 0 for none) is at most the index of the log after it. -/
theorem srvIdxOk_last_le (ai0 : w64) (A ce : List EntryModel) (ci : w64)
    (h : srvIdxOk ai0 (A ++ ce))
    (hci : (ce.getLast?).map EntryModel.index = some ci ∨ (ce = [] ∧ ci = W64 0)) :
    uint.Z ci ≤ uint.Z ai0 + (A ++ ce).length := by
  have hai0 : 0 ≤ uint.Z ai0 := by word
  rcases hci with h1 | ⟨-, rfl⟩
  · cases hl : ce.getLast? with
    | none => rw [hl] at h1; cases h1
    | some m =>
      rw [hl] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      subst h1
      have hne : ce ≠ [] := by intro he; subst he; cases hl
      have hpos : 0 < ce.length := List.length_pos_iff.mpr hne
      rw [List.getLast?_eq_getElem?] at hl
      have hk : (A ++ ce)[A.length + (ce.length - 1)]? = some m := by
        rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hl
      have := (h.2 _ m hk).1
      simp only [List.length_append]
      push_cast at this ⊢
      omega
  · rw [show uint.Z (W64 0) = 0 from rfl]
    simp only [List.length_append]
    push_cast
    omega

theorem updateCommittedIndex.wp_proof
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    updateCommittedIndex.spec (GF := GF) (hG := hG) := by
  have hGI := wp_entryAt_GetIndex hGI
  intro ap rh es ceL A ce R γr
  wp_start as ⟨#Hes, #Hsl, #Hents, #Hsnap, #Hrh, HR, #Hlog, %Hidx⟩
  imod monoNatLbOwn_0 (GF := GF) γr.committed with #H0
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  iunfold entriesAt at Hents
  icases Hents with ⟨%Hlen2, #Hent⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  -- `ci`: the last entry's index, or 0
  wp_join iprop(∃ ci : w64, ci_ptr ↦ ci ∗ ap_ptr ↦ ap ∗
      ⌜(ce.getLast?).map EntryModel.index = some ci ∨ (ce = [] ∧ ci = W64 0)⌝)
    at next with [ci ap] as ⟨%ci, ci, ap, %Hci⟩
  · wp_if_destruct
    · -- no entries: `ci` stays 0
      (try wp_auto)
      isplitr
      · itrivial
      iexists _; iframe ci ap
      ipureintro
      right
      refine ⟨?_, rfl⟩
      have h0 : sint.Z es.len = 0 := by
        rw [show es.len = W64 0 by first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)]
        rfl
      have : ceL.length = 0 := by rw [Hlen.1]; unfold sint.nat; rw [Hif]; rfl
      exact List.length_eq_zero_iff.mp (by rw [← Hlen2]; exact this)
    · have hlenz : 0 < sint.Z es.len := by
        rcases Hlen with ⟨h1, h2⟩
        rcases Int.lt_or_eq_of_le h2 with h | h
        · exact h
        · exfalso; apply Hif; word
      have hlenpos : 0 < ceL.length := by rw [Hlen.1]; word
      list_elem ceL (ceL.length - 1) as e
      have hm : ∃ m, ce[ceL.length - 1]? = some m := by
        rw [List.getElem?_eq_getElem (by omega)]; exact ⟨_, rfl⟩
      obtain ⟨m, hm⟩ := hm
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply wp_load_slice_index es (sint.Z (es.len - W64 1)) ceL
        DFrac.discard e (by word) $$ [] as -
      · iframe Hsl; ipureintro
        have : (sint.Z (es.len - W64 1)).toNat = ceL.length - 1 := by word
        rw [this]; exact He_lookup
      ihave He := Hent $$ %(ceL.length - 1) %e %m %He_lookup %hm
      wp_apply hGI e m $$ [$Hrpkg $He]
      (try wp_auto)
      isplitr
      · itrivial
      iexists _; iframe ci ap
      ipureintro
      left
      rw [List.getLast?_eq_getElem?, ← Hlen2, hm]
      rfl
  -- `ap.snapshot != nil`: never (no snapshot)
  iunfold isReadyHandler at Hrh
  icases Hrh with ⟨%gl, %ul, %uls, %uci, #Hgl, #Hul, #Huls, #Huci, #Hglt, #Hult, #Hulst, #Hucit⟩
  wp_if_destruct
  · iapply HΦ
    iframe HR
    unfold committedLast
    rcases Hci with h | ⟨h, -⟩
    · cases hl : ce.getLast? with
      | none => simp only; itrivial
      | some m =>
        simp only
        rw [hl] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [h]
        iunfold committedAtLeast
        rw [show uint.nat (W64 0) = 0 from rfl]
        iexact H0
    · subst h; simp only [List.getLast?_nil]; itrivial
  · ispecialize Hucit $$ %ci %(A ++ ce)
    -- (`wp_bind` then `iapply`: a `wp_apply` of the hypothesis triple inside `exceptionDo` can
    -- close the goal with a synthetic `sorry`)
    wp_bind (App (Val #uci) (Val #ci))
    iapply Hucit $$ [HR]
    · iframe HR Hlog
      ipureintro; exact srvIdxOk_last_le γr.raft.ai0 A ce ci Hidx Hci
    inext
    iintro ⟨HR, #Hca⟩
    wp_auto
    iapply HΦ
    iframe HR
    unfold committedLast
    rcases Hci with h | ⟨-, h⟩
    · cases hl : ce.getLast? with
      | none => rw [hl] at h; cases h
      | some m =>
        simp only
        rw [hl] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [h]; iexact Hca
    · exfalso; apply Hif; rw [h]

end proof

end EtcdGrove
end Perennial
