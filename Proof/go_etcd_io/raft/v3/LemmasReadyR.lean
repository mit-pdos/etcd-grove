/-
The lemmas of the `Ready` core's proofs (raft v3.7 retarget, stage R5 phase 3, group G2:
`RawNode.readyWithoutAccept`, `acceptReady`, `Ready`, `Advance`). Pure list facts moved here
from the old `RawNode__readyWithoutAccept.lean` (`ready_committed_prefix`, `eq_of_prefix_or`,
`nonself` now over `QMsg`), and the separation-logic bookkeeping of the messages a `Ready`
hands out (D8, `readyDq`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- `if_pos`/`if_neg` (deprecated in core under those names). -/
theorem ite_pos' {α : Sort _} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := ite_eq_left_of_eq_true _ _ (eq_true h)

theorem ite_neg' {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := ite_eq_right_of_eq_false _ _ (eq_false h)

section helpers
variable [FfiSyntax]

/-- The committed entries handed out sit in the global log right after its first
`applying` entries: `fp` is the log below the boundary `prev` (`FullOk`), `es` the log
after it. -/
theorem ready_committed_prefix (fp es ce : List EntryM) (prev : entryID) (cm apg : w64)
    (Hfp : (fp.length : Int) = uint.Z prev.index')
    (Hle : uint.Z prev.index' ≤ uint.Z apg ∧ uint.Z apg ≤ uint.Z cm)
    (Hcm : uint.Z cm ≤ uint.Z prev.index' + (es.length : Int))
    (Hnw : uint.Z cm + 1 < 2 ^ 64)
    (Hce : ce <+: (plogFrom prev es (apg + W64 1)).take (uint.Z cm - uint.Z apg).toNat) :
    (fp ++ es).take (uint.Z apg).toNat ++ ce <+: (fp ++ es).take (uint.Z cm).toNat ∧
    ((fp ++ es).take (uint.Z apg).toNat).length = (uint.Z apg).toNat := by
  unfold plogFrom at Hce
  have Hk : (uint.Z (apg + W64 1) - uint.Z prev.index' - 1).toNat
      = (uint.Z apg).toNat - fp.length := by word
  rw [Hk] at Hce
  rw [List.take_append, List.take_append,
    List.take_of_length_le (l := fp) (by omega), List.take_of_length_le (l := fp) (by omega)]
  refine ⟨?_, by simp only [List.length_append, List.length_take]; word⟩
  rw [List.append_assoc, List.prefix_append_right_inj]
  have Hsplit : (uint.Z cm).toNat - fp.length
      = ((uint.Z apg).toNat - fp.length) + (uint.Z cm - uint.Z apg).toNat := by omega
  rw [Hsplit, List.take_add, List.prefix_append_right_inj]
  exact Hce

/-- `delivered` is the committed log's prefix up to `applying`: of the same length as
`pre` and comparable with `pre ++ ce` (`isCommitted_agree`), it is `pre`. -/
theorem eq_of_prefix_or {α : Type _} (l pre ce : List α) (H : l <+: pre ++ ce ∨ pre ++ ce <+: l)
    (Hl : l.length = pre.length) : l = pre := by
  rcases H with H | H
  · exact (List.prefix_of_prefix_length_le H (List.prefix_append pre ce) (by omega)).eq_of_length Hl
  · have Hle := H.length_le
    simp only [List.length_append] at Hle
    have Hce : ce = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst Hce
    rw [List.append_nil] at H
    exact (H.eq_of_length Hl.symm).symm

/-- The messages of `msgsAfterAppend` that `readyWithoutAccept` hands out (`To ≠ id`;
`acceptReady` keeps those to oneself to step). (2026-10-16, stage R5: over `QMsg`, the filter of
`ownRaftPhysReady`'s `Hundo`.) -/
abbrev nonself (id : w64) (ms : List QMsg) : List QMsg :=
  ms.filter (fun q => !isSelfQ id q)

theorem nonself_take_succ (id : w64) (ms : List QMsg) (n : Nat)
    (mm : QMsg) (Hl : ms[n]? = some mm) :
    nonself id (ms.take (n + 1)) =
      nonself id (ms.take n) ++ (if mm.st.msg.To' = id then [] else [mm]) := by
  unfold nonself
  rw [List.take_add_one, Hl]
  by_cases h : mm.st.msg.To' = id <;> simp [List.filter_append, h, isSelfQ]

/-- The messages of `msgsAfterAppend` that `acceptReady` keeps to step (`To = id`;
`readyWithoutAccept` hands out the others, `nonself`). (2026-10-16, stage R5: over `QMsg`.) -/
abbrev selfmsgs (id : w64) (ms : List QMsg) : List QMsg :=
  ms.filter (fun q => isSelfQ id q)

theorem selfmsgs_take_succ (id : w64) (ms : List QMsg) (n : Nat)
    (mm : QMsg) (Hl : ms[n]? = some mm) :
    selfmsgs id (ms.take (n + 1)) =
      selfmsgs id (ms.take n) ++ (if mm.st.msg.To' = id then [mm] else []) := by
  unfold selfmsgs
  rw [List.take_add_one, Hl]
  by_cases h : mm.st.msg.To' = id <;> simp [List.filter_append, h, isSelfQ]

/-- A response type is not a snapshot's. -/
theorem mtypeOf_resp_ne_snap (t : w32) (H : RespType t) : mtypeOf t ≠ some .snap := by
  rcases H with H | H | H <;> rw [H] <;> decide

/-- A response is not a `MsgApp`. -/
theorem resp_ne_MsgApp (t : w32) (H : RespType t) : t ≠ MsgApp := by
  rcases H with H | H | H <;> rw [H] <;> decide

/-- The messages a `Ready` hands out at `readyDq` that are responses are at half. -/
theorem readyDq_resp (st : MsgSt) (h : RespType st.msg.Type') :
    readyDq st = DFrac.own (1 : Qp).half := by
  unfold readyDq; simp [h]

end helpers

section sep
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `readyDq` of messages that are all responses is a half. -/
theorem readyDq_halves (l : List QMsg) (H : ∀ q ∈ l, RespType q.st.msg.Type') :
    ([∗list] q ∈ l, msgOwn (GF := GF) q.loc (readyDq q.st) q.st) ⊢
      [∗list] q ∈ l, msgOwn q.loc (DFrac.own (1 : Qp).half) q.st := by
  induction l with
  | nil => iintro _; iempintro
  | cons q l ih =>
    iintro H'
    icases BigSepL.bigSepL_cons.1 $$ H' with ⟨Hq, H'⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hq]
    · rw [← readyDq_resp q.st (H q List.mem_cons_self)]; iexact Hq
    · iapply (ih (fun q' hq' => H q' (List.mem_cons_of_mem _ hq'))) $$ H'

/-- ... and back. -/
theorem halves_readyDq (l : List QMsg) (H : ∀ q ∈ l, RespType q.st.msg.Type') :
    ([∗list] q ∈ l, msgOwn (GF := GF) q.loc (DFrac.own (1 : Qp).half) q.st) ⊢
      [∗list] q ∈ l, msgOwn q.loc (readyDq q.st) q.st := by
  induction l with
  | nil => iintro _; iempintro
  | cons q l ih =>
    iintro H'
    icases BigSepL.bigSepL_cons.1 $$ H' with ⟨Hq, H'⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hq]
    · rw [readyDq_resp q.st (H q List.mem_cons_self)]; iexact Hq
    · iapply (ih (fun q' hq' => H q' (List.mem_cons_of_mem _ hq'))) $$ H'

/-- Owned messages handed out at `readyDq`, the other halves (`respHalf`) kept. -/
theorem qOwns_ready (l : List QMsg) :
    ([∗list] q ∈ l, qOwn (GF := GF) q) ⊢
      ([∗list] q ∈ l, msgOwn q.loc (readyDq q.st) q.st) ∗ [∗list] q ∈ l, respHalf q := by
  induction l with
  | nil => iintro _; isplitl <;> iempintro
  | cons q l ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hq, H⟩
    icases qOwn_ready q $$ Hq with ⟨Hq1, Hq2⟩
    icases ih $$ H with ⟨H1, H2⟩
    isplitl [Hq1 H1]
    · iapply BigSepL.bigSepL_cons.2; iframe Hq1 H1
    · iapply BigSepL.bigSepL_cons.2; iframe Hq2 H2

/-- ... and back. -/
theorem qOwns_unready (l : List QMsg) :
    ([∗list] q ∈ l, msgOwn (GF := GF) q.loc (readyDq q.st) q.st) ∗ ([∗list] q ∈ l, respHalf q) ⊢
      [∗list] q ∈ l, qOwn q := by
  induction l with
  | nil => iintro _; iempintro
  | cons q l ih =>
    iintro ⟨H1, H2⟩
    icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨Hq1, H1⟩
    icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨Hq2, H2⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hq1 Hq2]
    · iapply qOwn_unready q; iframe Hq1 Hq2
    · iapply ih; iframe H1 H2

/-- The messages to others of `msgsAfterAppend`, owned, are what is handed out (at `readyDq`,
a half: they are responses) and what is kept (`otherHalf`). -/
theorem qOwns_other_ready (id : w64) (l : List QMsg) (H : ∀ q ∈ l, RespType q.st.msg.Type') :
    ([∗list] q ∈ nonself id l, qOwn (GF := GF) q) ⊢
      ([∗list] q ∈ nonself id l, msgOwn q.loc (readyDq q.st) q.st) ∗
        [∗list] q ∈ l, otherHalf id q := by
  iintro Hq
  icases (qOwns_other_halves id l).2 $$ Hq with ⟨H1, H2⟩
  iframe H2
  iapply halves_readyDq _ (fun q hq => H q (List.mem_filter.1 hq).1) $$ H1

theorem list_set_self {α : Type _} (l : List α) (i : Nat) (x : α) (h : l[i]? = some x) :
    l.set i x = l := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  by_cases hij : i = j
  · subst hij
    obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.1 h
    simp [hl, he]
  · simp [hij]

/-- One element of a `[∗list]`, taken out and put back. -/
theorem bigSepL_acc_same {α : Type _} (Φ : α → IProp GF) (l : List α) (i : Nat) (x : α)
    (h : l[i]? = some x) :
    ([∗list] y ∈ l, Φ y) ⊢ Φ x ∗ (Φ x -∗ [∗list] y ∈ l, Φ y) := by
  iintro H
  icases (BigSepL.bigSepL_lookup_acc (Φ := fun _ y => Φ y) h).1 $$ H with ⟨Hx, Hb⟩
  iframe Hx
  iintro Hx
  ihave H := Hb $$ %x Hx
  rw [list_set_self l i x h]
  iexact H

theorem readStatesPts_nil : ⊢ readStatesPts (GF := GF) slice.nil [] := by
  unfold readStatesPts
  iexists ([] : List ReadState)
  isplitr
  · iapply ownSlice_nil
  · iapply (BigSepL2.bigSepL2_nil (Φ := fun _ (v : ReadState) (st : ReadStateM) =>
      iprop(⌜v.Index' = st.Index'⌝ ∗ v.RequestCtx' ↦*□ st.RequestCtx' : IProp GF))).2
    iempintro

/-- The queued messages' contributions are in the outbox, so each one handed out was
legitimately sent (`outboxRelP_isRaftMsg`, over a list). -/
theorem outboxRelP_isRaftMsgs (γ : RaftNames) (o : List Msg) (ms1 ms2 : List QMsg)
    (Hp : outboxRelP o ms1 ms2) (l : List QMsg) (Hsub : ∀ q ∈ l, q ∈ ms1 ++ ms2) :
    ([∗list] x ∈ o, isMessage (GF := GF) γ x) ⊢ [∗list] q ∈ l, isRaftMsg γ q.st := by
  induction l with
  | nil => iintro _; iempintro
  | cons q l ih =>
    iintro #Ho
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iapply outboxRelP_isRaftMsg γ o ms1 ms2 q Hp (Hsub q List.mem_cons_self) $$ Ho
    · iapply (ih (fun q' hq' => Hsub q' (List.mem_cons_of_mem _ hq'))) $$ Ho

/-- A hard state that may be `nil` and is not empty is a read-only one. -/
theorem hsRO_of_hsOpt (p : Loc) (h : HardStateM)
    (Hne : ¬ (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0)) :
    hsOpt (GF := GF) p h ⊢ hsRO p h := by
  iintro H
  unfold hsOpt
  icases H with (%Hn | H)
  · exfalso; obtain ⟨-, rfl⟩ := Hn; exact Hne ⟨rfl, rfl, rfl⟩
  · iexact H

/-- The self-addressed messages of `msgsAfterAppend`, as the pending steps `acceptReady`
queues (2026-10-16, stage R5): each owned (`selfOwn`) becomes a `msgIn` (a response is not a
`MsgApp`, `msgOwn_to_msgIn`), `SelfMsgOk` (`AAMsgOk.selfMsgOk`), and its abstraction, at no
entries and no context, was legitimately sent (its contribution is in the outbox,
`outboxRelP_isRaftMsg`). -/
theorem self_pending (γ : RaftNames) (id t : w64) (o : List Msg) (ms1 ms2 : List QMsg)
    (Hp : outboxRelP o ms1 ms2) (l : List QMsg) (Hsub : ∀ q ∈ l, q ∈ ms1 ++ ms2)
    (Hok : ∀ q ∈ l, AAMsgOk id t q.st) :
    ⊢ ([∗list] x ∈ o, isMessage (GF := GF) γ x) -∗ ([∗list] q ∈ l, selfOwn (GF := GF) id q) -∗
      pendList γ id ((selfmsgs id l).map QMsg.loc)
        ((selfmsgs id l).map (fun q => selfPending q.st.msg)) := by
  induction l with
  | nil =>
    iintro _ _
    simp only [selfmsgs, List.filter_nil, List.map_nil]
    iapply pendList_nil
  | cons q l ih =>
    have Hsub' : ∀ q' ∈ l, q' ∈ ms1 ++ ms2 := fun q' h => Hsub q' (List.mem_cons_of_mem _ h)
    have Hok' : ∀ q' ∈ l, AAMsgOk id t q'.st := fun q' h => Hok q' (List.mem_cons_of_mem _ h)
    iintro #Ho H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hq, H⟩
    by_cases h : isSelfQ id q = true
    · simp only [selfmsgs, List.filter_cons, h, ↓reduceIte, List.map_cons]
      have hto : q.st.msg.To' = id := of_decide_eq_true h
      have Hsm := (Hok q List.mem_cons_self).selfMsgOk hto
      have Hresp : RespType q.st.msg.Type' := Hsm.1
      iapply (BigSepL2.bigSepL2_cons (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
        pendingRel γ id st p))).2
      isplitl [Hq]
      · iexists q.st
        isplitl [Hq]
        · iapply msgOwn_to_msgIn q.loc q.st (resp_ne_MsgApp _ Hresp)
          unfold selfOwn; simp only [h, ↓reduceIte]; iexact Hq
        · ihave #Hr := outboxRelP_isRaftMsg γ o ms1 ms2 q Hp (Hsub q List.mem_cons_self) $$ Ho
          unfold pendingRel selfPending
          isplitr
          · ipureintro; exact ⟨Hsm, rfl, rfl⟩
          · imodintro
            iintro %ty %Hty
            ihave H := isRaftMsg_isMessage γ q.st ty Hty
              (fun hs => mtypeOf_resp_ne_snap _ Hresp (hs ▸ Hty)) $$ Hr
            rw [Hsm.2.2.2.2.1, Hsm.2.2.2.2.2.1]
            iexact H
      · iapply ih Hsub' Hok' $$ Ho H
    · simp only [selfmsgs, List.filter_cons, h, Bool.false_eq_true, ↓reduceIte]
      iapply ih Hsub' Hok' $$ Ho H

end sep

end EtcdGrove
end Perennial
