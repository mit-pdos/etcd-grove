/-
Lean-first (no Rocq counterpart). **A `Ready` line's tokens, distributed over the handed-out queues**
(2026-11-11, trace-check Q8 stage 1 slice 27n; `notes/decisions.md`, "Q8 stage 1 (slice 27n)").
Raft-internal (not on `etc/api/raft.txt`).

`trCap_fire_ready` gives the caller the tokens of the share's pending messages before the line
(`[∗map] k ↦ m ∈ Bn, inFlight tn k m`, `Bn`'s values a permutation of `P`, `P` the outbox's traced
messages `pendAbs C o` at the idle phase). `acceptReady` hands those messages out as two queues
(`outboxRelP o ms1 ms2`: the outbox, up to order, what the queues' messages contribute). Here: the
tokens, one per queued message of a traced type, as the receiver's `recvTokOf` at the message's state
(`readyToks_queues`); the self-addressed ones are `self_pending`'s (`selfTok`), the rest the handed-out
messages'. No `MsgsUniq` is needed: a permutation of the filter-map is matched element by element
(`bigSepL_pairs_split`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRecvTok
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.TracedCap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section toks
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A token of an optional specification message: nothing for none, some token for it otherwise. -/
def optTok (F : Nat → Etcdraft.Msg → IProp GF) : Option Etcdraft.Msg → IProp GF
  | none => iprop(True)
  | some ma => iprop(∃ k, F k ma)

/-- **The tokens of a permutation of a filter-map, element by element**: resources indexed by a list
of pairs whose second components are, up to order, the `g`-images of `xs`, split over `xs`. -/
theorem bigSepL_pairs_split {A : Type} (F : Nat → Etcdraft.Msg → IProp GF)
    (g : A → Option Etcdraft.Msg) :
    ∀ (xs : List A) (L : List (Nat × Etcdraft.Msg)), (L.map Prod.snd).Perm (xs.filterMap g) →
    ([∗list] p ∈ L, F p.1 p.2) ⊢ [∗list] x ∈ xs, optTok F (g x) := by
  intro xs
  induction xs with
  | nil =>
    intro L h
    have hL : L = [] := by
      have := h.length_eq
      simp only [List.filterMap_nil, List.length_nil, List.length_map] at this
      exact List.eq_nil_of_length_eq_zero this
    subst hL
    iintro _
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons x xs ih =>
    intro L h
    cases hg : g x with
    | none =>
      rw [List.filterMap_cons_none hg] at h
      iintro H
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · rw [hg]; simp only [optTok]; itrivial
      · iapply ih L h $$ H
    | some ma =>
      rw [List.filterMap_cons_some hg] at h
      have hmem : ma ∈ L.map Prod.snd := h.symm.subset List.mem_cons_self
      obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hmem
      obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hp
      have hperm : (l1 ++ p :: l2).Perm (p :: (l1 ++ l2)) := List.perm_middle
      have h' : ((l1 ++ l2).map Prod.snd).Perm (xs.filterMap g) := by
        have := (hperm.map Prod.snd).symm.trans h
        rw [List.map_cons, hpe] at this
        exact this.cons_inv
      iintro H
      ihave H := (BigSepL.bigSepL_perm (Φ := fun p : Nat × Etcdraft.Msg => F p.1 p.2) hperm).1 $$ H
      icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hp, H⟩
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hp]
      · rw [hg]; simp only [optTok]
        iexists p.1
        rw [← hpe]
        iexact Hp
      · iapply ih (l1 ++ l2) h' $$ H

/-- **`trCap_fire_ready`'s tokens over any list whose `g`-images are its messages**, up to order. -/
theorem readyToks_split {A : Type} (tn : TraceNames) (Bn : GMap Nat Etcdraft.Msg)
    (P : List Etcdraft.Msg) (hB : ((GMap.toList Bn).map Prod.snd).Perm P)
    (g : A → Option Etcdraft.Msg) (xs : List A) (hx : P.Perm (xs.filterMap g)) :
    ([∗map] k ↦ m ∈ Bn, inFlight (GF := GF) tn k m) ⊢
      [∗list] x ∈ xs, optTok (fun k m => inFlight (GF := GF) tn k m) (g x) := by
  iintro H
  ihave H := (BigSepM.bigSepM_toList (Φ := fun k m => inFlight (GF := GF) tn k m) (m := Bn)).1 $$ H
  iapply bigSepL_pairs_split (fun k m => inFlight (GF := GF) tn k m) g xs (GMap.toList Bn)
    (hB.trans hx) $$ H

/-- The specification messages of the queues' contributions, at the voters `C`. -/
def qAbsTr (C : List w64) (qa : QMsg × Option Msg) : Option Etcdraft.Msg :=
  qa.2.bind (TraceSim.msgAbs C C.length)

/-- The outbox's traced messages are the queues' contributions', up to order. -/
theorem pendAbs_outboxRelP (C : List w64) (o : List Msg) (ms1 ms2 : List QMsg)
    (as1 as2 : List (Option Msg)) (hp : o.Perm (absList as1 ++ absList as2))
    (h1 : List.Forall₂ (fun q a => msgAbs q.st a) ms1 as1)
    (h2 : List.Forall₂ (fun q a => msgAbs q.st a) ms2 as2) :
    (pendAbs C o).Perm (((ms1 ++ ms2).zip (as1 ++ as2)).filterMap (qAbsTr C)) := by
  have hl : (ms1 ++ ms2).length = (as1 ++ as2).length := by
    simp only [List.length_append, h1.length_eq, h2.length_eq]
  have hz : ((ms1 ++ ms2).zip (as1 ++ as2)).filterMap (qAbsTr C) =
      (as1 ++ as2).filterMap (fun a => a.bind (TraceSim.msgAbs C C.length)) := by
    clear hp h1 h2
    generalize ms1 ++ ms2 = xs at hl ⊢
    generalize as1 ++ as2 = ys at hl ⊢
    induction xs generalizing ys with
    | nil => cases ys with
      | nil => rfl
      | cons _ _ => simp at hl
    | cons x xs ih => cases ys with
      | nil => simp at hl
      | cons y ys =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [List.zip_cons_cons, List.filterMap_cons, qAbsTr]
        cases y with
        | none => simpa [qAbsTr] using ih ys hl
        | some y =>
          simp only [Option.bind_some]
          cases TraceSim.msgAbs C C.length y with
          | none => simpa [qAbsTr] using ih ys hl
          | some z => simpa [qAbsTr] using ih ys hl
  rw [hz]
  unfold pendAbs
  have hab : absList as1 ++ absList as2 = absList (as1 ++ as2) := by
    simp only [absList, List.filterMap_append]
  rw [hab] at hp
  refine (hp.filterMap _).trans ?_
  unfold absList
  rw [List.filterMap_filterMap]
  apply List.Perm.of_eq
  congr 1

/-- A traced type's message has a specification counterpart. -/
theorem msgAbs_absMsg_traced (C : List w64) (bl : Nat) (ty : MsgType) (m : MessageM)
    (ents : List EntryM) (ctx : List w8) (h : ty.traced = true) :
    ∃ ma, TraceSim.msgAbs C bl (absMsg ty m ents ctx) = some ma := by
  cases ty <;> simp [MsgType.traced] at h <;> exact ⟨_, rfl⟩

/-- **A queued message's token**, from its contribution's: the receiver's `recvTokOf`. -/
theorem optTok_recvTok (γd : GName) (tn : TraceNames) (q : QMsg) (a : Option Msg)
    (ha : msgAbs q.st a) :
    ⊢ traceDir (GF := GF) γd tn -∗
      optTok (fun k m => inFlight (GF := GF) tn k m) (qAbsTr tn.voters (q, a)) -∗
      recvTokOf γd q.st.msg q.st.ents q.st.ctx := by
  iintro #Hd Ht
  iunfold recvTokOf
  iintro %ty %hty
  obtain ⟨hty, htr⟩ := hty
  rcases ha with ⟨hn, -⟩ | ⟨ty', ht', -, rfl⟩ | ⟨sv, hs, -, -⟩
  · rw [hn] at hty; cases hty
  · rw [ht'] at hty
    cases hty
    obtain ⟨ma, hma⟩ := msgAbs_absMsg_traced tn.voters tn.voters.length ty q.st.msg q.st.ents
      q.st.ctx htr
    simp only [qAbsTr, Option.bind_some, hma, optTok]
    icases Ht with ⟨%k, Hk⟩
    iexists tn, k, ma
    iframe Hd Hk
    ipureintro; exact hma
  · rw [hs] at hty; cases hty; simp [MsgType.traced] at htr

/-- The tokens of a queue's contributions, as its messages' `recvTokOf`. -/
theorem zipToks (γd : GName) (tn : TraceNames) :
    ∀ (ms : List QMsg) (as_ : List (Option Msg)), List.Forall₂ (fun q a => msgAbs q.st a) ms as_ →
    ⊢ traceDir (GF := GF) γd tn -∗
      ([∗list] qa ∈ ms.zip as_, optTok (fun k m => inFlight (GF := GF) tn k m) (qAbsTr tn.voters qa)) -∗
      [∗list] q ∈ ms, recvTokOf γd q.st.msg q.st.ents q.st.ctx := by
  intro ms as_ h
  induction h with
  | nil =>
    iintro _ _
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | @cons q a ms as_ hqa _ ih =>
    iintro #Hd H
    rw [List.zip_cons_cons]
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hq, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hq]
    · iapply optTok_recvTok γd tn q a hqa $$ Hd Hq
    · iapply ih $$ Hd H

/-- **A `Ready` line's tokens over the handed-out queues** (see the header): with `P` the outbox's
traced messages at the names' voters (the idle phase's) and `Bn`'s values a permutation of `P`, one
`recvTokOf` per queued message (`True`-like for an untraced type). -/
theorem readyToks_queues (γd : GName) (tn : TraceNames) (Bn : GMap Nat Etcdraft.Msg)
    (P : List Etcdraft.Msg) (hB : ((GMap.toList Bn).map Prod.snd).Perm P)
    (o : List Msg) (ms1 ms2 : List QMsg) (hP : P = pendAbs tn.voters o)
    (hrel : outboxRelP o ms1 ms2) :
    ⊢ traceDir (GF := GF) γd tn -∗ ([∗map] k ↦ m ∈ Bn, inFlight (GF := GF) tn k m) -∗
      [∗list] q ∈ ms1 ++ ms2, recvTokOf γd q.st.msg q.st.ents q.st.ctx := by
  obtain ⟨as1, as2, hp, h1, h2⟩ := hrel
  have hx := pendAbs_outboxRelP tn.voters o ms1 ms2 as1 as2 hp h1 h2
  rw [← hP] at hx
  iintro #Hd H
  ihave H := readyToks_split tn Bn P hB (qAbsTr tn.voters) _ hx $$ H
  rw [List.zip_append h1.length_eq]
  icases (BigSepL.bigSepL_append (Φ := fun _ qa => optTok (fun k m => inFlight (GF := GF) tn k m)
    (qAbsTr tn.voters qa))).1 $$ H with ⟨H1, H2⟩
  iapply (BigSepL.bigSepL_append (Φ := fun _ q => recvTokOf (GF := GF) γd q.st.msg q.st.ents q.st.ctx)
    (l₁ := ms1) (l₂ := ms2)).2
  isplitl [H1]
  · iapply zipToks γd tn ms1 as1 h1 $$ Hd H1
  · iapply zipToks γd tn ms2 as2 h2 $$ Hd H2

end toks

end EtcdGrove
end Perennial
