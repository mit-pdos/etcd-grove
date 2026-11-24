/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Specs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: what the Gryff register handlers do to the read records, the ongoing requests and the
`Write2` accounting (specs by `peel`/`simp`).
-/
module

public import Dsverify.Proof.gryff.PureLb.Frame

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

/-- A read record as `StartRead` creates it. -/
def freshRead (rid cid n : w32) : ReadOp :=
  { requestId := rid, clientId := cid, n, maxValTag := none, readValTag := none,
    numRead1Replies := 1, numRead2Replies := 0, readsWithMaxTag := 0, sentRead2Round := false,
    determinedReadVal := false, replicasWithMaxTag := [] }

/-- The record is as created (the first `Read1Reply` completes a read). -/
def Fresh (rd : ReadOp) : Prop := rd = freshRead rd.requestId rd.clientId rd.n

theorem stepRead1Reply_fresh {s s' : RState} {m : Read1ReplyM} {o : List Out} {rid cid n : w32}
    (hk : s.rops.get? (shiftInts m.requestId m.clientId) = some (freshRead rid cid n))
    (h : stepRead1Reply s m = .ok (s', o)) :
    s' = { s.overwrite m.vt.v m.vt.t with
      ongoingReqs := s.ongoingReqs.del n, rops := s.rops.del (shiftInts m.requestId m.clientId) } ∧
    o = [.ext (.readReply cid rid m.vt.v 1)] := by
  unfold stepRead1Reply at h
  simp only [hk] at h
  simp [freshRead, NHALF, sge, sle, overwrite_rops, overwrite_ongoingReqs] at h
  rw [pure_ok_iff] at h; cases h; exact ⟨rfl, rfl⟩

theorem stepRead1Reply_none {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (hk : s.rops.get? (shiftInts m.requestId m.clientId) = none)
    (h : stepRead1Reply s m = .ok (s', o)) : s' = s ∧ o = [] := by
  unfold stepRead1Reply at h
  simp only [hk] at h
  rw [pure_ok_iff] at h; cases h; exact ⟨rfl, rfl⟩

theorem stepRead1_spec {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) :
    FR s s' ∧ FW s s' ∧ tagLe m.vt.t.toP s'.tag.toP ∧ ∃ x, sendTo m.replicaId
      (.read1Reply ⟨m.requestId, m.clientId, s'.id, s'.storeVT⟩) = some x ∧ o = [x] := by
  unfold stepRead1 at h
  peel h
  all_goals (cases h)
  all_goals (exact ⟨by fr_fin_st, by fw_fin_st, (overwrite_tag _ _ _).2, _, ‹_›, rfl⟩)

theorem stepWrite2_spec {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) :
    FR s s' ∧ FW s s' ∧ tagLe m.vt.t.toP s'.tag.toP ∧ ∃ x, sendTo m.replicaId
      (.write2Reply ⟨m.requestId, m.clientId, if s.tag.lt m.vt.t then 1 else 0⟩) = some x ∧ o = [x] := by
  unfold stepWrite2 at h
  peel h
  all_goals (cases h)
  all_goals (exact ⟨by fr_fin_st, by fw_fin_st, (overwrite_tag _ _ _).2, _, ‹_›, rfl⟩)

theorem stepWrite1_fr {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) : FR s s' := by
  unfold stepWrite1 at h
  peel h
  all_goals (cases h)
  all_goals fr_fin_st

theorem stepClientRMW_fr {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d a b = .ok (s', o)) :
    s'.rops = s.rops ∧ s'.ongoingReqs = s.ongoingReqs ∧ s'.maxN = s.maxN ∧
      s'.nReqs = s.nReqs + 1 ∧ s.nReqs < 24 ∧ NoR o := by
  unfold stepClientRMW at h
  peel h
  obtain ⟨-, -, h⟩ := handlePropose_ok h; unfold handleProposeBody at h
  have hh := startPhase1_fr h
  obtain ⟨⟨e1, e2, e3, e4⟩, hn⟩ := hh
  refine ⟨e1, e2, e3, e4, ?_, hn⟩
  have := ‹¬s.nReqs ≥ 24›; omega

/-- Lookups only lose entries. -/
def Shrinks {n : Nat} {V : Type} (a b : model.AMap n V) : Prop :=
  ∀ k v, b.get? k = some v → a.get? k = some v

theorem Shrinks.rfl' {n : Nat} {V : Type} {a : model.AMap n V} : Shrinks a a := fun _ _ h => h
theorem Shrinks.trans' {n : Nat} {V : Type} {a b c : model.AMap n V} (h1 : Shrinks a b)
    (h2 : Shrinks b c) : Shrinks a c := fun k v h => h1 k v (h2 k v h)
theorem Shrinks.del {n : Nat} {V : Type} (a : model.AMap n V) (k : BitVec n) :
    Shrinks a (a.del k) := by
  intro k' v h; rw [AMap.get?_del] at h; split at h
  · cases h
  · exact h

theorem forIn_opt_inv_mem {α β : Type} (l : List α) (b : β) (f : α → β → Option (ForInStep β))
    (P : β → Prop) (h0 : P b) (hf : ∀ a ∈ l, ∀ b st, P b → f a b = some st → P st.value) :
    ∀ r, forIn l b f = some r → P r := by
  induction l generalizing b with
  | nil => intro r h; cases h; exact h0
  | cons a l ih =>
    intro r h
    rw [List.forIn_cons] at h
    cases hfa : f a b with
    | none => rw [hfa] at h; cases h
    | some st =>
      have := hf a (by simp) b st h0 hfa
      rw [hfa] at h
      cases st with
      | done b' => cases h; exact this
      | yield b' => exact ih b' this (fun a ha => hf a (by simp [ha])) r h

/-- A short-circuit reply. -/
def SCOut (s : RState) (n : w32) (v : w64) (x : Out) : Prop :=
  ∃ cid rid, x = .ext (.readReply cid rid v 1) ∧ ∃ op, s.ongoingReqs.get? n = some op ∧
    ∃ k ∈ op.shortReads, ∃ e, s.ongoingReqs.get? k = some e ∧ e.clientId = cid ∧
      e.requestId = rid ∧ ∃ rd, s.rops.get? (shiftInts rid cid) = some rd

theorem ex_ids {X : model.AMap 32 OngoingOp} {n : w32} {op : OngoingOp} {sr : List w32}
    (h : X.get? n = some op) : ∃ e0, X.get? n = some e0 ∧
      ({ op with shortReads := sr }).requestId = e0.requestId ∧
      ({ op with shortReads := sr }).clientId = e0.clientId := ⟨op, h, rfl, rfl⟩

theorem shortCircuit_spec {s s' : RState} {n : w32} {value : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n value f = some (s', o)) :
    ∃ X Y, s' = { s with ongoingReqs := X, rops := Y } ∧
    Shrinks s.ongoingReqs (X.del n) ∧ Shrinks s.rops Y ∧
    (∀ k e, k ≠ n → s.ongoingReqs.get? k = some e → X.get? k = none →
      Y.get? (shiftInts e.requestId e.clientId) = none ∧
      (s.rops.get? (shiftInts e.requestId e.clientId)).isSome) ∧
    ∀ x ∈ o, SCOut s n value.v x := by
  unfold shortCircuit at h
  opeel h
  all_goals (try (cases h))
  all_goals (
    refine (fun H => ?_) (forIn_opt_inv_mem _ _ _ (fun p : RState × List Out =>
      (∃ X Y, p.1 = { s with ongoingReqs := X, rops := Y } ∧
        Shrinks s.ongoingReqs (X.del n) ∧
        (∀ e, X.get? n = some e → ∃ e0, s.ongoingReqs.get? n = some e0 ∧
          e.requestId = e0.requestId ∧ e.clientId = e0.clientId) ∧
        Shrinks s.rops Y ∧
        (∀ k e, k ≠ n → s.ongoingReqs.get? k = some e → X.get? k = none →
          Y.get? (shiftInts e.requestId e.clientId) = none ∧
          (s.rops.get? (shiftInts e.requestId e.clientId)).isSome)) ∧
      ∀ x ∈ p.2, SCOut s n value.v x) ?_ ?_ _ ‹forIn _ _ _ = some _›)
    · obtain ⟨⟨X, Y, hXY, h1, -, h2, h4⟩, h3⟩ := H
      exact ⟨X, Y, hXY, h1, h2, h4, h3⟩)
  all_goals (first
    | (
    intro a ha b st hb hf
    opeel hf
    all_goals (cases hf)
    all_goals (try exact hb)
    rename_i _ e he _ rd hrd
    obtain ⟨⟨X, Y, hX, h1, h1n, h2, h4⟩, h3⟩ := hb
    obtain ⟨b1, b2⟩ := b
    simp only at hX he hrd h3 ⊢
    subst hX
    simp only at he hrd
    -- the entry at `a` is `s`'s (or, at `n`, has its ids)
    have hea : ∃ e0, s.ongoingReqs.get? a = some e0 ∧ e.requestId = e0.requestId ∧
        e.clientId = e0.clientId := by
      by_cases han : a = n
      · subst han; exact h1n e he
      · refine ⟨e, h1 _ _ ?_, rfl, rfl⟩
        rw [AMap.get?_del, if_neg han]; exact he
    refine ⟨⟨_, _, rfl, fun k v hk => ?_, fun e' he' => ?_, h2.trans' (Shrinks.del _ _),
      fun k e0 hkn hk hk' => ?_⟩, fun x hx => ?_⟩
    · simp only [AMap.get?_del] at hk
      split at hk
      · cases hk
      · split at hk
        · cases hk
        · exact h1 k v (by rw [AMap.get?_del, if_neg (by assumption)]; exact hk)
    · simp only [AMap.get?_del] at he'
      split at he'
      · cases he'
      · exact h1n e' he'
    · simp only [AMap.get?_del] at hk' ⊢
      by_cases hka : k = a
      · subst hka
        have : e0 = e := by
          have := h1 _ _ (by rw [AMap.get?_del, if_neg hkn]; exact he); rw [hk] at this
          cases this; rfl
        subst this
        refine ⟨by simp, ?_⟩
        rw [h2 _ _ hrd]; rfl
      · rw [if_neg hka] at hk'
        obtain ⟨c1, c2⟩ := h4 k e0 hkn hk hk'
        refine ⟨?_, c2⟩
        split
        · rfl
        · exact c1
    · rcases List.mem_append.1 hx with hx | hx
      · exact h3 x hx
      · rw [List.mem_singleton.1 hx]
        have ha' := (List.mergeSort_perm _ _).mem_iff.1 ha
        obtain ⟨e0, he0, ea, eb⟩ := hea
        exact ⟨_, _, rfl, _, ‹s.ongoingReqs.get? n = some _›, a, ha', e0, he0, eb.symm, ea.symm,
          rd, h2 _ _ hrd⟩)
    | (refine ⟨⟨_, _, rfl, fun k v hk => ?_, fun e he => ?_, Shrinks.rfl', fun k e hkn hk hk' => ?_⟩,
         by simp⟩
       · simp only [AMap.get?_del, AMap.get?_put] at hk
         split at hk
         · cases hk
         · first | exact hk | (rw [if_neg (by assumption)] at hk; exact hk)
       · simp only [AMap.get?_put, if_pos] at he
         cases he
         exact ex_ids (by assumption)
       · simp only [AMap.get?_put, if_neg hkn] at hk'
         rw [hk] at hk'; cases hk'))

end Perennial.gryff.pure

namespace Perennial.gryff.pure
open model kahn proto

def w2bump (w : WriteOp) (a : w32) : WriteOp :=
  { w with numWrite2Replies := w.numWrite2Replies + 1,
           numWrite2Applies := if sgt a 0 then w.numWrite2Applies + 1 else w.numWrite2Applies }

theorem stepWrite2Reply_none {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (hk : s.wops.get? (shiftInts m.requestId m.clientId) = none)
    (h : stepWrite2Reply s m = .ok (s', o)) : s' = s ∧ o = [] := by
  unfold stepWrite2Reply at h
  simp only [hk] at h
  rw [pure_ok_iff] at h; cases h; exact ⟨rfl, rfl⟩

theorem stepWrite1Reply_none {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (hk : s.wops.get? (shiftInts m.requestId m.clientId) = none)
    (h : stepWrite1Reply s m = .ok (s', o)) : s' = s ∧ o = [] := by
  unfold stepWrite1Reply at h
  simp only [hk] at h
  rw [pure_ok_iff] at h; cases h; exact ⟨rfl, rfl⟩

theorem stepWrite2Reply_some {s s' : RState} {m : Write2ReplyM} {o : List Out} {w : WriteOp}
    (hk : s.wops.get? (shiftInts m.requestId m.clientId) = some w)
    (h : stepWrite2Reply s m = .ok (s', o)) :
    (s' = { s with wops := s.wops.put (shiftInts m.requestId m.clientId) (w2bump w m.applied) } ∧
      o = []) ∨
    ∃ wt s1 outs, w.writeTag = some wt ∧
      ((sge (w2bump w m.applied).numWrite2Applies (NHALF + 1) = true ∧
         shortCircuit s w.n ⟨w.writeValue, wt⟩ false = some (s1, outs)) ∨ (s1 = s ∧ outs = [])) ∧
      s' = { s1 with wops := s1.wops.del (shiftInts m.requestId m.clientId),
                     ongoingReqs := s1.ongoingReqs.del w.n } ∧
      o = outs ++ [.ext (.writeReply w.clientId w.requestId 1)] := by
  unfold stepWrite2Reply at h
  simp only [hk] at h
  peel h
  all_goals (cases h)
  all_goals (first
    | (left; refine ⟨?_, rfl⟩; simp_all [w2bump]; done)
    | (right
       rename_i hsg _ wt hwt _ s1 outs hif
       refine ⟨wt, s1, outs, hwt, ?_, rfl, rfl⟩
       rcases oite_some_iff.1 hif with ⟨hc, hif⟩ | ⟨hc, hif⟩
       · exact Or.inl ⟨by simp only [w2bump]; simp_all, hif⟩
       · cases hif; exact Or.inr ⟨rfl, rfl⟩))

/-- The `Write1Reply` handler on a record that never short-circuits. -/
theorem stepWrite1Reply_some {s s' : RState} {m : Write1ReplyM} {o : List Out} {w : WriteOp}
    (hk : s.wops.get? (shiftInts m.requestId m.clientId) = some w)
    (hv : w.maxValTag.v = -1) (ha : w.numWrite1Applies = 0) (hm : m.vt.v = -1)
    (h : stepWrite1Reply s m = .ok (s', o)) :
    ∃ w', s' = { s with wops := s.wops.put (shiftInts m.requestId m.clientId) w' } ∧
      w'.requestId = w.requestId ∧ w'.clientId = w.clientId ∧ w'.n = w.n ∧
      w'.numWrite2Applies = w.numWrite2Applies ∧ w'.maxValTag.v = -1 ∧ w'.numWrite1Applies = 0 ∧
      ((w'.sentWrite2Round = w.sentWrite2Round ∧ w'.writeTag = w.writeTag ∧ o = []) ∨
       (w.sentWrite2Round = false ∧ w'.sentWrite2Round = true ∧ ∃ wt, w'.writeTag = some wt ∧
        ∃ m2 : Write2ProxiedM, m2.requestId = w.requestId ∧ m2.clientId = w.clientId ∧
          m2.replicaId = s.id ∧ m2.vt.t = wt ∧
          o = [.send 0 (.write2 m2), .send 1 (.write2 m2), .send 2 (.write2 m2)])) := by
  unfold stepWrite1Reply at h
  have e1 : sge (-1 : w64) 0 = false := by decide
  have e2 : sge (0 : w64) (NHALF + 1) = false := by decide
  simp only [hk, hm, hv, ha, e1, e2, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h
  peel h
  all_goals (cases h)
  all_goals (first
    | exact ⟨_, rfl, rfl, rfl, rfl, rfl, by assumption, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
    | (rename_i hsent _ hmo
       refine ⟨_, rfl, rfl, rfl, rfl, rfl, by assumption, rfl, Or.inr ⟨by simpa using hsent, rfl, _,
         rfl, ?_⟩⟩
       simp [List.mapM_cons, sendTo, dstOf, sint.Z] at hmo
       subst hmo; exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩))

/-- A `Write1Reply` keeps the record's count of `Write2Reply`s. -/
theorem stepWrite1Reply_nw2r {s s' : RState} {m : Write1ReplyM} {o : List Out} {w : WriteOp}
    (hk : s.wops.get? (shiftInts m.requestId m.clientId) = some w)
    (hv : w.maxValTag.v = -1) (ha : w.numWrite1Applies = 0) (hm : m.vt.v = -1)
    (h : stepWrite1Reply s m = .ok (s', o)) {w' : WriteOp}
    (hw' : s'.wops.get? (shiftInts m.requestId m.clientId) = some w') :
    w'.numWrite2Replies = w.numWrite2Replies := by
  unfold stepWrite1Reply at h
  have e1 : sge (-1 : w64) 0 = false := by decide
  have e2 : sge (0 : w64) (NHALF + 1) = false := by decide
  simp only [hk, hm, hv, ha, e1, e2, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h
  peel h
  all_goals (cases h)
  all_goals (simp only [AMap.get?_put, if_true, Option.some.injEq] at hw'; subst hw'; rfl)

theorem stepClientWrite_spec' {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep}
    {o : List Out} (h : stepClientWrite s rid cid k v d = .ok (s', o)) :
    (cid, rid) ∉ s.used ∧ 0 ≤ sint.Z cid ∧ s.nReqs < 24 ∧
    s' = { s with
             nReqs := s.nReqs + 1, used := ((cid, rid) :: s.used), maxN := s.maxN + 1,
             wops := s.wops.put (shiftInts rid cid)
               { requestId := rid, clientId := cid, n := s.maxN + 1, writeValue := v, dep := d,
                 maxValTag := ⟨-1, model.tag0⟩, numWrite1Applies := 0, numWrite1Replies := 0,
                 numWrite2Applies := 0, numWrite2Replies := 0, sentWrite2Round := false,
                 writeTag := none },
             ongoingReqs := s.ongoingReqs.put (s.maxN + 1)
               { requestId := rid, clientId := cid, isRead := false, shortReads := [] } } ∧
    NoR o := by
  unfold stepClientWrite at h
  peel h
  cases h
  rename_i hg hn hu _ hm
  refine ⟨hu, ?_, by omega, rfl, ?_⟩
  · simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, sge, sle,
      decide_eq_true_eq] at hg
    exact hg.2
  · intro y hy; exact (mapM_sendTo_isR hm y hy).trans rfl

theorem forIn_exc_inv_mem {ε α β : Type} (l : List α) (b : β)
    (f : α → β → Except ε (ForInStep β))
    (P : β → Prop) (h0 : P b) (hf : ∀ a ∈ l, ∀ b st, P b → f a b = .ok st → P st.value) :
    ∀ r, forIn l b f = .ok r → P r := by
  induction l generalizing b with
  | nil => intro r h; cases h; exact h0
  | cons a l ih =>
    intro r h
    rw [List.forIn_cons] at h
    cases hfa : f a b with
    | error e => rw [hfa] at h; cases h
    | ok st =>
      have := hf a (by simp) b st h0 hfa
      rw [hfa] at h
      cases st with
      | done b' => cases h; exact this
      | yield b' => exact ih b' this (fun a ha => hf a (by simp [ha])) r h

/-- The new read's loop over the write records: entries keep their ids; only unsent writes'
entries gain the new read's number. -/
def LoopOK (W : model.AMap 64 WriteOp) (n : w32) (X0 X : model.AMap 32 OngoingOp) : Prop :=
  ∀ k, ((X.get? k).isSome = (X0.get? k).isSome) ∧ ∀ e, X.get? k = some e → ∃ e0,
    X0.get? k = some e0 ∧ e.requestId = e0.requestId ∧ e.clientId = e0.clientId ∧
    (e.shortReads = e0.shortReads ∨ ((∃ K w, (K, w) ∈ W ∧ w.sentWrite2Round = false ∧ w.n = k) ∧
      ∀ x ∈ e.shortReads, x ∈ e0.shortReads ∨ x = n))

theorem loopOK_refl {W : model.AMap 64 WriteOp} {n : w32} {X0 : model.AMap 32 OngoingOp} :
    LoopOK W n X0 X0 :=
  fun _ => ⟨rfl, fun e he => ⟨e, he, rfl, rfl, Or.inl rfl⟩⟩

theorem loopOK_put {W : model.AMap 64 WriteOp} {n k0 : w32} {X0 X : model.AMap 32 OngoingOp}
    {op : OngoingOp} (hL : LoopOK W n X0 X) (hop : X.get? k0 = some op)
    (hw : ∃ K w, (K, w) ∈ W ∧ w.sentWrite2Round = false ∧ w.n = k0) :
    LoopOK W n X0 (X.put k0 { op with shortReads := op.shortReads ++ [n] }) := by
  intro k
  rw [AMap.get?_put]
  split
  · rename_i hk
    subst hk
    refine ⟨by rw [← (hL k).1, hop]; rfl, fun e he => ?_⟩
    cases he
    obtain ⟨e0, he0, h1, h2, h3⟩ := (hL k).2 op hop
    refine ⟨e0, he0, h1, h2, Or.inr ⟨hw, fun x hx => ?_⟩⟩
    rcases List.mem_append.1 hx with hx | hx
    · rcases h3 with h3 | ⟨-, h3⟩
      · rw [← h3]; exact Or.inl hx
      · exact h3 x hx
    · exact Or.inr (List.mem_singleton.1 hx)
  · exact hL k

theorem stepClientRead_spec' {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) :
    (cid, rid) ∉ s.used ∧ 0 ≤ sint.Z cid ∧ s.nReqs < 24 ∧
    (∃ X, s' = { s with
                   nReqs := s.nReqs + 1, used := ((cid, rid) :: s.used), maxN := s.maxN + 1,
                   rops := s.rops.put (shiftInts rid cid) (freshRead rid cid (s.maxN + 1)),
                   ongoingReqs := X }) ∧
    LoopOK s.wops (s.maxN + 1) (s.ongoingReqs.put (s.maxN + 1)
      { requestId := rid, clientId := cid, isRead := true, shortReads := [] }) s'.ongoingReqs ∧
    ∀ x ∈ o, ∃ dd, x = .send dd (.read1 ⟨rid, cid, 0, dep0, s.id, s.storeVT⟩) ∧
      ∃ q, q ≠ s.id ∧ dstOf q = some dd := by
  unfold stepClientRead at h
  peel h
  cases h
  have hloop := ‹forIn _ _ _ = Except.ok s'›
  have hm := ‹List.mapM _ _ = some o›
  have hfr := ‹¬(cid, rid) ∈ s.used›
  have hn := ‹¬(!(_ && _ && _)) = true›
  have hu := ‹¬s.nReqs ≥ 24›
  have hP := forIn_exc_inv_mem _ _ _ (fun x : RState =>
    (∃ X, x = { s with
                  nReqs := s.nReqs + 1, used := ((cid, rid) :: s.used), maxN := s.maxN + 1,
                  rops := s.rops.put (shiftInts rid cid) (freshRead rid cid (s.maxN + 1)),
                  ongoingReqs := X }) ∧
    LoopOK s.wops (s.maxN + 1) (s.ongoingReqs.put (s.maxN + 1)
      { requestId := rid, clientId := cid, isRead := true, shortReads := [] }) x.ongoingReqs)
    ⟨⟨_, rfl⟩, loopOK_refl⟩ ?_ _ hloop
  · obtain ⟨⟨X, rfl⟩, hL⟩ := hP
    refine ⟨hfr, ?_, by omega, ⟨X, rfl⟩, hL, fun y hy => ?_⟩
    · simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, sge, sle,
        decide_eq_true_eq] at hn
      exact hn.2
    · obtain ⟨a, -, ha⟩ := mapM_some_mem hm y hy
      unfold sendPeer at ha
      split at ha
      · cases ha
      · rename_i hne
        obtain ⟨dd, hdd, rfl⟩ := sendTo_out ha
        exact ⟨dd, rfl, a, hne, hdd⟩
  · intro a ha b st hb hf
    obtain ⟨⟨X, rfl⟩, hL⟩ := hb
    peel hf
    all_goals (cases hf)
    · rename_i hns _ op hop
      refine ⟨⟨_, rfl⟩, loopOK_put hL hop ⟨a.1, a.2, ha, by simpa using hns, rfl⟩⟩
    · exact ⟨⟨_, rfl⟩, hL⟩

end Perennial.gryff.pure
