/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/WSrc.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: write records over a replica's projection, for L3's write source: a record's fields
come from the client write that created it (`wrec_origin`), and a record's `WriteTag`, once set,
stays set while the record lives (`wtag_persist`).
-/
module

public import Dsverify.Proof.gryff.PureLc.Vals
public import Dsverify.Proof.gryff.PureLb.RInv

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

/-- The identity fields of a write record. -/
abbrev WId (w w' : WriteOp) : Prop :=
  w'.requestId = w.requestId ∧ w'.clientId = w.clientId ∧ w'.writeValue = w.writeValue

theorem stepWrite1Reply_wid {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) : ∀ K w', s'.wops.get? K = some w' →
      ∃ w, s.wops.get? K = some w ∧ WId w w' := by
  intro K w' hK
  unfold stepWrite1Reply at h
  peel h
  all_goals (cases h)
  all_goals (try (have hsc := (shortCircuit_fw ‹shortCircuit _ _ _ _ = some _›).1.1))
  all_goals (by_cases hk : K = shiftInts m.requestId m.clientId)
  all_goals (first
    | (refine ⟨w', ?_, rfl, rfl, rfl⟩; exact hK)
    | (subst hk; simp [AMap.get?_del] at hK; done)
    | (subst hk; rw [AMap.get?_put] at hK; split at hK
       · cases hK; refine ⟨_, ‹s.wops.get? _ = some _›, ?_⟩; exact ⟨rfl, rfl, rfl⟩
       · rename_i hne; exact absurd rfl hne)
    | (simp only [AMap.get?_del, AMap.get?_put, if_neg hk] at hK
       try rw [hsc] at hK
       refine ⟨w', ?_, rfl, rfl, rfl⟩; exact hK)
)

theorem stepWrite2Reply_wid {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) : ∀ K w', s'.wops.get? K = some w' →
      ∃ w, s.wops.get? K = some w ∧ WId w w' ∧ w'.writeTag = w.writeTag := by
  intro K w' hK
  unfold stepWrite2Reply at h
  peel h
  all_goals (cases h)
  all_goals (try (have hsc := (shortCircuit_ite_fw ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›).1.1))
  all_goals (by_cases hk : K = shiftInts m.requestId m.clientId)
  all_goals (first
    | (refine ⟨w', ?_, ⟨rfl, rfl, rfl⟩, rfl⟩; exact hK)
    | (subst hk; simp [AMap.get?_del] at hK; done)
    | (subst hk; rw [AMap.get?_put] at hK; split at hK
       · cases hK; refine ⟨_, ‹s.wops.get? _ = some _›, ?_⟩; exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
       · rename_i hne; exact absurd rfl hne)
    | (simp only [AMap.get?_del, AMap.get?_put, if_neg hk] at hK
       try rw [hsc] at hK
       refine ⟨w', ?_, ⟨rfl, rfl, rfl⟩, rfl⟩; exact hK))

/-- A step's effect on the write records: unchanged, or (client write) one new record, or
(`Write1Reply`/`Write2Reply`) each record kept with its identity, `WriteTag` kept or set. -/
theorem step_wrec {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) : ∀ K w', s'.wops.get? K = some w' →
      (∃ w, s.wops.get? K = some w ∧ WId w w' ∧ (w.writeTag.isSome → w'.writeTag.isSome)) ∨
      (∃ rid cid k v d, e = .write rid cid k v d ∧ K = shiftInts rid cid ∧ w'.requestId = rid ∧
        w'.clientId = cid ∧ w'.writeValue = v ∧ w'.writeTag = none) := by
  intro K w' hK
  have of_eq : s'.wops = s.wops → (∃ w, s.wops.get? K = some w ∧ WId w w' ∧
      (w.writeTag.isSome → w'.writeTag.isSome)) := fun he => by
    rw [he] at hK; exact ⟨w', hK, ⟨rfl, rfl, rfl⟩, id⟩
  cases e with
  | read => exact Or.inl (of_eq (stepClientRead_spec h).2.2.2.2.1)
  | rmw => exact Or.inl (of_eq (stepClientRMW_spec h).2.2.2.2.1)
  | write rid cid k v d =>
    have h' := h
    change stepClientWrite s rid cid k v d = _ at h'
    unfold stepClientWrite at h'
    peel h'
    cases h'
    simp only [AMap.get?_put] at hK
    split at hK
    · cases hK; rename_i hk; exact Or.inr ⟨rid, cid, k, v, d, rfl, hk, rfl, rfl, rfl, rfl⟩
    · exact Or.inl ⟨w', hK, ⟨rfl, rfl, rfl⟩, id⟩
  | msg m =>
    cases m with
    | write1 => exact Or.inl (of_eq (stepWrite1_spec h).1.1)
    | write1Reply m =>
      obtain ⟨w, hw, hid⟩ := stepWrite1Reply_wid h K w' hK
      refine Or.inl ⟨w, hw, hid, fun hs => ?_⟩
      rcases stepWrite1Reply_wt h K w' hK with ⟨w0, hw0, e⟩ | ⟨-, ts, e⟩
      · rw [hw] at hw0; cases hw0; rw [e]; exact hs
      · rw [e]; rfl
    | write2Reply m =>
      obtain ⟨w, hw, hid, e⟩ := stepWrite2Reply_wid h K w' hK
      exact Or.inl ⟨w, hw, hid, fun hs => e ▸ hs⟩
    | _ => exact Or.inl (of_eq (step_fw_other h rfl).1.1)
  | _ => exact Or.inl (of_eq (step_fw_other h rfl).1.1)

section
variable {L : List Label} {cL : Cfg gNet} (hL : GRun (Cfg.init gNet) L cL) (r : Fin 3)
include hL

/-- **A record's fields come from the client write that created it.** -/
theorem wrec_origin (j : Nat) (hj : j ≤ (projR L r).length) :
    ∀ K w, (stOf r ((projR L r).take j)).wops.get? K = some w →
      K = shiftInts w.requestId w.clientId ∧ ∃ j' < j, ∃ k d,
        (projR L r)[j']? = some (.write w.requestId w.clientId k w.writeValue d) := by
  refine proj_ind hL r (fun j s => ∀ K w, s.wops.get? K = some w →
      K = shiftInts w.requestId w.clientId ∧ ∃ j' < j, ∃ k d,
        (projR L r)[j']? = some (.write w.requestId w.clientId k w.writeValue d)) ?_ ?_ j hj
  · intro K w h; simp [stOf, runP, runFrom, gNet, RState.init, AMap.get?] at h
  · intro j e s' o he hs ih K w' hK
    rcases step_wrec hs K w' hK with ⟨w, hw, ⟨e1, e2, e3⟩, -⟩ | ⟨rid, cid, k, v, d, rfl, hk, e1, e2, e3, -⟩
    · obtain ⟨hk, j', hj', k, d, hj''⟩ := ih K w hw
      rw [e1, e2, e3]
      exact ⟨hk, j', by omega, k, d, hj''⟩
    · rw [e1, e2, e3]
      exact ⟨hk, j, by omega, k, d, he⟩

/-- **A set `WriteTag` stays set while the record lives** (no client write with its key). -/
theorem wtag_persist {K : w64} {j : Nat}
    (hset : ∀ w, (stOf r ((projR L r).take j)).wops.get? K = some w → w.writeTag.isSome) :
    ∀ d, j + d ≤ (projR L r).length →
      (∀ z, j ≤ z → z < j + d → ∀ rid cid k v dd,
        (projR L r)[z]? = some (.write rid cid k v dd) → K ≠ shiftInts rid cid) →
      ∀ w, (stOf r ((projR L r).take (j + d))).wops.get? K = some w → w.writeTag.isSome := by
  intro d
  induction d with
  | zero => intro _ _; exact hset
  | succ d ih =>
    intro hd hno w' hK
    have hlt : j + d < (projR L r).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (projR L r)[j + d]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨n, s', o, -, -, hs, hs2, -⟩ := proj_step hL he
    rw [← Nat.add_assoc, hs2] at hK
    rcases step_wrec hs K w' hK with ⟨w, hw, -, hsome⟩ | ⟨rid, cid, k, v, dd, rfl, hk, -⟩
    · exact hsome (ih (by omega) (fun z h1 h2 => hno z h1 (by omega)) w hw)
    · exact absurd hk (hno (j + d) (by omega) (by omega) rid cid k v dd he)

end

/-- The first `some` of `f` from `a`. -/
theorem firstFrom_eq {α : Type} {a b n : Nat} {f : Nat → Option α} {x : α} (hab : a ≤ b)
    (hbn : b < n) (hb : f b = some x) (hbefore : ∀ c, a ≤ c → c < b → f c = none) :
    firstFrom a n f = some x := by
  unfold firstFrom
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.findSome?_append]
    by_cases hlt : b < n
    · rw [ih hlt]; rfl
    · have hbn' : b = n := by omega
      subst hbn'
      have hnone : ((List.range b).filter (a ≤ ·)).findSome? f = none := by
        rw [List.findSome?_eq_none_iff]
        intro c hc
        obtain ⟨hc1, hc2⟩ := List.mem_filter.1 hc
        exact hbefore c (by simpa using hc2) (List.mem_range.1 hc1)
      rw [hnone]
      simp [hab, hb]

end Perennial.gryff.pure
