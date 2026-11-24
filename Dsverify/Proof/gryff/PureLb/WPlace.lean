/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/WPlace.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: **a write's place is its live record's `WriteTag`** (`WPInv`, `wpinv`): while write
`ow`'s record is live at its coordinator, `writePlace l ow` (the first state, after the request,
whose record has a `WriteTag`) is the record's `writeTag` (the tag is set once, with
`sentWrite2Round`, and a record is never re-created: keys are fresh); and an unsent record has no
`WriteTag`.
-/
module

public import Dsverify.Proof.gryff.PureLb.L1Read

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-! ## `firstFrom` -/

theorem firstFrom_succ {α : Type} (a n : Nat) (f : Nat → Option α) :
    firstFrom a (n + 1) f = (firstFrom a n f).or (if a ≤ n then f n else none) := by
  unfold firstFrom
  rw [List.range_succ, List.filter_append, List.findSome?_append]
  congr 1
  by_cases h : a ≤ n <;> simp [h]

theorem firstFrom_congr {α : Type} {a n : Nat} {f g : Nat → Option α}
    (h : ∀ j < n, f j = g j) : firstFrom a n f = firstFrom a n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [firstFrom_succ, firstFrom_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

theorem firstFrom_self {α : Type} (a : Nat) (f : Nat → Option α) : firstFrom a a f = none := by
  unfold firstFrom
  rw [List.findSome?_eq_none_iff]
  intro j hj
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
  omega

theorem firstFrom_mono {α : Type} {a n : Nat} {f g : Nat → Option α} {t : α}
    (h : ∀ j < n, f j = g j) (hf : firstFrom a n f = some t) (k : Nat) :
    firstFrom a (n + k) g = some t := by
  induction k with
  | zero => rw [Nat.add_zero, ← firstFrom_congr h]; exact hf
  | succ k ih => rw [← Nat.add_assoc, firstFrom_succ, ih]; rfl

/-! ## `writePlace` along a run -/

theorem writePlace_snoc (l : List Label) (i : Fin 3) (e : Ev) {ow : Op}
    (hj : ow.j ≤ (projR l ow.r).length) :
    writePlace (l ++ [(i, e)]) ow = if i = ow.r then (writePlace l ow).or
      ((stOf ow.r (projR l ow.r ++ [e])).wops.get? ow.key >>= WriteOp.writeTag)
      else writePlace l ow := by
  unfold writePlace
  simp only [proj_snoc]
  split
  · rw [List.length_append, List.length_singleton, firstFrom_succ, if_pos hj]
    congr 1
    · apply firstFrom_congr; intro j hj'
      rw [List.take_append_of_le_length (by omega)]
    · rw [List.take_of_length_le (by simp)]; rfl
  · rfl

theorem writePlace_append {l l' : List Label} {o : Op} {t : model.Tag}
    (h : writePlace l o = some t) : writePlace (l ++ l') o = some t := by
  unfold writePlace at h ⊢
  simp only [proj_append, List.length_append]
  exact firstFrom_mono (fun j hj => by rw [List.take_append_of_le_length (by omega)]) h _

/-- The ops after a step: the old ones, or the step's new one. -/
theorem mem_ops_snoc' {l : List Label} {i : Fin 3} {e : Ev} {o : Op} (h : o ∈ ops (l ++ [(i, e)])) :
    o ∈ ops l ∨ (o.g = l.length ∧ o.r = i ∧ o.j = (projR l i).length ∧
      e.clientReq = some (o.cid, o.rid, o.inp)) := by
  rw [ops_snoc, opAt_snoc_new, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    cases hc : e.clientReq with
    | none => rw [hc] at h; cases h
    | some x =>
      rw [hc] at h
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at h
      subst h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem op_j_le {l : List Label} {o : Op} (ho : o ∈ ops l) : o.j ≤ (projR l o.r).length := by
  rw [op_j ho]
  have := proj_take_len_mono l o.r (ops_g_le ho)
  have hl : l.take l.length = l := List.take_length
  rwa [hl] at this

/-! ## The invariant -/

/-- **A write's place is its live record's `WriteTag`**; an unsent record has none. -/
def WPInv (l : List Label) (c : Cfg gNet) : Prop :=
  ∀ ow ∈ ops l, ∀ v, ow.inp = .write v → ∀ w, (stR c ow.r).wops.get? ow.key = some w →
    writePlace l ow = w.writeTag ∧ (w.sentWrite2Round = false → w.writeTag = none)

theorem wpinv_init : WPInv [] (Cfg.init gNet) := by
  intro ow ho; simp [ops_eq] at ho

/-- How a step changes the record at a key: kept (tag and round flag), the `Write2`s sent, or
created (fresh). -/
def WTr (pre : Option WriteOp) (w' : WriteOp) (fresh : Prop) : Prop :=
  (∃ w, pre = some w ∧ w'.writeTag = w.writeTag ∧ w'.sentWrite2Round = w.sentWrite2Round) ∨
  (∃ w, pre = some w ∧ w.sentWrite2Round = false ∧ w'.sentWrite2Round = true) ∨
  (fresh ∧ w'.writeTag = none ∧ w'.sentWrite2Round = false)

theorem or_self' {α : Type} (x : Option α) : x.or x = x := by cases x <;> rfl

/-- The record of `ow` after a step at `ow.r`. -/
theorem wp_tr {l : List Label} {c : Cfg gNet} {ow : Op} {s' : RState} {e : Ev} {w' : WriteOp}
    (hI : ∀ w, (stR c ow.r).wops.get? ow.key = some w →
      writePlace l ow = w.writeTag ∧ (w.sentWrite2Round = false → w.writeTag = none))
    (hj : ow.j ≤ (projR l ow.r).length)
    (hs' : stOf ow.r (projR l ow.r ++ [e]) = s')
    (hw' : s'.wops.get? ow.key = some w')
    (htr : WTr ((stR c ow.r).wops.get? ow.key) w' (writePlace l ow = none)) :
    writePlace (l ++ [(ow.r, e)]) ow = w'.writeTag ∧
      (w'.sentWrite2Round = false → w'.writeTag = none) := by
  rw [writePlace_snoc l ow.r e hj, if_pos rfl, hs', hw']
  change (writePlace l ow).or w'.writeTag = _ ∧ _
  rcases htr with ⟨w, hpre, ht, hsr⟩ | ⟨w, hpre, hsr, hsr'⟩ | ⟨hf, ht, hsr⟩
  · obtain ⟨a, b⟩ := hI w hpre
    rw [a, ht, or_self']
    exact ⟨rfl, fun h => by rw [hsr] at h; exact b h⟩
  · obtain ⟨a, b⟩ := hI w hpre
    rw [a, b hsr]
    exact ⟨rfl, fun h => by rw [hsr'] at h; cases h⟩
  · rw [hf, ht]; exact ⟨rfl, fun _ => rfl⟩

/-- The step. -/
theorem wpinv_step {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {x : List Ext}
    (h : GRun (Cfg.init gNet) l c) (hi : WPInv l c) (hst : GStep c i e c' x) :
    WPInv (l ++ [(i, e)]) c' := by
  obtain ⟨s', o, hs⟩ := StepAt.of h hst
  have h' := grun_snoc h hst
  have hW := winv h
  obtain ⟨hM, hR, -⟩ := rinv h
  have hs'i : stOf i (projR l i ++ [e]) = s' := by
    have := cutSt_len h' i
    unfold cutSt at this
    rw [List.take_length, proj_snoc, if_pos rfl] at this
    rw [this]; exact hs.sti
  intro ow how v hv w' hw'
  by_cases hR : ow.r = i
  · subst hR
    rw [hs.sti] at hw'
    -- the new op, if any
    have hnew : ow.j = (projR l ow.r).length → writePlace l ow = none := by
      intro hj; unfold writePlace; simp only; rw [← hj]; exact firstFrom_self _ _
    have hj : ow.j ≤ (projR l ow.r).length := by
      rcases mem_ops_snoc' how with how | how
      · exact op_j_le how
      · rw [how.2.2.1]; exact Nat.le_refl _
    have hI : ∀ w, (stR c ow.r).wops.get? ow.key = some w →
        writePlace l ow = w.writeTag ∧ (w.sentWrite2Round = false → w.writeTag = none) := by
      intro w hw
      rcases mem_ops_snoc' how with how | how
      · exact hi ow how v hv w hw
      · -- a new write's key is fresh
        exfalso
        obtain ⟨-, -, -, hcr⟩ := how
        cases e with
        | write rid cid k v' d =>
          simp only [Ev.clientReq, Option.some.injEq, Prod.mk.injEq] at hcr
          obtain ⟨hc, hr', -⟩ := hcr
          obtain ⟨hu0, hcid, -⟩ := stepClientWrite_spec' hs.ok
          obtain ⟨hK, -, ⟨e1, he1, he1a, he1b⟩, -⟩ := hR.wops _ _ w (AMap.mem_of_get? hw)
          have hu := (hR.ongoing _ _ e1 he1).2.2.2
          have hk : shiftInts w.requestId w.clientId = shiftInts rid cid := by
            rw [← hK]; unfold Op.key; rw [hc, hr']
          obtain ⟨a, b⟩ := shiftInts_inj (by rw [← he1b]; exact hu.2) hcid hk
          rw [he1a, he1b, a, b] at hu; exact hu0 hu.1
        | read => simp [Ev.clientReq] at hcr; rw [hv] at hcr; cases hcr.2.2
        | rmw => simp [Ev.clientReq] at hcr; rw [hv] at hcr; cases hcr.2.2
        | _ => cases hcr
    refine wp_tr hI hj hs'i hw' ?_
    -- the transition, by event
    cases e with
    | write rid cid k v' d =>
      obtain ⟨hu0, hcid, -, hs'e, -⟩ := stepClientWrite_spec' hs.ok
      rw [hs'e] at hw'
      change ((stR c ow.r).wops.put _ _).get? _ = _ at hw'
      rw [AMap.get?_put] at hw'
      split at hw'
      · rename_i hk
        cases hw'
        refine Or.inr (Or.inr ⟨?_, rfl, rfl⟩)
        rcases mem_ops_snoc' how with how' | how'
        · exfalso
          have hu := hW.1.ops ow how'
          obtain ⟨a, b⟩ := shiftInts_inj hu.2 hcid hk
          rw [a, b] at hu; exact hu0 hu.1
        · exact hnew how'.2.2.1
      · exact Or.inl ⟨w', hw', rfl, rfl⟩
    | read rid cid k d =>
      have := (stepClientRead_spec hs.ok).2.2.2.2.1
      rw [this] at hw'; exact Or.inl ⟨w', hw', rfl, rfl⟩
    | rmw rid cid k d a b =>
      have := (stepClientRMW_spec hs.ok).2.2.2.2.1
      rw [this] at hw'; exact Or.inl ⟨w', hw', rfl, rfl⟩
    | msg m =>
      cases m with
      | write1Reply m =>
        obtain ⟨-, -, -, hK1, hK2, -⟩ := stepWrite1Reply_spec hs.ok
        by_cases hk : ow.key = shiftInts m.requestId m.clientId
        · cases hpre : (stR c ow.r).wops.get? ow.key with
          | none => rw [hk] at hpre hw'; rw [hK2 hpre] at hw'; cases hw'
          | some w =>
            rw [hk] at hpre hw'
            obtain ⟨-, -, -, hwv, hwa⟩ := hR.wops _ _ w (AMap.mem_of_get? hpre)
            have hmv : m.vt.v = -1 := hM _ _ (hs.recv _ rfl)
            obtain ⟨w'', rfl, -, -, -, -, -, -, hbr⟩ := stepWrite1Reply_some hpre hwv hwa hmv hs.ok
            change ((stR c ow.r).wops.put _ _).get? _ = _ at hw'
            rw [AMap.get?_put, if_pos rfl] at hw'
            cases hw'
            rcases hbr with ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩
            · exact Or.inl ⟨w, rfl, e2, e1⟩
            · exact Or.inr (Or.inl ⟨w, rfl, e1, e2⟩)
        · rw [hK1 _ hk] at hw'; exact Or.inl ⟨w', hw', rfl, rfl⟩
      | write2Reply m =>
        obtain ⟨-, -, -, hK1, hK2, -⟩ := stepWrite2Reply_spec hs.ok
        by_cases hk : ow.key = shiftInts m.requestId m.clientId
        · cases hpre : (stR c ow.r).wops.get? ow.key with
          | none => rw [hk] at hpre hw'; rw [hK2 hpre] at hw'; cases hw'
          | some w =>
            rw [hk] at hpre hw'
            rcases stepWrite2Reply_some hpre hs.ok with ⟨rfl, -⟩ | ⟨wt, s1, outs, -, -, rfl, -⟩
            · change ((stR c ow.r).wops.put _ _).get? _ = _ at hw'
              rw [AMap.get?_put, if_pos rfl] at hw'
              cases hw'
              exact Or.inl ⟨w, rfl, rfl, rfl⟩
            · change (s1.wops.del _).get? _ = _ at hw'
              rw [AMap.get?_del, if_pos rfl] at hw'; cases hw'
        · rw [hK1 _ hk] at hw'; exact Or.inl ⟨w', hw', rfl, rfl⟩
      | write1 m =>
        have := (stepWrite1_spec hs.ok).1.1
        rw [this] at hw'; exact Or.inl ⟨w', hw', rfl, rfl⟩
      | _ =>
        have := (step_fw_other hs.ok rfl).1.1
        rw [this] at hw'; exact Or.inl ⟨w', hw', rfl, rfl⟩
    | _ =>
      have := (step_fw_other hs.ok rfl).1.1
      rw [this] at hw'; exact Or.inl ⟨w', hw', rfl, rfl⟩
  · -- another replica's step
    have how' : ow ∈ ops l := by
      rcases mem_ops_snoc' how with how | how
      · exact how
      · exact absurd how.2.1 hR
    rw [hs.stj hR] at hw'
    rw [writePlace_snoc l i e (op_j_le how'), if_neg (Ne.symm hR)]
    exact hi ow how' v hv w' hw'

/-- **A write's place is its live record's `WriteTag`**, along every run. -/
theorem wpinv {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) : WPInv l c :=
  grun_inv WPInv wpinv_init (fun _ _ _ _ _ _ h hi hs => wpinv_step h hi hs) l c h

end Perennial.gryff.pure
