/-
The register's porcupine model, pure (notes/dsv-hraft.md, S5e), as craq's `craqnet/ModelSet.lean`.

* **The store** `regB` (`Kit.lean`): linkv's pending-writes store of the register (`service.Reg`), on the
  kit's inputs `HIn` (a put of a value, or a read in a way; a put of unknown outcome is pending: it may
  take effect later, once, or never).
* **The Go model's state** `(a, P)` (kit.go's `State{Present, V, Pend}`: the register, the values of
  the writes pending, `P.map pendV`) does not determine the set of configurations the history reached
  (a pending write may have taken effect before a later write overwrote it, or not), so the kit's
  `Equal` is always false and the state only **brackets** the set (`Sim a P S`): it holds every
  configuration reachable from `⟨a, P⟩` (`Funl`) and only configurations reachable from `a` with
  pending writes whose values are some of `P`'s (`Fall`; values, not inputs: Go keeps a write's value
  only, and two writes of one value in different ways have the same effect).
* **The simulation** `sim_step`: from a bracketed set, the model's step on `(i, o)` is defined exactly
  when the Go step (`goStep`, kit.go's `step` on the decoded answer) allows it, and the next set is
  bracketed by the Go step's next state. The lemmas: `reach_cons` (a pending input that never fires),
  `reach_sub` (late effects only remove pending inputs), `reach_val` (the register after late effects:
  its value before, or a pending write's, which can be taken to have fired first).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Kit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove EtcdGrove.linkv

section pure
variable [GooseExts]

/-! ## The store -/

/-- `HIn`'s `BEq` is its decidable equality's (the instance linkv's pending lists erase with). -/
@[reducible] instance (priority := high) HIn.beq : BEq HIn := instBEqOfDecidableEq

/-- A configuration of the store. -/
abbrev Cfg := PCfg service.Reg HIn

/-- An input's value (a write's: what Go keeps of a pending write). -/
def pendV (i : HIn) : GoString := i.1.2.2

/-- A bounded string: shorter than 256 bytes (the codec writes a string's length in one byte). -/
abbrev Str8 := {s : GoString // s.length < 256}

/-- The register holds a short value, if any. -/
def RegOk (a : service.Reg) : Prop := ∀ v, a = some v → v.length < 256

theorem val_short (i : HIn) : (pendV i).length < 256 := i.2.2

theorem regOk_some (i : HIn) : RegOk (some (pendV i)) := by
  intro v h; cases h; exact val_short i

theorem step_put (i : HIn) (h : i.1.1 = true) (st : service.Reg) :
    regB.step i st = (some (pendV i), bndO (false, [])) := by
  simp [regB, h, pendV]

theorem step_get (i : HIn) (h : i.1.1 = false) (st : service.Reg) :
    regB.step i st = (st, bndO (regOut st)) := by
  simp [regB, h]

theorem bndO_got (v : GoString) (hv : v.length < 256) :
    bndO (regOut (some v)) = ⟨(true, v), hv⟩ := bndO_of (o := (true, v)) hv

theorem bndO_none : bndO (regOut none) = ⟨(false, []), by simp⟩ :=
  bndO_of (o := (false, [])) (by simp)

/-! ## Late effects -/

/-- A pending input that never fires rides along. -/
theorem reach_cons (i : HIn) {c c' : Cfg} (h : PReach regB c c') :
    PReach regB ⟨c.st, i :: c.pend⟩ ⟨c'.st, i :: c'.pend⟩ := by
  induction h with
  | refl c => exact .refl _
  | @step c c₁ c₂ hs _ ih =>
    refine PReach.trans ?_ ih
    cases hs with
    | apply j hj =>
      refine .step (.apply ⟨c.st, i :: c.pend⟩ j (List.mem_cons_of_mem _ hj)) (.single (.perm _ _ ?_))
      by_cases hij : i = j
      · subst hij
        simp only [List.erase_cons_head]
        exact (List.perm_cons_erase hj).symm
      · rw [List.erase_cons_tail (by simpa using hij)]
    | perm p hp => exact .single (.perm _ _ (hp.cons i))

/-- Late effects only remove pending inputs. -/
theorem reach_sub {c c' : Cfg} (h : PReach regB c c') : c'.pend.Subperm c.pend := by
  induction h with
  | refl c => exact List.Subperm.refl _
  | @step c c₁ c₂ hs _ ih =>
    cases hs with
    | apply j hj => exact ih.trans (List.erase_sublist ..).subperm
    | perm p hp => exact ih.trans hp.subperm

/-- **The register after late effects**: its value before, or the value of a pending write, which
may be taken to have fired first (the ones before it are overwritten). -/
theorem reach_val {c c' : Cfg} (h : PReach regB c c') :
    c'.st = c.st ∨ ∃ i ∈ c.pend, c'.st = some (pendV i) ∧
      ∃ Q, Q.Subperm (c.pend.erase i) ∧ PReach regB ⟨some (pendV i), Q⟩ c' := by
  induction h with
  | refl c => exact .inl rfl
  | @step c c₁ c₂ hs hr ih =>
    cases hs with
    | apply j hj =>
      rcases ih with h1 | ⟨i, him, hx, Q, hQ, hr'⟩
      · cases hjp : j.1.1
        · exact .inl (by simpa [step_get j hjp] using h1)
        · refine .inr ⟨j, hj, by simpa [step_put j hjp] using h1, _, List.Subperm.refl _, ?_⟩
          simpa [step_put j hjp] using hr
      · refine .inr ⟨i, List.mem_of_mem_erase him, hx, Q, ?_, hr'⟩
        rw [List.erase_comm] at hQ
        exact hQ.trans (List.erase_sublist ..).subperm
    | perm p hp =>
      rcases ih with h1 | ⟨i, him, hx, Q, hQ, hr'⟩
      · exact .inl h1
      · exact .inr ⟨i, hp.mem_iff.1 him, hx, Q, hQ.trans (hp.erase i).subperm, hr'⟩

/-- A list's values without one of its elements: its values without that element's (up to order). -/
theorem map_erase_perm {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β)
    {l : List α} {x : α} (h : x ∈ l) : ((l.erase x).map f).Perm ((l.map f).erase (f x)) := by
  have h1 : (l.map f).Perm (f x :: (l.erase x).map f) := by
    simpa using (List.perm_cons_erase h).map f
  have h2 : (l.map f).Perm (f x :: (l.map f).erase (f x)) :=
    List.perm_cons_erase (List.mem_map.2 ⟨x, h, rfl⟩)
  exact (h1.symm.trans h2).cons_inv

theorem subperm_map {α β : Type} (f : α → β) {l₁ l₂ : List α} (h : l₁.Subperm l₂) :
    (l₁.map f).Subperm (l₂.map f) := by
  obtain ⟨l, hp, hs⟩ := h
  exact ⟨l.map f, hp.map f, hs.map f⟩

/-! ## The bracket -/

/-- The configurations reachable from `⟨a, P⟩`. -/
def Funl (a : service.Reg) (P : List HIn) : PSet service.Reg HIn := fun c => PReach regB ⟨a, P⟩ c

/-- The configurations reachable from `a` with pending inputs whose values are some of `P`'s. -/
def Fall (a : service.Reg) (P : List HIn) : PSet service.Reg HIn :=
  fun c => ∃ Q : List HIn, (Q.map pendV).Subperm (P.map pendV) ∧ PReach regB ⟨a, Q⟩ c

/-- **The Go state `(a, P)` brackets the model's set `S`.** -/
def Sim (a : service.Reg) (P : List HIn) (S : PSet service.Reg HIn) : Prop :=
  (∀ c, Funl a P c → S c) ∧ (∀ c, S c → Fall a P c)

theorem Fall_reach {a : service.Reg} {P : List HIn} {c c' : Cfg} (h : Fall a P c)
    (hr : PReach regB c c') : Fall a P c' := by
  obtain ⟨Q, hQ, h⟩ := h
  exact ⟨Q, hQ, h.trans hr⟩

theorem sim_init : Sim regB.init [] (pInit regB) := by
  constructor
  · intro c h
    show c = ⟨regB.init, []⟩
    suffices ∀ c₀ c', PReach regB c₀ c' → c₀.pend = [] → c' = c₀ from
      (this _ _ h rfl)
    intro c₀ c' hr
    induction hr with
    | refl => intro _; rfl
    | @step c c₁ c₂ hs _ ih =>
      intro hp
      cases hs with
      | apply j hj => simp [hp] at hj
      | perm p hq =>
        rw [hp] at hq
        have := hq.eq_nil
        subst this
        rw [ih rfl, ← hp]
  · intro c h
    rw [show c = ⟨regB.init, []⟩ from h]
    exact ⟨[], List.Subperm.refl _, .refl _⟩

/-! ## The Go step -/

/-- kit.go's `step` on the decoded answer: its verdict and next state (`none`: it refuses). -/
def goStep (a : service.Reg) (P : List HIn) (i : HIn) : Ans HOut → Option (service.Reg × List HIn)
  | .err => if i.1.1 then some (a, P ++ [i]) else some (a, P)
  | .ok o =>
    if i.1.1 then (if o.1 = (false, []) then some (some (pendV i), P) else none)
    else if o.1.1 = false then (if o.1.2 = [] ∧ a = none then some (a, P) else none)
    else if a = some o.1.2 then some (a, P)
    else match P.find? (fun j => decide (pendV j = o.1.2)) with
      | some j => some (some o.1.2, P.erase j)
      | none => none

theorem pstep_inv {c c₁ : Cfg} {i : HIn} {o : Ans HOut} (h : PStep regB c i o c₁) :
    (o = .ok (regB.step i c.st).2 ∧ c₁ = ⟨(regB.step i c.st).1, c.pend⟩) ∨
    (o = .err ∧ i.1.1 = true ∧ c₁ = ⟨c.st, i :: c.pend⟩) ∨
    (o = .err ∧ i.1.1 = false ∧ c₁ = c) := by
  cases h with
  | ok => exact .inl ⟨rfl, rfl⟩
  | errW hw _ => exact .inr (.inl ⟨rfl, hw, rfl⟩)
  | errR hw _ => exact .inr (.inr ⟨rfl, hw, rfl⟩)
  | obs _ hob _ => exact absurd hob (by simp [regB])

theorem pstep_ok (c : Cfg) (i : HIn) : PStep regB c i (.ok (regB.step i c.st).2)
    ⟨(regB.step i c.st).1, c.pend⟩ := PStep.ok (P := regB) c i rfl

/-- A configuration's register in `Fall a P` after a read of it answered `o`: `o` is `a`'s value
(`a` holding one), or a value of `P`, which may be taken to have fired first. -/
theorem fall_read {a : service.Reg} {P : List HIn} (ha : RegOk a) {c : Cfg} (hF : Fall a P c) :
    (c.st = a) ∨ ∃ i, pendV i ∈ P.map pendV ∧ c.st = some (pendV i) ∧
      ∃ Q, (Q.map pendV).Subperm ((P.map pendV).erase (pendV i)) ∧ PReach regB ⟨some (pendV i), Q⟩ c := by
  obtain ⟨Q, hQ, hq⟩ := hF
  rcases reach_val hq with h1 | ⟨i, him, hx, Q₂, hQ₂, hr⟩
  · exact .inl h1
  · refine .inr ⟨i, hQ.subset (List.mem_map.2 ⟨i, him, rfl⟩), hx, Q₂, ?_, hr⟩
    exact (subperm_map pendV hQ₂).trans ((map_erase_perm pendV him).subperm.trans (hQ.erase _))

theorem regOut_short {st : service.Reg} (h : RegOk st) :
    ∃ o : HOut, bndO (regOut st) = o ∧ o.1 = regOut st := by
  cases st with
  | none => exact ⟨_, bndO_none, rfl⟩
  | some v => exact ⟨_, bndO_got v (h v rfl), rfl⟩

theorem find_some {P : List HIn} {w : GoString} {j : HIn}
    (h : P.find? (fun j => decide (pendV j = w)) = some j) : j ∈ P ∧ pendV j = w := by
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [decide_eq_true_eq] at h2
  exact ⟨h1, h2⟩

theorem find_none {P : List HIn} {w : GoString}
    (h : P.find? (fun j => decide (pendV j = w)) = none) : w ∉ P.map pendV := by
  intro hm
  obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
  have := List.find?_eq_none.1 h x hx
  simp [e] at this

/-- The model's next set, when the Go step allows the operation: nonempty and bracketed. -/
theorem sim_some {a : service.Reg} {P : List HIn} {S : PSet service.Reg HIn} (hS : Sim a P S)
    (hP : ∀ x ∈ P, x.1.1 = true) (ha : RegOk a) {i : HIn} {o : Ans HOut} {a' : service.Reg}
    {P' : List HIn} (hg : goStep a P i o = some (a', P')) :
    (∃ c, ppost regB S i o c) ∧ Sim a' P' (ppost regB S i o) := by
  have hbase : S ⟨a, P⟩ := hS.1 _ (.refl _)
  have hF : ∀ c₀ c, S c₀ → PReach regB c₀ c → Fall a P c := fun c₀ c h hr =>
    Fall_reach (hS.2 _ h) hr
  suffices hlow : (∀ c, Funl a' P' c → ppost regB S i o c) ∧
      (∀ c, ppost regB S i o c → Fall a' P' c) by
    exact ⟨⟨_, hlow.1 _ (.refl _)⟩, hlow⟩
  cases o with
  | err =>
    unfold goStep at hg
    cases hp : i.1.1
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      constructor
      · intro c h
        exact ⟨⟨a, P⟩, ⟨a, P⟩, ⟨a, P⟩, hbase, .refl _, .errR _ _ hp rfl, h⟩
      · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
        rcases pstep_inv hs with ⟨he, _⟩ | ⟨_, hw, _⟩ | ⟨_, _, rfl⟩
        · cases he
        · rw [hp] at hw; cases hw
        · exact Fall_reach (hF _ _ h0 hr) hr'
    · simp only [hp, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      constructor
      · intro c h
        exact ⟨⟨a, P⟩, ⟨a, P⟩, ⟨a, i :: P⟩, hbase, .refl _, .errW _ _ hp rfl,
          .step (.perm _ _ (List.perm_append_singleton _ _)) h⟩
      · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
        obtain ⟨Q, hQ, hq⟩ := hF _ _ h0 hr
        rcases pstep_inv hs with ⟨he, _⟩ | ⟨_, _, rfl⟩ | ⟨_, hw, _⟩
        · cases he
        · refine ⟨i :: Q, ?_, (reach_cons i hq).trans hr'⟩
          simp only [List.map_cons, List.map_append, List.map_nil]
          exact ((List.subperm_cons _).2 hQ).trans (List.perm_append_singleton _ _).symm.subperm
        · rw [hp] at hw; cases hw
  | ok o =>
    unfold goStep at hg
    cases hp : i.1.1
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hg
      cases hf : o.1.1
      · -- a read, nothing found
        simp only [hf, ↓reduceIte] at hg
        split at hg
        · rename_i hc
          obtain ⟨hw, rfl⟩ := hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          have ho : o = ⟨(false, []), by simp⟩ := Subtype.ext (Prod.ext hf hw)
          subst ho
          constructor
          · intro c hc
            refine ⟨⟨none, P⟩, ⟨none, P⟩, ⟨none, P⟩, hbase, .refl _, ?_, hc⟩
            have := pstep_ok ⟨none, P⟩ i
            rw [step_get i hp, bndO_none] at this
            exact this
          · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
            rcases pstep_inv hs with ⟨_, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
            · rw [step_get i hp] at hr'; exact Fall_reach (hF _ _ h0 hr) hr'
            · cases he
            · cases he
        · cases hg
      · -- a read, a value found
        simp only [hf, Bool.true_eq_false, ↓reduceIte] at hg
        have hw := o.2
        split at hg
        · rename_i hak
          simp only [Option.some.injEq, Prod.mk.injEq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          have ho : o = ⟨(true, o.1.2), hw⟩ := Subtype.ext (Prod.ext hf rfl)
          constructor
          · intro c hc
            refine ⟨⟨a, P⟩, ⟨a, P⟩, ⟨a, P⟩, hbase, .refl _, ?_, hc⟩
            have := pstep_ok ⟨a, P⟩ i
            rw [step_get i hp] at this
            simp only at this
            rw [hak, bndO_got _ hw, ← ho, ← hak] at this
            exact this
          · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
            rcases pstep_inv hs with ⟨_, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
            · rw [step_get i hp] at hr'; exact Fall_reach (hF _ _ h0 hr) hr'
            · cases he
            · cases he
        · rename_i hak
          cases hfd : P.find? (fun j => decide (pendV j = o.1.2)) with
          | none => rw [hfd] at hg; cases hg
          | some j =>
            rw [hfd] at hg
            simp only [Option.some.injEq, Prod.mk.injEq] at hg
            obtain ⟨rfl, rfl⟩ := hg
            obtain ⟨hj, hjv⟩ := find_some hfd
            have hjp := hP j hj
            have ho : o = ⟨(true, o.1.2), hw⟩ := Subtype.ext (Prod.ext hf rfl)
            constructor
            · intro c hc
              have hf1 : PReach regB ⟨a, P⟩ ⟨some o.1.2, P.erase j⟩ := by
                have := PReach.single (PSilent.apply (P := regB) ⟨a, P⟩ j hj)
                rw [step_put j hjp, hjv] at this
                exact this
              refine ⟨⟨a, P⟩, ⟨some o.1.2, P.erase j⟩, ⟨some o.1.2, P.erase j⟩, hbase, hf1, ?_, hc⟩
              have := pstep_ok ⟨some o.1.2, P.erase j⟩ i
              rw [step_get i hp] at this
              simp only at this
              rw [bndO_got _ hw, ← ho] at this
              exact this
            · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
              rcases pstep_inv hs with ⟨he, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
              · rw [step_get i hp] at he hr'
                simp only [Ans.ok.injEq] at he
                rcases fall_read ha (hF _ _ h0 hr) with h1 | ⟨y, -, hy, Q₂, hQ₂, hq₂⟩
                · exfalso
                  rw [h1] at he
                  obtain ⟨O, hO, hO1⟩ := regOut_short ha
                  rw [hO] at he
                  subst he
                  cases a with
                  | none => rw [hO1] at hf; cases hf
                  | some v =>
                    simp only [regOut, Option.isSome_some, Option.getD_some] at hO1
                    exact hak (by rw [show o.1.2 = v from (Prod.ext_iff.1 hO1).2])
                · have hyv : pendV y = o.1.2 := by
                    rw [hy, bndO_got _ (val_short y)] at he
                    rw [he]
                  rw [hyv] at hQ₂ hq₂
                  refine ⟨Q₂, ?_, hq₂.trans hr'⟩
                  rw [← hjv] at hQ₂
                  exact hQ₂.trans (map_erase_perm pendV hj).symm.subperm
              · cases he
              · cases he
    · -- a put
      simp only [hp, ↓reduceIte] at hg
      split at hg
      · rename_i ho1
        simp only [Option.some.injEq, Prod.mk.injEq] at hg
        obtain ⟨rfl, rfl⟩ := hg
        have ho : o = bndO (false, []) := by
          rw [bndO_of (o := (false, [])) (by simp)]; exact Subtype.ext ho1
        subst ho
        constructor
        · intro c hc
          refine ⟨⟨a, P⟩, ⟨a, P⟩, _, hbase, .refl _, ?_, hc⟩
          have := pstep_ok ⟨a, P⟩ i
          rw [step_put i hp] at this
          exact this
        · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
          obtain ⟨Q, hQ, hq⟩ := hF _ _ h0 hr
          rcases pstep_inv hs with ⟨_, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
          · rw [step_put i hp] at hr'
            exact ⟨c.pend, (subperm_map pendV (reach_sub hq)).trans hQ, hr'⟩
          · cases he
          · cases he
      · cases hg

/-- The model's next set, when the Go step refuses the operation: empty. -/
theorem sim_none {a : service.Reg} {P : List HIn} {S : PSet service.Reg HIn} (hS : Sim a P S)
    (ha : RegOk a) {i : HIn} {o : Ans HOut} (hg : goStep a P i o = none) :
    ¬ ∃ c, ppost regB S i o c := by
  rintro ⟨c', c₀, c, c₁, h0, hr, hs, -⟩
  have hFc := Fall_reach (hS.2 _ h0) hr
  rcases pstep_inv hs with ⟨he, -⟩ | ⟨rfl, hw, -⟩ | ⟨rfl, hw, -⟩
  · subst he
    cases hp : i.1.1
    · rw [step_get i hp] at hg
      unfold goStep at hg
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at hg
      rcases fall_read ha hFc with h1 | ⟨y, hym, hy, -⟩
      · rw [h1] at hg
        cases a with
        | none => simp [bndO_none] at hg
        | some v => simp [bndO_got v (ha v rfl)] at hg
      · rw [hy, bndO_got _ (val_short y)] at hg
        simp only [Bool.true_eq_false, ↓reduceIte] at hg
        split at hg
        · cases hg
        · cases hfd : P.find? (fun j => decide (pendV j = pendV y)) with
          | none => exact find_none hfd hym
          | some j => rw [hfd] at hg; cases hg
    · rw [step_put i hp] at hg
      unfold goStep at hg
      simp [hp, bndO] at hg
  · simp [goStep, hw] at hg
  · simp [goStep, hw] at hg

/-- **The simulation**: on a bracketed set, the model allows `(i, o)` exactly when the Go step
does, and its next set is bracketed by the Go step's next state. -/
theorem sim_step {a : service.Reg} {P : List HIn} {S : PSet service.Reg HIn} (hS : Sim a P S)
    (hP : ∀ x ∈ P, x.1.1 = true) (ha : RegOk a) (i : HIn) (o : Ans HOut) :
    ((pSeq regB).step S (i, o)).isSome = (goStep a P i o).isSome ∧
    ∀ a' P' S', goStep a P i o = some (a', P') → (pSeq regB).step S (i, o) = some S' →
      Sim a' P' S' := by
  cases hg : goStep a P i o with
  | none =>
    refine ⟨?_, fun _ _ _ h => by cases h⟩
    have := sim_none hS ha hg
    simp only [pSeq, Option.isSome_none]
    rw [if_neg this]
    rfl
  | some r =>
    obtain ⟨a', P'⟩ := r
    obtain ⟨hne, hsim⟩ := sim_some hS hP ha hg
    refine ⟨?_, ?_⟩
    · simp only [pSeq, Option.isSome_some]
      rw [if_pos hne]
      rfl
    · intro a'' P'' S' he hs
      cases he
      have := pSeq_step_some hs
      subst this
      exact hsim

/-- The Go step's next state keeps the bracket's side conditions, with at most one more pending
write. -/
theorem goStep_ok {a : service.Reg} {P : List HIn} (hP : ∀ x ∈ P, x.1.1 = true) (ha : RegOk a)
    {i : HIn} {o : Ans HOut} {a' : service.Reg} {P' : List HIn}
    (hg : goStep a P i o = some (a', P')) :
    (∀ x ∈ P', x.1.1 = true) ∧ RegOk a' ∧ P'.length ≤ P.length + 1 := by
  cases o with
  | err =>
    unfold goStep at hg
    cases hp : i.1.1
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨hP, ha, by omega⟩
    · simp only [hp, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      refine ⟨fun x hx => ?_, ha, by simp⟩
      rcases List.mem_append.1 hx with h | h
      · exact hP x h
      · simp only [List.mem_singleton] at h; subst h; exact hp
  | ok o =>
    unfold goStep at hg
    cases hp : i.1.1
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hg
      split at hg
      · split at hg
        · simp only [Option.some.injEq, Prod.mk.injEq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          exact ⟨hP, ha, by omega⟩
        · cases hg
      · split at hg
        · simp only [Option.some.injEq, Prod.mk.injEq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          exact ⟨hP, ha, by omega⟩
        · cases hfd : P.find? (fun j => decide (pendV j = o.1.2)) with
          | none => rw [hfd] at hg; cases hg
          | some j =>
            rw [hfd] at hg
            simp only [Option.some.injEq, Prod.mk.injEq] at hg
            obtain ⟨rfl, rfl⟩ := hg
            refine ⟨fun x hx => hP x (List.mem_of_mem_erase hx), ?_, ?_⟩
            · intro v hv; cases hv; exact o.2
            · have := List.length_erase_le (l := P) (a := j); omega
    · simp only [hp, ↓reduceIte] at hg
      split at hg
      · simp only [Option.some.injEq, Prod.mk.injEq] at hg
        obtain ⟨rfl, rfl⟩ := hg
        exact ⟨hP, regOk_some i, by omega⟩
      · cases hg

end pure

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
