/-
The key-value map's porcupine model, pure (notes/dsv-vr.md, step 3): `step` (kit.go) on the model's
state `(Cur, Pend)` is the pending-writes model's step `pSeq kvB` (`Kit.lean`) on any set of
configurations the state stands for (`Rep`): `stepG_pSeq`.

Unlike paxos's register, the state does not determine the set: two histories may reach one state
`(Cur, Pend)` with different sets (a pending put applied and then overwritten by an answered put is
a configuration of one and not of the other). `Rep s Cur Pend` says that `s` holds the
configuration `(Cur, Pend)` itself and that every configuration of `s` is dominated by it (`DOk`: its
pending puts are some of `Pend`'s, and each key's value is `Cur`'s or that of one of `Pend`'s puts
that has taken effect in it, counted). That is enough for `step`'s verdict and next state; and with
nothing pending the set is one configuration, so `Equal` says `true` only then (`rep_eq`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Kit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove EtcdGrove.linkv VsrModel VsrGhost.Impl

section pure
variable [GooseExts]

abbrev Cfg := PCfg VsrModel.Store KIn

/-! ## The Go model's pure state -/

/-- A pair list's map (`lookup`: the first pair of the key). -/
def lk : List (GoString × GoString) → VsrModel.Store
  | [] => fun _ => none
  | (k, v) :: t => fun k' => if k' = k then some v else lk t k'

/-- `set p k v` (kit.go): every pair of `k` replaced by `(k, v)`, or `(k, v)` added. -/
def setP (p : List (GoString × GoString)) (k v : GoString) : List (GoString × GoString) :=
  if p.any (fun x => decide (x.1 = k)) then p.map (fun x => if x.1 = k then (k, v) else x)
  else p ++ [(k, v)]

theorem lk_map (p : List (GoString × GoString)) (k v : GoString) :
    lk (p.map (fun x => if x.1 = k then (k, v) else x)) =
      fun k' => if k' = k then (if p.any (fun x => decide (x.1 = k)) then some v else none)
        else lk p k' := by
  induction p with
  | nil => funext k'; simp [lk]
  | cons x t ih =>
    obtain ⟨a, b⟩ := x
    funext k'
    by_cases ha : a = k
    · subst ha
      simp only [List.map_cons, ↓reduceIte, lk, ih, List.any_cons, decide_true, Bool.true_or]
      by_cases hk : k' = a <;> simp [hk]
    · simp only [List.map_cons, ha, ↓reduceIte, lk, ih, List.any_cons, decide_false,
        Bool.false_or]
      by_cases hk : k' = k
      · subst hk; simp [Ne.symm ha]
      · simp [hk]

theorem lk_append (p : List (GoString × GoString)) (k v : GoString)
    (h : p.any (fun x => decide (x.1 = k)) = false) :
    lk (p ++ [(k, v)]) = fun k' => if k' = k then some v else lk p k' := by
  induction p with
  | nil => funext k'; simp [lk]
  | cons x t ih =>
    obtain ⟨a, b⟩ := x
    simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    funext k'
    simp only [List.cons_append, lk, ih h.2]
    by_cases hk : k' = k
    · subst hk; simp [Ne.symm h.1]
    · simp [hk]

theorem lk_setP (p : List (GoString × GoString)) (k v : GoString) :
    lk (setP p k v) = fun k' => if k' = k then some v else lk p k' := by
  unfold setP
  split
  · rename_i h; rw [lk_map]; funext k'; simp [h]
  · rename_i h; exact lk_append p k v (by
      cases hh : p.any (fun x => decide (x.1 = k)) <;> simp_all)

theorem setP_len (p : List (GoString × GoString)) (k v : GoString) :
    (setP p k v).length ≤ p.length + 1 := by
  unfold setP; split <;> simp

/-- A store's values are short (each an input's value, `InputBounded`). -/
def StBnd (σ : VsrModel.Store) : Prop := ∀ k v, σ k = some v → v.length < 2 ^ 16

/-- **The domination** of a configuration by the state `(Cur, Pend)` (see the file header). -/
def DOk (Cur : List (GoString × GoString)) (Pend : List KIn) (c : Cfg) : Prop :=
  c.pend.Subperm Pend ∧ StBnd c.st ∧ ∀ k, c.st k = lk Cur k ∨
    ∃ x ∈ Pend, ∃ v, x.1 = .put k v ∧ c.st k = some v ∧ c.pend.count x < Pend.count x

/-- **The sets the state `(Cur, Pend)` stands for** (see the file header). -/
def Rep (s : PSet VsrModel.Store KIn) (Cur : List (GoString × GoString)) (Pend : List KIn) : Prop :=
  (∃ c, s c ∧ c.st = lk Cur ∧ c.pend.Perm Pend) ∧ ∀ c, s c → DOk Cur Pend c

/-- `step` (kit.go) on the model's pure state: its verdict and next `(Cur, Pend)`. -/
def stepG (Cur : List (GoString × GoString)) (Pend : List KIn) (i : KIn) (a : Ans KOut) :
    Bool × List (GoString × GoString) × List KIn :=
  match a with
  | .err => (true, Cur, if kvB.isWrite i then Pend ++ [i] else Pend)
  | .ok o =>
    match i.1, o.1 with
    | .put k v, .done => (true, setP Cur k v, Pend)
    | .put _ _, .got _ => (false, Cur, Pend)
    | .get _, .done => (false, Cur, Pend)
    | .get k, .got none => (decide (lk Cur k = none), Cur, Pend)
    | .get k, .got (some w) =>
      if lk Cur k = some w then (true, Cur, Pend) else
      match Pend.find? (fun x => decide (x.1 = .put k w)) with
      | some x => (true, setP Cur k w, Pend.erase x)
      | none => (false, Cur, Pend)

/-! ## Lemmas -/

theorem kin_bnd (x : KIn) {k v : GoString} (h : x.1 = .put k v) : v.length < 2 ^ 16 := by
  obtain ⟨x, hx⟩ := x
  simp only at h
  subst h
  exact hx.2.1.2

theorem stBnd_update {σ : VsrModel.Store} (hσ : StBnd σ) (k v : GoString) (hv : v.length < 2 ^ 16) :
    StBnd (fun k' => if k' = k then some v else σ k') := by
  intro k' w hw
  by_cases e : k' = k
  · simp only [e, ↓reduceIte, Option.some.injEq] at hw; subst hw; exact hv
  · simp only [e, ↓reduceIte] at hw; exact hσ k' w hw

theorem count_erase_le (l : List KIn) (x z : KIn) : (l.erase x).count z ≤ l.count z := by
  rw [List.count_erase]; omega

theorem count_erase_self (l : List KIn) (x : KIn) : (l.erase x).count x = l.count x - 1 := by
  rw [List.count_erase]; simp

theorem count_erase_ne (l : List KIn) {x z : KIn} (h : x ≠ z) : (l.erase x).count z = l.count z := by
  rw [List.count_erase]; simp [h]

theorem subperm_of_count {l₁ l₂ : List KIn} (h : ∀ x, l₁.count x ≤ l₂.count x) : l₁.Subperm l₂ :=
  List.subperm_ext_iff.2 (fun x _ => h x)

/-- **The domination is closed under late effects.** -/
theorem dOk_silent {Cur : List (GoString × GoString)} {Pend : List KIn} {c c' : Cfg}
    (h : DOk Cur Pend c) (hs : PSilent kvB c c') : DOk Cur Pend c' := by
  obtain ⟨hsub, hb, hk⟩ := h
  cases hs with
  | perm p hp =>
    refine ⟨hp.subperm.trans hsub, hb, fun k => ?_⟩
    rcases hk k with e | ⟨x, hx, v, hxv, hst, hc⟩
    · exact .inl e
    · exact .inr ⟨x, hx, v, hxv, hst, by rw [hp.count_eq]; exact hc⟩
  | apply x hx =>
    have hcnt : c.pend.count x ≤ Pend.count x := hsub.count_le x
    have hpos : 0 < c.pend.count x := List.count_pos_iff.2 hx
    refine ⟨(List.erase_subperm x c.pend).trans hsub, ?_, fun k => ?_⟩
    · show StBnd (kvFn c.st x.1).1
      obtain ⟨xi, hxi⟩ := x
      cases xi with
      | get k0 => exact hb
      | put k0 v0 => exact stBnd_update hb k0 v0 (kin_bnd ⟨_, hxi⟩ rfl)
    · show (kvFn c.st x.1).1 k = _ ∨ _
      rcases x with ⟨xi, hxi⟩
      cases xi with
      | get k0 =>
        show c.st k = _ ∨ _
        rcases hk k with e | ⟨z, hz, v, hzv, hst, hc⟩
        · exact .inl e
        · exact .inr ⟨z, hz, v, hzv, hst, Nat.lt_of_le_of_lt (count_erase_le _ _ _) hc⟩
      | put k0 v0 =>
        show (if k = k0 then some v0 else c.st k) = _ ∨ _
        by_cases e : k = k0
        · subst e
          refine .inr ⟨⟨_, hxi⟩, hsub.subset hx, v0, rfl, by simp [kvB, kvFn], ?_⟩
          rw [count_erase_self]; omega
        · rcases hk k with e' | ⟨z, hz, v, hzv, hst, hc⟩
          · exact .inl (by simp [kvB, kvFn, e, e'])
          · exact .inr ⟨z, hz, v, hzv, by simp [kvB, kvFn, e, hst],
              Nat.lt_of_le_of_lt (count_erase_le _ _ _) hc⟩

theorem dOk_reach {Cur : List (GoString × GoString)} {Pend : List KIn} {c c' : Cfg}
    (h : DOk Cur Pend c) (hr : PReach kvB c c') : DOk Cur Pend c' := by
  induction hr with
  | refl => exact h
  | step hs _ ih => exact ih (dOk_silent h hs)

/-- `find?` of a put: one of the list's, of that put. -/
theorem find_put {Pend : List KIn} {k w : GoString} {x : KIn}
    (h : Pend.find? (fun x => decide (x.1 = .put k w)) = some x) : x ∈ Pend ∧ x.1 = .put k w := by
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [decide_eq_true_eq] at h2
  exact ⟨h1, h2⟩

theorem find_put_none {Pend : List KIn} {k w : GoString}
    (h : Pend.find? (fun x => decide (x.1 = .put k w)) = none) (x : KIn) (hx : x ∈ Pend) :
    x.1 ≠ .put k w := by
  have := List.find?_eq_none.1 h x hx
  simpa using this

theorem kvB_put (st : VsrModel.Store) (x : KIn) {k v : GoString} (h : x.1 = .put k v) :
    kvB.step x st = ((fun k' => if k' = k then some v else st k'), ⟨.done, trivial⟩) := by
  simp only [kvB, h, kvFn, bndO_of (o := .done) trivial]

theorem kvB_get (st : VsrModel.Store) (x : KIn) {k : GoString} (h : x.1 = .get k)
    (hb : StBnd st) : kvB.step x st = (st, ⟨.got (st k), by
      cases e : st k with
      | none => trivial
      | some w => exact hb k w e⟩) := by
  simp only [kvB, h, kvFn]
  rw [bndO_of]

/-- **Every step of a dominated configuration is one `step` allows**, to a configuration its next
state dominates. -/
theorem dOk_pstep {Cur : List (GoString × GoString)} {Pend : List KIn} {c c₁ : Cfg} {i : KIn}
    {a : Ans KOut} (h : DOk Cur Pend c) (hs : PStep kvB c i a c₁) :
    (stepG Cur Pend i a).1 = true ∧
      DOk (stepG Cur Pend i a).2.1 (stepG Cur Pend i a).2.2 c₁ := by
  obtain ⟨hsub, hb, hk⟩ := h
  cases hs with
  | obs o hobs => simp [kvB] at hobs
  | errR hw =>
    have e : stepG Cur Pend i .err = (true, Cur, Pend) := by simp [stepG, hw]
    rw [e]
    exact ⟨rfl, hsub, hb, hk⟩
  | errW hw =>
    have e : stepG Cur Pend i .err = (true, Cur, Pend ++ [i]) := by simp [stepG, hw]
    rw [e]
    refine ⟨rfl, subperm_of_count fun z => ?_, hb, fun k => ?_⟩
    · have := hsub.count_le z
      simp only [List.count_cons, List.count_append, List.count_singleton]
      split <;> omega
    · rcases hk k with e | ⟨z, hz, v, hzv, hst, hc⟩
      · exact .inl e
      · refine .inr ⟨z, List.mem_append_left _ hz, v, hzv, hst, ?_⟩
        simp only [List.count_cons, List.count_append, List.count_singleton]
        split <;> omega
  | ok ho =>
    rcases i with ⟨xi, hxi⟩
    cases xi with
    | put k v =>
      rw [kvB_put c.st ⟨_, hxi⟩ rfl]
      have e : stepG Cur Pend ⟨_, hxi⟩ (.ok ⟨.done, trivial⟩) = (true, setP Cur k v, Pend) := by
        simp [stepG]
      rw [e]
      refine ⟨rfl, hsub, stBnd_update hb k v (kin_bnd ⟨_, hxi⟩ rfl), fun k' => ?_⟩
      show (if k' = k then some v else c.st k') = _ ∨ _
      rw [lk_setP]
      by_cases e : k' = k
      · subst e; simp
      · simp only [e, ↓reduceIte]; exact hk k'
    | get k =>
      obtain ⟨O, hO, hO1⟩ : ∃ O : KOut, kvB.step ⟨_, hxi⟩ c.st = (c.st, O) ∧ O.1 = .got (c.st k) :=
        ⟨_, kvB_get c.st ⟨_, hxi⟩ rfl hb, rfl⟩
      rw [hO]
      simp only
      cases hck : c.st k with
      | none =>
        have hl : lk Cur k = none := by
          rcases hk k with e | ⟨z, hz, v, hzv, hst, hc⟩
          · rw [← e, hck]
          · rw [hck] at hst; cases hst
        have e : stepG Cur Pend ⟨_, hxi⟩ (.ok ⟨.got none, trivial⟩) = (true, Cur, Pend) := by
          simp [stepG, hl]
        rw [hck] at hO1
        have : O = ⟨.got none, trivial⟩ := Subtype.ext hO1
        subst this
        rw [e]
        exact ⟨rfl, hsub, hb, hk⟩
      | some w =>
        have hw : w.length < 2 ^ 16 := hb k w hck
        rw [hck] at hO1
        have : O = ⟨.got (some w), hw⟩ := Subtype.ext hO1
        subst this
        by_cases hl : lk Cur k = some w
        · have e : stepG Cur Pend ⟨_, hxi⟩ (.ok ⟨.got (some w), hw⟩) = (true, Cur, Pend) := by
            simp [stepG, hl]
          rw [e]
          exact ⟨rfl, hsub, hb, hk⟩
        · obtain ⟨y, hy, v, hyv, hst, hc⟩ : ∃ y ∈ Pend, ∃ v, y.1 = .put k v ∧ c.st k = some v ∧
              c.pend.count y < Pend.count y := by
            rcases hk k with e | h'
            · exact absurd (e ▸ hck) hl
            · exact h'
          rw [hck, Option.some.injEq] at hst
          subst hst
          cases hf : Pend.find? (fun x => decide (x.1 = .put k w)) with
          | none => exact absurd hyv (find_put_none hf y hy)
          | some x =>
            obtain ⟨hx, hxv⟩ := find_put hf
            have hxy : x = y := Subtype.ext (hxv.trans hyv.symm)
            subst hxy
            have e : stepG Cur Pend ⟨_, hxi⟩ (.ok ⟨.got (some w), hw⟩) =
                (true, setP Cur k w, Pend.erase x) := by
              simp [stepG, hl, hf]
            rw [e]
            refine ⟨rfl, subperm_of_count fun z => ?_, hb, fun k' => ?_⟩
            · have hz := hsub.count_le z
              by_cases e : x = z
              · subst e; rw [count_erase_self]; exact Nat.le_sub_one_of_lt hc
              · rw [count_erase_ne _ e]; exact hz
            · rw [lk_setP]
              by_cases e : k' = k
              · subst e; simp [hck]
              · simp only [e, ↓reduceIte]
                rcases hk k' with e' | ⟨z, hz, u, hzu, hst, hc'⟩
                · exact .inl e'
                · have hzx : x ≠ z := by
                    intro hxz; subst hxz; rw [hxv] at hzu
                    exact e (KvInput.put.inj hzu).1.symm
                  exact .inr ⟨z, (List.mem_erase_of_ne (Ne.symm hzx)).2 hz, u, hzu, hst, by
                    rw [count_erase_ne _ hzx]; exact hc'⟩

theorem pstep_put (c : Cfg) (x : KIn) {k v : GoString} (h : x.1 = .put k v) (o : KOut)
    (ho : o.1 = .done) :
    PStep kvB c x (.ok o) ⟨fun k' => if k' = k then some v else c.st k', c.pend⟩ := by
  have := PStep.ok (P := kvB) c x rfl
  rw [kvB_put c.st x h] at this
  have e : o = ⟨.done, trivial⟩ := Subtype.ext ho
  subst e
  exact this

theorem pstep_get (c : Cfg) (x : KIn) {k : GoString} (h : x.1 = .get k) (hb : StBnd c.st)
    (o : KOut) (ho : o.1 = .got (c.st k)) : PStep kvB c x (.ok o) c := by
  obtain ⟨O, hO, hO1⟩ : ∃ O : KOut, kvB.step x c.st = (c.st, O) ∧ O.1 = .got (c.st k) :=
    ⟨_, kvB_get c.st x h hb, rfl⟩
  have := PStep.ok (P := kvB) c x rfl
  rw [hO] at this
  have e : O = o := Subtype.ext (hO1.trans ho.symm)
  subst e
  exact this

/-- **When `step` says yes, the model's next set has its next state's configuration.** -/
theorem stepG_exists {s : PSet VsrModel.Store KIn} {Cur : List (GoString × GoString)}
    {Pend : List KIn} (h : Rep s Cur Pend) (i : KIn) (a : Ans KOut)
    (hg : (stepG Cur Pend i a).1 = true) :
    ∃ c₁, ppost kvB s i a c₁ ∧ c₁.st = lk (stepG Cur Pend i a).2.1 ∧
      c₁.pend.Perm (stepG Cur Pend i a).2.2 := by
  obtain ⟨⟨c0, hs, hst, hp⟩, hd⟩ := h
  have hb : StBnd c0.st := (hd c0 hs).2.1
  cases a with
  | err =>
    cases hw : kvB.isWrite i
    · have e : stepG Cur Pend i .err = (true, Cur, Pend) := by simp [stepG, hw]
      rw [e]
      exact ⟨c0, ⟨c0, c0, c0, hs, .refl _, .errR c0 i hw rfl, .refl _⟩, hst, hp⟩
    · have e : stepG Cur Pend i .err = (true, Cur, Pend ++ [i]) := by simp [stepG, hw]
      rw [e]
      exact ⟨⟨c0.st, i :: c0.pend⟩, ⟨c0, c0, _, hs, .refl _, .errW c0 i hw rfl, .refl _⟩, hst,
        (hp.cons i).trans (List.perm_append_singleton i Pend).symm⟩
  | ok o =>
    rcases i with ⟨xi, hxi⟩
    rcases o with ⟨ov, hov⟩
    cases xi with
    | put k v =>
      cases ov with
      | got _ => simp [stepG] at hg
      | done =>
        have e : stepG Cur Pend ⟨_, hxi⟩ (.ok ⟨.done, hov⟩) = (true, setP Cur k v, Pend) := by
          simp [stepG]
        rw [e]
        refine ⟨_, ⟨c0, c0, _, hs, .refl _, pstep_put c0 ⟨_, hxi⟩ rfl ⟨.done, hov⟩ rfl, .refl _⟩,
          ?_, hp⟩
        rw [lk_setP, hst]
    | get k =>
      cases ov with
      | done => simp [stepG] at hg
      | got r =>
        cases r with
        | none =>
          have hl : lk Cur k = none := by simpa [stepG] using hg
          have e : stepG Cur Pend ⟨_, hxi⟩ (.ok ⟨.got none, hov⟩) = (true, Cur, Pend) := by
            simp [stepG, hl]
          rw [e]
          exact ⟨c0, ⟨c0, c0, c0, hs, .refl _,
            pstep_get c0 ⟨_, hxi⟩ rfl hb _ (by simp [hst, hl]), .refl _⟩, hst, hp⟩
        | some w =>
          by_cases hl : lk Cur k = some w
          · have e : stepG Cur Pend ⟨_, hxi⟩ (.ok ⟨.got (some w), hov⟩) = (true, Cur, Pend) := by
              simp [stepG, hl]
            rw [e]
            exact ⟨c0, ⟨c0, c0, c0, hs, .refl _,
              pstep_get c0 ⟨_, hxi⟩ rfl hb _ (by simp [hst, hl]), .refl _⟩, hst, hp⟩
          · cases hf : Pend.find? (fun x => decide (x.1 = .put k w)) with
            | none => simp [stepG, hl, hf] at hg
            | some x =>
              obtain ⟨hx, hxv⟩ := find_put hf
              have e : stepG Cur Pend ⟨_, hxi⟩ (.ok ⟨.got (some w), hov⟩) =
                  (true, setP Cur k w, Pend.erase x) := by
                simp [stepG, hl, hf]
              rw [e]
              have hx0 : x ∈ c0.pend := hp.symm.subset hx
              have hsil := PSilent.apply (P := kvB) c0 x hx0
              rw [kvB_put c0.st x hxv] at hsil
              have hbA : StBnd (fun k' => if k' = k then some w else c0.st k') :=
                stBnd_update hb k w (kin_bnd x hxv)
              refine ⟨_, ⟨c0, _, _, hs, .single hsil,
                pstep_get _ ⟨_, hxi⟩ rfl hbA ⟨.got (some w), hov⟩ (by simp), .refl _⟩, ?_,
                hp.erase x⟩
              rw [lk_setP, hst]

/-- **`step` is the model's step** on any set its state stands for: its verdict is whether the
model allows the operation, and the model's next set is one its next state stands for. -/
theorem stepG_pSeq {s : PSet VsrModel.Store KIn} {Cur : List (GoString × GoString)}
    {Pend : List KIn} (h : Rep s Cur Pend) (i : KIn) (a : Ans KOut) :
    ((pSeq kvB).step s (i, a)).isSome = (stepG Cur Pend i a).1 ∧
      ∀ s', (pSeq kvB).step s (i, a) = some s' →
        Rep s' (stepG Cur Pend i a).2.1 (stepG Cur Pend i a).2.2 := by
  -- every configuration of the next set is dominated by the next state, and `step` says yes
  have hall : ∀ c', ppost kvB s i a c' → (stepG Cur Pend i a).1 = true ∧
      DOk (stepG Cur Pend i a).2.1 (stepG Cur Pend i a).2.2 c' := by
    rintro c' ⟨c0, c, c1, hs, hr0, hst, hr1⟩
    have h1 := dOk_pstep (dOk_reach (h.2 c0 hs) hr0) hst
    exact ⟨h1.1, dOk_reach h1.2 hr1⟩
  cases hg : (stepG Cur Pend i a).1
  · refine ⟨?_, fun s' hs' => ?_⟩
    · simp only [pSeq]
      split
      · next hex => obtain ⟨c', hc'⟩ := hex; rw [(hall c' hc').1] at hg; cases hg
      · rfl
    · exfalso
      rw [pSeq_step_some hs'] at hs'
      simp only [pSeq] at hs'
      split at hs'
      · next hex => obtain ⟨c', hc'⟩ := hex; rw [(hall c' hc').1] at hg; cases hg
      · cases hs'
  · obtain ⟨c₁, hc₁, hst₁, hp₁⟩ := stepG_exists h i a hg
    have hstep : (pSeq kvB).step s (i, a) = some (ppost kvB s i a) := by
      simp only [pSeq]
      split
      · rfl
      · next hn => exact absurd ⟨c₁, hc₁⟩ hn
    refine ⟨by rw [hstep]; rfl, fun s' hs' => ?_⟩
    rw [hstep, Option.some.injEq] at hs'
    subst hs'
    exact ⟨⟨c₁, hc₁, hst₁, hp₁⟩, fun c' hc' => (hall c' hc').2⟩

/-- The initial set: `State{}`'s. -/
theorem rep_init : Rep (pInit kvB) [] [] := by
  refine ⟨⟨⟨fun _ => none, []⟩, rfl, by funext k; rfl, .refl _⟩, fun c hc => ?_⟩
  subst hc
  refine ⟨List.Subperm.refl _, ?_, fun k => .inl rfl⟩
  intro k v h
  simp [kvB] at h

/-- With nothing pending, the state stands for one set (its one configuration): `Equal`. -/
theorem rep_eq {s t : PSet VsrModel.Store KIn} {Cur : List (GoString × GoString)}
    (hs : Rep s Cur []) (ht : Rep t Cur []) : s = t := by
  have one : ∀ {u : PSet VsrModel.Store KIn}, Rep u Cur [] → ∀ c, u c ↔ c = ⟨lk Cur, []⟩ := by
    intro u hu c
    constructor
    · intro hc
      obtain ⟨hsub, -, hk⟩ := hu.2 c hc
      have hp : c.pend = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hsub.length_le)
      have hst : c.st = lk Cur := by
        funext k
        rcases hk k with e | ⟨x, hx, -⟩
        · exact e
        · cases hx
      cases c; simp only at hp hst; subst hp hst; rfl
    · intro hc
      obtain ⟨c0, hc0, hst, hp⟩ := hu.1
      have : c0 = ⟨lk Cur, []⟩ := by
        cases c0; simp only at hst hp; subst hst; rw [List.Perm.eq_nil hp]
      subst hc this; exact hc0
  funext c
  exact propext ((one hs c).trans (one ht c).symm)

/-- `step`'s next state: at most one more pair and one more pending put. -/
theorem stepG_bounds (Cur : List (GoString × GoString)) (Pend : List KIn) (i : KIn) (a : Ans KOut) :
    (stepG Cur Pend i a).2.1.length ≤ Cur.length + 1 ∧
      (stepG Cur Pend i a).2.2.length ≤ Pend.length + 1 := by
  have h1 := setP_len Cur
  unfold stepG
  repeat' split
  all_goals simp only [List.length_append, List.length_singleton]
  all_goals first
    | omega
    | exact ⟨h1 _ _, by omega⟩
    | exact ⟨h1 _ _, Nat.le_trans List.length_erase_le (by omega)⟩

end pure

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
