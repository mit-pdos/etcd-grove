/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/InvPure.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The pure core of Gryff's invariant's laws (U4): lemmas about `invFacts` and the strengthened facts
of hub request H-U4-2 (`invFactsR`), and the pure core of `store_update` (the helping step:
a store's tag grows; the operations whose place the frontier passes are appended to `lin` in place
order, and every fact is preserved).
-/
module

public import Dsverify.Proof.gryff.Proto.InvDefs
public import Dsverify.Proof.gryff.Proto.TagOrder
public import Perennial.Std.Word.ToIntArith

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open proto dsverify_lab.harness

/-! ## Replays -/

theorem replayOk_nil (s s' : w64) : replayOk s [] s' ↔ s' = s := Iff.rfl

theorem replayOk_append : ∀ (s : w64) (l1 l2 : List (RegInput w64 × RegOutput w64)) (s2 : w64),
    replayOk s (l1 ++ l2) s2 ↔ ∃ s1, replayOk s l1 s1 ∧ replayOk s1 l2 s2
  | s, [], l2, s2 => by simp [replayOk]
  | s, (i, o) :: l1, l2, s2 => by
    simp only [List.cons_append, replayOk]
    rw [replayOk_append]
    constructor
    · rintro ⟨h1, s1, h2, h3⟩; exact ⟨s1, ⟨h1, h2⟩, h3⟩
    · rintro ⟨s1, ⟨h1, h2⟩, h3⟩; exact ⟨h1, s1, h2, h3⟩

theorem replayOk_det : ∀ {s : w64} {l : List (RegInput w64 × RegOutput w64)} {s1 s2 : w64},
    replayOk s l s1 → replayOk s l s2 → s1 = s2
  | _, [], _, _, h1, h2 => by simp only [replayOk] at h1 h2; rw [h1, h2]
  | _, (_, _) :: _, _, _, h1, h2 => replayOk_det h1.2 h2.2

theorem replayOk_prefix {s s' : w64} {l l1 : List (RegInput w64 × RegOutput w64)}
    (h : replayOk s l s') (hp : l1 <+: l) : ∃ s1, replayOk s l1 s1 := by
  obtain ⟨l2, rfl⟩ := hp
  obtain ⟨s1, h1, _⟩ := (replayOk_append _ _ _ _).1 h
  exact ⟨s1, h1⟩

/-! ## Notation over the invariant's maps -/

/-- An operation's place tag. -/
def ptag (ops : GMap OpId OpMeta) (id : OpId) : Option PTag :=
  (ops.lookup id).bind (fun m => m.place.tag?)

/-- The inputs and outputs of a list of linearized operations. -/
def entries (ops : GMap OpId OpMeta) (L : List (OpId × RegOutput w64)) :
    List (RegInput w64 × RegOutput w64) :=
  L.filterMap (fun x => (ops.lookup x.1).map (fun m => (m.input, x.2)))

/-- The linearized operations placed at or below `t` (the history fact's filter). -/
def preT (ops : GMap OpId OpMeta) (L : List (OpId × RegOutput w64)) (t : PTag) :
    List (OpId × RegOutput w64) :=
  L.filter (fun x => match (ops.lookup x.1).bind (fun m => m.place.tag?) with
    | some tx => decide (tagLe tx t) | none => false)

/-- The place order of `lin`. -/
def linOrd (ops : GMap OpId OpMeta) (x y : OpId × RegOutput w64) : Prop :=
  ∃ mx my tx ty, ops.lookup x.1 = some mx ∧ ops.lookup y.1 = some my ∧
    mx.place.tag? = some tx ∧ my.place.tag? = some ty ∧
    (tagLt tx ty ∨ (tx = ty ∧ rank mx.input ≤ rank my.input))

theorem entries_append (ops : GMap OpId OpMeta) (L1 L2 : List (OpId × RegOutput w64)) :
    entries ops (L1 ++ L2) = entries ops L1 ++ entries ops L2 := by
  simp [entries, List.filterMap_append]

theorem preT_append (ops : GMap OpId OpMeta) (L1 L2 : List (OpId × RegOutput w64)) (t : PTag) :
    preT ops (L1 ++ L2) t = preT ops L1 t ++ preT ops L2 t := by
  simp [preT, List.filter_append]

theorem entries_prefix (ops : GMap OpId OpMeta) {L1 L2 : List (OpId × RegOutput w64)}
    (h : L1 <+: L2) : entries ops L1 <+: entries ops L2 := by
  obtain ⟨L3, rfl⟩ := h
  rw [entries_append]; exact List.prefix_append _ _

theorem mem_preT {ops : GMap OpId OpMeta} {L : List (OpId × RegOutput w64)} {t : PTag}
    {x : OpId × RegOutput w64} :
    x ∈ preT ops L t ↔ x ∈ L ∧ ∃ tx, ptag ops x.1 = some tx ∧ tagLe tx t := by
  unfold preT ptag
  rw [List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    revert h2
    cases (ops.lookup x.1).bind (fun m => m.place.tag?) with
    | none => simp
    | some tx => simp
  · rintro ⟨h1, tx, h2, h3⟩
    refine ⟨h1, ?_⟩
    rw [h2]; simpa using h3

/-- `preT` of a list sorted by place is a prefix of it, the rest placed above `t`. -/
theorem preT_split (ops : GMap OpId OpMeta) (t : PTag) :
    ∀ (L : List (OpId × RegOutput w64)), (∀ x ∈ L, ∃ tx, ptag ops x.1 = some tx) →
      L.Pairwise (linOrd ops) →
      ∃ rest, L = preT ops L t ++ rest ∧ ∀ y ∈ rest, ∃ ty, ptag ops y.1 = some ty ∧ tagLt t ty
  | [], _, _ => ⟨[], by simp [preT], by simp⟩
  | x :: L, htag, hp => by
    rw [List.pairwise_cons] at hp
    obtain ⟨tx, hx⟩ := htag x (List.mem_cons_self ..)
    by_cases hle : tagLe tx t
    · obtain ⟨rest, h1, h2⟩ := preT_split ops t L (fun y hy => htag y (List.mem_cons_of_mem _ hy)) hp.2
      refine ⟨rest, ?_, h2⟩
      have : preT ops (x :: L) t = x :: preT ops L t := by
        unfold preT ptag at *; rw [List.filter_cons]; rw [hx]; simp [hle]
      rw [this, List.cons_append, ← h1]
    · have hlt : tagLt t tx := (not_tagLe_iff _ _).1 hle
      have hall : ∀ y ∈ L, ∃ ty, ptag ops y.1 = some ty ∧ tagLt t ty := by
        intro y hy
        obtain ⟨mx, my, tx', ty, hmx, hmy, htx, hty, hord⟩ := hp.1 y hy
        have : tx' = tx := by
          unfold ptag at hx; rw [hmx] at hx; simp only [Option.bind_some] at hx
          rw [htx] at hx; exact Option.some.inj hx
        subst this
        refine ⟨ty, by unfold ptag; rw [hmy]; simpa using hty, ?_⟩
        rcases hord with h | ⟨h, _⟩
        · exact tagLt_trans hlt h
        · rw [← h]; exact hlt
      refine ⟨x :: L, ?_, ?_⟩
      · have : preT ops (x :: L) t = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro y hy
          rw [mem_preT] at hy
          obtain ⟨hy, ty, h1, h2⟩ := hy
          rcases List.mem_cons.1 hy with e | hy'
          · subst e; rw [hx] at h1; cases h1; exact hle h2
          · obtain ⟨ty', h1', h2'⟩ := hall y hy'
            rw [h1] at h1'; cases h1'
            exact (not_tagLe_iff _ _).2 h2' h2
        rw [this]; rfl
      · intro y hy
        rcases List.mem_cons.1 hy with e | hy'
        · subst e; exact ⟨tx, hx, hlt⟩
        · exact hall y hy'

theorem preT_prefix (ops : GMap OpId OpMeta) (t : PTag) (L : List (OpId × RegOutput w64))
    (htag : ∀ x ∈ L, ∃ tx, ptag ops x.1 = some tx) (hp : L.Pairwise (linOrd ops)) :
    preT ops L t <+: L := by
  obtain ⟨rest, h, _⟩ := preT_split ops t L htag hp
  exact ⟨rest, h.symm⟩


/-! ## The chain -/

theorem W64_inj {a b : Int} (ha : inRange a) (hb : inRange b) (h : W64 a = W64 b) : a = b := by
  have h1 : (W64 a).toInt = a := word.toInt_ofInt_eq a (by unfold inRange at ha; omega)
  have h2 : (W64 b).toInt = b := word.toInt_ofInt_eq b (by unfold inRange at hb; omega)
  rw [← h1, ← h2, h]

theorem casApply_casStep {c o n : Int} (hc : inRange c) (ho : inRange o) :
    (casApply (W64 c) (.cas (W64 o) (W64 n))).1 = W64 (casStep o n c) := by
  unfold casApply casStep
  by_cases h : c = o
  · subst h; simp
  · have : W64 c ≠ W64 o := fun e => h (W64_inj hc ho e)
    simp [h, this]

/-- Each chain entry's result is its CAS applied to `cur`, which is its base, the previous result
given (`prev`), or an earlier entry's result. -/
theorem execOk_cur : ∀ (prev : Option (Int × PTag)) (es : List ExecEntry), execOk prev es →
    ∀ e ∈ es, ∃ cur : Int × PTag, e.res = (casStep e.old e.new cur.1, rmwTag cur.2) ∧
      (cur = e.base ∨ prev = some cur ∨ ∃ e' ∈ es, cur = e'.res)
  | _, [], _, _, hx => by simp at hx
  | prev, e :: es, ⟨h1, h2⟩, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · cases prev with
      | none => exact ⟨x.base, h1, Or.inl rfl⟩
      | some p =>
        by_cases hp : tagLt p.2 x.base.2
        · refine ⟨x.base, ?_, Or.inl rfl⟩; rw [h1]; simp [hp]
        · refine ⟨p, ?_, Or.inr (Or.inl rfl)⟩; rw [h1]; simp [hp]
    · obtain ⟨cur, hc, hor⟩ := execOk_cur (some e.res) es h2 x hx
      refine ⟨cur, hc, ?_⟩
      rcases hor with h | h | ⟨e', he', h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨e, List.mem_cons_self .., (Option.some.inj h).symm⟩)
      · exact Or.inr (Or.inr ⟨e', List.mem_cons_of_mem _ he', h⟩)

theorem casStep_range {o n c : Int} (hn : inRange n) (hc : inRange c) : inRange (casStep o n c) := by
  unfold casStep; split
  · exact hn
  · exact hc

theorem execOk_range : ∀ (prev : Option (Int × PTag)) (es : List ExecEntry), execOk prev es →
    (∀ p, prev = some p → inRange p.1) → (∀ e ∈ es, inRange e.base.1 ∧ inRange e.new) →
    ∀ e ∈ es, inRange e.res.1
  | _, [], _, _, _, _, hx => by simp at hx
  | prev, e :: es, ⟨h1, h2⟩, hp, hb, x, hx => by
    have he : inRange e.res.1 := by
      rw [h1]
      have hcur : inRange (match prev with
          | none => e.base
          | some p => if tagLt p.2 e.base.2 then e.base else p).1 := by
        cases prev with
        | none => exact (hb e (List.mem_cons_self ..)).1
        | some p =>
          simp only
          split
          · exact (hb e (List.mem_cons_self ..)).1
          · exact hp p rfl
      exact casStep_range (hb e (List.mem_cons_self ..)).2 hcur
    rcases List.mem_cons.1 hx with rfl | hx
    · exact he
    · exact execOk_range (some e.res) es h2 (fun p hp' => by cases hp'; exact he)
        (fun y hy => hb y (List.mem_cons_of_mem _ hy)) x hx

/-! ## The strengthened facts (hub request H-U4-2) -/

/-- The first-frozen facts with H-U4-2's (X1-X4; `extraFacts` is now in `Proto/Inv.lean` and
part of `invFacts`: `invFacts_R`). -/
def invFactsR (σ : w64) (stores : GMap Nat (w64 × PTag)) (tv : GMap PTag w64)
    (lbs : GMap (Nat × PTag) Unit) (ops : GMap OpId OpMeta)
    (lin : List (OpId × RegOutput w64)) (insts : GMap (Int × Int) InstAttrs)
    (execS : List ExecEntry) (preds : GMap Nat (List ExecEntry)) (turns : GMap Int (Int × Bool)) : Prop :=
  invFactsCore σ stores tv lbs ops lin insts execS preds turns ∧ extraFacts tv ops insts execS

/-- The invariant's facts give `invFactsR`. -/
theorem invFacts_R {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)}
    (h : invFactsB σ stores tv lbs ops lin insts execS preds turns) :
    invFactsR σ stores tv lbs ops lin insts execS preds turns :=
  ⟨h.1, h.2.1⟩

/-! ## Splitting a sorted `lin` at a tag -/

/-- The linearized operations placed strictly below `t`. -/
def ltT (ops : GMap OpId OpMeta) (L : List (OpId × RegOutput w64)) (t : PTag) :
    List (OpId × RegOutput w64) :=
  L.filter (fun x => match ptag ops x.1 with | some tx => decide (tagLt tx t) | none => false)

/-- The linearized operations placed at `t`. -/
def eqT (ops : GMap OpId OpMeta) (L : List (OpId × RegOutput w64)) (t : PTag) :
    List (OpId × RegOutput w64) :=
  L.filter (fun x => decide (ptag ops x.1 = some t))

theorem linOrd_tag {ops : GMap OpId OpMeta} {x y : OpId × RegOutput w64} {tx ty : PTag}
    (h : linOrd ops x y) (hx : ptag ops x.1 = some tx) (hy : ptag ops y.1 = some ty) :
    tagLe tx ty := by
  obtain ⟨mx, my, tx', ty', hmx, hmy, htx, hty, hord⟩ := h
  unfold ptag at hx hy
  rw [hmx] at hx; rw [hmy] at hy
  simp only [Option.bind_some] at hx hy
  rw [htx] at hx; rw [hty] at hy
  cases hx; cases hy
  rcases hord with h | ⟨h, _⟩
  · exact tagLe_of_lt h
  · rw [h]; exact tagLe_refl _

theorem preT_eq_lt_eq (ops : GMap OpId OpMeta) (t : PTag) :
    ∀ (L : List (OpId × RegOutput w64)), (∀ x ∈ L, ∃ tx, ptag ops x.1 = some tx) →
      L.Pairwise (linOrd ops) → preT ops L t = ltT ops L t ++ eqT ops L t
  | [], _, _ => rfl
  | x :: L, htag, hp => by
    rw [List.pairwise_cons] at hp
    obtain ⟨tx, hx⟩ := htag x (List.mem_cons_self ..)
    have htag' := fun y hy => htag y (List.mem_cons_of_mem _ hy)
    have ih := preT_eq_lt_eq ops t L htag' hp.2
    -- every later element is placed at or above `tx`
    have hge : ∀ y ∈ L, ∃ ty, ptag ops y.1 = some ty ∧ tagLe tx ty := by
      intro y hy
      obtain ⟨ty, h⟩ := htag' y hy
      exact ⟨ty, h, linOrd_tag (hp.1 y hy) hx h⟩
    have hpx : (match (ops.lookup x.1).bind (fun m => m.place.tag?) with
        | some tx => decide (tagLe tx t) | none => false) = decide (tagLe tx t) := by
      unfold ptag at hx; rw [hx]
    have hlx : (match ptag ops x.1 with | some tx => decide (tagLt tx t) | none => false) =
        decide (tagLt tx t) := by rw [hx]
    unfold preT ltT eqT at *
    rw [List.filter_cons, List.filter_cons, List.filter_cons, hpx, hlx, hx]
    by_cases h1 : tagLt tx t
    · have h2 : tagLe tx t := tagLe_of_lt h1
      have h3 : tx ≠ t := tagLt_ne h1
      simp only [h1, h2, h3, decide_true, decide_false, ite_true, ite_false, Option.some.injEq,
        Bool.false_eq_true]
      rw [ih]; rfl
    · by_cases h2 : tx = t
      · subst h2
        have hlt0 : List.filter (fun x => match ptag ops x.1 with
            | some tz => decide (tagLt tz tx) | none => false) L = [] := by
          rw [List.filter_eq_nil_iff]
          intro y hy
          obtain ⟨ty, hy1, hy2⟩ := hge y hy
          rw [hy1]; simpa using (not_tagLt_iff _ _).2 hy2
        have hsame : List.filter (fun x => match (ops.lookup x.1).bind (fun m => m.place.tag?) with
            | some tz => decide (tagLe tz tx) | none => false) L =
            List.filter (fun x => decide (ptag ops x.1 = some tx)) L := by
          apply List.filter_congr
          intro y hy
          obtain ⟨ty, hy1, hy2⟩ := hge y hy
          have : (ops.lookup y.1).bind (fun m => m.place.tag?) = some ty := hy1
          rw [this, hy1]
          simp only [Option.some.injEq]
          by_cases e : ty = tx
          · subst e; simp [tagLe_refl]
          · have : ¬ tagLe ty tx := fun h => e (tagLe_antisymm h hy2)
            simp [this, e]
        simp only [h1, tagLe_refl, decide_true, decide_false, ite_true, ite_false,
          Bool.false_eq_true]
        rw [hlt0, hsame]; rfl
      · have h3 : ¬ tagLe tx t := fun h => by
          rcases h with h | h
          · exact h1 h
          · exact h2 h
        have hall : ∀ y ∈ L, ∃ ty, ptag ops y.1 = some ty ∧ tagLt t ty := by
          intro y hy
          obtain ⟨ty, hy1, hy2⟩ := hge y hy
          exact ⟨ty, hy1, tagLt_of_lt_of_le ((not_tagLe_iff _ _).1 h3) hy2⟩
        have e1 : List.filter (fun x => match (ops.lookup x.1).bind (fun m => m.place.tag?) with
            | some tx => decide (tagLe tx t) | none => false) L = [] := by
          rw [List.filter_eq_nil_iff]
          intro y hy
          obtain ⟨ty, hy1, hy2⟩ := hall y hy
          have : (ops.lookup y.1).bind (fun m => m.place.tag?) = some ty := hy1
          rw [this]; simpa using (not_tagLe_iff _ _).2 hy2
        have e2 : List.filter (fun x => match ptag ops x.1 with
            | some tx => decide (tagLt tx t) | none => false) L = [] := by
          rw [List.filter_eq_nil_iff]
          intro y hy
          obtain ⟨ty, hy1, hy2⟩ := hall y hy
          rw [hy1]; simpa using tagLt_asymm hy2
        have e3 : List.filter (fun x => decide (ptag ops x.1 = some t)) L = [] := by
          rw [List.filter_eq_nil_iff]
          intro y hy
          obtain ⟨ty, hy1, hy2⟩ := hall y hy
          rw [hy1]; simpa using (tagLt_ne hy2).symm
        simp only [h1, h2, h3, decide_false, ite_false, Option.some.injEq, Bool.false_eq_true]
        rw [e1, e2, e3]; rfl


theorem rank_ne_zero {i : RegInput w64} (h : rank i ≠ 0) : i = .read := by
  cases i <;> simp_all [rank]

theorem rank_write (v : w64) : rank (RegInput.write v) = 0 := rfl
theorem rank_cas (o n : w64) : rank (RegInput.cas o n) = 0 := rfl

/-- The operations placed at `t` in a sorted `lin` where `t`'s producer `P` is linearized: `P`
first, then reads. -/
theorem eqT_struct (ops : GMap OpId OpMeta) (L : List (OpId × RegOutput w64)) (t : PTag)
    (hL2 : L.Pairwise (linOrd ops)) (hnd : (L.map Prod.fst).Nodup)
    (huniq : ∀ id1 id2 m1 m2 t, ops.lookup id1 = some m1 → ops.lookup id2 = some m2 →
      m1.place.tag? = some t → m2.place.tag? = some t → rank m1.input = 0 →
      rank m2.input = 0 → id1 = id2)
    (P : OpId × RegOutput w64) (mP : OpMeta) (hP : P ∈ L) (hmP : ops.lookup P.1 = some mP)
    (hPt : mP.place.tag? = some t) (hPr : rank mP.input = 0) :
    ∃ rest, eqT ops L t = P :: rest ∧ ∀ y ∈ rest, ∃ m, ops.lookup y.1 = some m ∧ m.input = .read := by
  have hsub : (eqT ops L t).Sublist L := List.filter_sublist
  have hp : (eqT ops L t).Pairwise (linOrd ops) := hL2.sublist hsub
  have hnd' : ((eqT ops L t).map Prod.fst).Nodup := hnd.sublist (hsub.map _)
  have hptP : ptag ops P.1 = some t := by unfold ptag; rw [hmP]; simpa using hPt
  have hmemE : ∀ x, x ∈ eqT ops L t ↔ x ∈ L ∧ ptag ops x.1 = some t := by
    intro x; unfold eqT; simp
  have hPE : P ∈ eqT ops L t := (hmemE P).2 ⟨hP, hptP⟩
  -- a rank-0 member is P
  have hzero : ∀ y ∈ eqT ops L t, ∀ m, ops.lookup y.1 = some m → rank m.input = 0 → y.1 = P.1 := by
    intro y hy m hm hr
    have hyt := ((hmemE y).1 hy).2
    unfold ptag at hyt; rw [hm] at hyt; simp only [Option.bind_some] at hyt
    exact huniq _ _ _ _ t hm hmP hyt hPt hr hPr
  generalize hE : eqT ops L t = E at hp hnd' hPE hzero hmemE
  cases E with
  | nil => simp at hPE
  | cons y rest =>
    rw [List.pairwise_cons] at hp
    simp only [List.map_cons, List.nodup_cons] at hnd'
    have hyP : y = P := by
      rcases List.mem_cons.1 hPE with e | hPr'
      · exact e.symm
      · obtain ⟨my, mP', ty, tP, hmy, hmP', hty, htP, hord⟩ := hp.1 P hPr'
        rw [hmP] at hmP'; cases hmP'
        have hyt := ((hmemE y).1 (List.mem_cons_self ..)).2
        unfold ptag at hyt; rw [hmy] at hyt; simp only [Option.bind_some] at hyt
        rw [hyt] at hty; cases hty; rw [hPt] at htP; cases htP
        have hr : rank my.input = 0 := by
          rcases hord with h | ⟨_, h⟩
          · exact absurd h (tagLt_irrefl _)
          · omega
        have := hzero y (List.mem_cons_self ..) my hmy hr
        exact absurd (this ▸ List.mem_map_of_mem (f := Prod.fst) hPr') hnd'.1
    subst hyP
    refine ⟨rest, rfl, fun z hz => ?_⟩
    have hz' := (hmemE z).1 (List.mem_cons_of_mem _ hz)
    obtain ⟨tz, hz1⟩ : ∃ tz, ptag ops z.1 = some tz := ⟨t, hz'.2⟩
    unfold ptag at hz1
    cases hmz : ops.lookup z.1 with
    | none => rw [hmz] at hz1; simp at hz1
    | some mz =>
      refine ⟨mz, rfl, rank_ne_zero fun hr => ?_⟩
      have := hzero z (List.mem_cons_of_mem _ hz) mz hmz hr
      exact hnd'.1 (this ▸ List.mem_map_of_mem (f := Prod.fst) hz)

theorem replayOk_reads (ops : GMap OpId OpMeta) :
    ∀ (rest : List (OpId × RegOutput w64)) (s s' : w64),
      (∀ y ∈ rest, ∃ m, ops.lookup y.1 = some m ∧ m.input = .read) →
      replayOk s (entries ops rest) s' → s' = s
  | [], s, s', _, h => h
  | y :: rest, s, s', hr, h => by
    obtain ⟨m, hm, hi⟩ := hr y (List.mem_cons_self ..)
    have : entries ops (y :: rest) = (m.input, y.2) :: entries ops rest := by
      simp [entries, hm]
    rw [this, hi] at h
    exact replayOk_reads ops rest s s' (fun z hz => hr z (List.mem_cons_of_mem _ hz)) h.2

theorem replayOk_eqT (ops : GMap OpId OpMeta) (P : OpId × RegOutput w64) (mP : OpMeta)
    (hmP : ops.lookup P.1 = some mP) (rest : List (OpId × RegOutput w64))
    (hr : ∀ y ∈ rest, ∃ m, ops.lookup y.1 = some m ∧ m.input = .read) {s s' : w64}
    (h : replayOk s (entries ops (P :: rest)) s') : s' = (casApply s mP.input).1 := by
  have : entries ops (P :: rest) = (mP.input, P.2) :: entries ops rest := by
    simp [entries, hmP]
  rw [this] at h
  exact replayOk_reads ops rest _ _ hr h.2

theorem length_filter_lt {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) → (∃ x ∈ l, q x = true ∧ p x = false) →
      (l.filter p).length < (l.filter q).length
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | x :: l, hpq, ⟨y, hy, hqy, hpy⟩ => by
    have hle : (l.filter p).length ≤ (l.filter q).length := by
      clear hy hqy hpy y
      induction l with
      | nil => simp
      | cons z l ih =>
        simp only [List.filter_cons]
        have := hpq z (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        cases hpz : p z <;> cases hqz : q z <;> simp_all <;>
          first | omega | exact ih (fun w hw => hpq w (by simp_all)) |
            (have := ih (fun w hw => hpq w (by simp_all)); omega)
    rcases List.mem_cons.1 hy with rfl | hy
    · simp only [List.filter_cons, hqy, hpy]; simp; omega
    · have ih := length_filter_lt p q l (fun z hz => hpq z (List.mem_cons_of_mem _ hz)) ⟨y, hy, hqy, hpy⟩
      simp only [List.filter_cons]
      have := hpq x (List.mem_cons_self ..)
      cases hpx : p x <;> cases hqx : q x <;> simp_all <;> omega


/-- `ltT` below an RMW's result tag is `preT` at the tag it applied to (no tag in between). -/
theorem ltT_rmwTag (ops : GMap OpId OpMeta) (L : List (OpId × RegOutput w64)) (c : PTag) :
    ltT ops L (rmwTag c) = preT ops L c := by
  unfold ltT preT
  apply List.filter_congr
  intro x _
  have : ptag ops x.1 = (ops.lookup x.1).bind (fun m => m.place.tag?) := rfl
  rw [← this]
  cases ptag ops x.1 with
  | none => rfl
  | some tx =>
    simp only [decide_eq_decide]
    constructor
    · intro h
      rcases tagLt_or_le c tx with h' | h'
      · exact absurd h (fun h => rmwTag_no_between c tx h' h)
      · exact h'
    · intro h; exact tagLt_of_le_of_lt h (tagLt_rmwTag c)

/-- The number of chain entries whose result is below `t`. -/
def chainBelow (execS : List ExecEntry) (t : PTag) : Nat :=
  (execS.filter (fun e => decide (tagLt e.res.2 t))).length

/-- **The history fact, extended**: in a sorted `lin` that contains every rank-0 operation placed
at or below the new frontier `F'` (from a frontier at or below its place), every stored tag at or
below `F'` holds the replay of the operations placed at or below it, given that this holds below
the old frontier `F`. -/
theorem history_extend (ops : GMap OpId OpMeta) (tv : GMap PTag w64)
    (insts : GMap (Int × Int) InstAttrs) (execS : List ExecEntry)
    (L : List (OpId × RegOutput w64)) (F F' : PTag) (σ' : w64)
    (hL1 : ∀ x ∈ L, ∃ tx, ptag ops x.1 = some tx)
    (hL2 : L.Pairwise (linOrd ops))
    (hL3 : (L.map Prod.fst).Nodup)
    (hL5 : replayOk (W64 0) (entries ops L) σ')
    (hmem : ∀ id m x freg, ops.lookup id = some m → rank m.input = 0 →
      m.place = .placed (some x) freg → tagLe freg x → tagLe x F' → ∃ o, (id, o) ∈ L)
    (huniq : ∀ id1 id2 m1 m2 t, ops.lookup id1 = some m1 → ops.lookup id2 = some m2 →
      m1.place.tag? = some t → m2.place.tag? = some t → rank m1.input = 0 →
      rank m2.input = 0 → id1 = id2)
    (hold : ∀ t v, tv.lookup t = some v → tagLe t F →
      replayOk (W64 0) (entries ops (preT ops L t)) v)
    (hF0 : tagLe tag0 F)
    (hx : extraFacts tv ops insts execS)
    (hexec : execOk none execS)
    (hchain : ∀ e ∈ execS, tv.lookup e.res.2 = some (W64 e.res.1)) :
    ∀ t v, tv.lookup t = some v → tagLe t F' →
      replayOk (W64 0) (entries ops (preT ops L t)) v := by
  obtain ⟨_, hprod, hbase⟩ := hx
  -- the state after `preT t` exists
  have hpre : ∀ t, ∃ s, replayOk (W64 0) (entries ops (preT ops L t)) s := fun t =>
    replayOk_prefix hL5 (entries_prefix ops (preT_prefix ops t L hL1 hL2))
  -- the step at a tag `t` above `F` with a linearized producer `P`
  have hstep : ∀ t, ¬ tagLe t F → ∀ id m freg, ops.lookup id = some m →
      m.place = .placed (some t) freg → tagLe freg t → tagLe t F' → rank m.input = 0 →
      ∃ s_lt, replayOk (W64 0) (entries ops (ltT ops L t)) s_lt ∧
        replayOk (W64 0) (entries ops (preT ops L t)) (casApply s_lt m.input).1 := by
    intro t _ id m freg hm hpl hf htF hr
    obtain ⟨o, hP⟩ := hmem id m t freg hm hr hpl hf htF
    have hPt : m.place.tag? = some t := by rw [hpl]; rfl
    obtain ⟨rest, hE, hreads⟩ := eqT_struct ops L t hL2 hL3 huniq (id, o) m hP hm hPt hr
    have hsplit := preT_eq_lt_eq ops t L hL1 hL2
    obtain ⟨s_t, hs_t⟩ := hpre t
    have hs_t0 := hs_t
    rw [hsplit, entries_append] at hs_t
    obtain ⟨s_lt, h1, h2⟩ := (replayOk_append _ _ _ _).1 hs_t
    rw [hE] at h2
    have := replayOk_eqT ops (id, o) m hm rest hreads h2
    refine ⟨s_lt, h1, ?_⟩
    rw [← this]; exact hs_t0
  -- tags at or below `F`, or produced by a write
  have hwrite : ∀ t v, tv.lookup t = some v → tagLe t F' →
      (tagLe t F ∨ ∃ id m freg, ops.lookup id = some m ∧ m.place = .placed (some t) freg ∧
        tagLe freg t ∧ m.input = .write v) →
      replayOk (W64 0) (entries ops (preT ops L t)) v := by
    intro t v ht htF h
    by_cases hle : tagLe t F
    · exact hold t v ht hle
    rcases h with h | ⟨id, m, freg, hm, hpl, hf, hi⟩
    · exact absurd h hle
    obtain ⟨s_lt, _, h2⟩ := hstep t hle id m freg hm hpl hf htF (by rw [hi]; rfl)
    rw [hi] at h2; exact h2
  -- strong induction on the number of chain entries below the tag
  suffices H : ∀ n t v, chainBelow execS t ≤ n → tv.lookup t = some v → tagLe t F' →
      replayOk (W64 0) (entries ops (preT ops L t)) v from
    fun t v ht htF => H _ t v (Nat.le_refl _) ht htF
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro t v hn ht htF
    by_cases hle : tagLe t F
    · exact hold t v ht hle
    have ht0 : t ≠ tag0 := fun e => hle (e ▸ hF0)
    obtain ⟨id, m, freg, hm, hpl, hf, hin⟩ := hprod t v ht ht0
    rcases hin with hw | ⟨e, a, he, het, hev, _, _, hi⟩
    · exact hwrite t v ht htF (Or.inr ⟨id, m, freg, hm, hpl, hf, hw⟩)
    obtain ⟨cur, hres, hcur⟩ := execOk_cur none execS hexec e he
    have htc : t = rmwTag cur.2 := by rw [← het, hres]
    -- the tag the RMW applied to: stored, its value in range
    have hcs : tv.lookup cur.2 = some (W64 cur.1) ∧ inRange cur.1 := by
      rcases hcur with h | h | ⟨e', he', h⟩
      · subst h; exact ⟨(hbase e he).1, (hbase e he).2.1⟩
      · cases h
      · subst h
        exact ⟨hchain e' he', execOk_range none execS hexec (by simp)
          (fun x hx => ⟨(hbase x hx).2.1, (hbase x hx).2.2.2⟩) e' he'⟩
    have hct : tagLt cur.2 t := htc ▸ tagLt_rmwTag cur.2
    have hcF : tagLe cur.2 F' := tagLe_trans (tagLe_of_lt hct) htF
    -- the history at the applied tag
    have hcur_hist : replayOk (W64 0) (entries ops (preT ops L cur.2)) (W64 cur.1) := by
      by_cases hcle : tagLe cur.2 F
      · exact hold _ _ hcs.1 hcle
      have hc0 : cur.2 ≠ tag0 := fun e => hcle (e ▸ hF0)
      obtain ⟨id', m', freg', hm', hpl', hf', hin'⟩ := hprod cur.2 _ hcs.1 hc0
      rcases hin' with hw' | ⟨e'', a'', he'', het'', _, _, _, _⟩
      · exact hwrite _ _ hcs.1 hcF (Or.inr ⟨id', m', freg', hm', hpl', hf', hw'⟩)
      · -- produced by an earlier chain entry: fewer entries below it
        have hlt : chainBelow execS cur.2 < chainBelow execS t := by
          unfold chainBelow
          apply length_filter_lt
          · intro x _ hx
            simp only [decide_eq_true_eq] at hx ⊢
            exact tagLt_trans hx hct
          · exact ⟨e'', he'', by simp [het'', hct], by simp [het'', tagLt_irrefl]⟩
        first
        | omega
        | exact ih cur.2 _ (by omega) hcs.1 hcF
    obtain ⟨s_lt, h1, h2⟩ := hstep t hle id m freg hm hpl hf htF (by rw [hi]; rfl)
    rw [htc, ltT_rmwTag] at h1
    have := replayOk_det h1 hcur_hist
    subst this
    rw [hi, casApply_casStep hcs.2 (hbase e he).2.2.1] at h2
    rw [← hev, hres]
    exact h2


/-! ## The helping step -/

/-- An operation qualifies for linearization at frontier `F`: placed at a tag at or below `F`,
from a frontier at or below its place; a read also needs its tag's producer to qualify (the
non-recursive form of `invFacts`' linearization fact). -/
def qualP (ops : GMap OpId OpMeta) (F : PTag) (m : OpMeta) : Prop :=
  ∃ t freg, m.place = .placed (some t) freg ∧ tagLe freg t ∧ tagLe t F ∧
    (rank m.input = 0 ∨ t = tag0 ∨ ∃ id' m' freg', ops.lookup id' = some m' ∧
      rank m'.input = 0 ∧ m'.place = .placed (some t) freg' ∧ tagLe freg' t)

/-- The right side of `invFacts`' linearization fact. -/
def linRHS (ops : GMap OpId OpMeta) (F : PTag) (L : List (OpId × RegOutput w64)) (m : OpMeta) :
    Prop :=
  ∃ t freg, m.place = .placed (some t) freg ∧ tagLe freg t ∧ tagLe t F ∧
    (rank m.input = 0 ∨ t = tag0 ∨ ∃ id' m' o', ops.lookup id' = some m' ∧
      rank m'.input = 0 ∧ m'.place.tag? = some t ∧ (id', o') ∈ L)

theorem place_tag_eq {m : OpMeta} {t : PTag} :
    m.place.tag? = some t ↔ ∃ freg, m.place = .placed (some t) freg := by
  cases h : m.place with
  | unplaced => simp [Placement.tag?]
  | placed p f =>
    cases p with
    | none => simp [Placement.tag?]
    | some t' => simp [Placement.tag?]

/-- With `lin` characterized for the rank-0 operations, the two forms agree. -/
theorem linRHS_iff_qualP {ops : GMap OpId OpMeta} {F : PTag} {L : List (OpId × RegOutput w64)}
    (h0 : ∀ id' m', ops.lookup id' = some m' → rank m'.input = 0 →
      ((∃ o, (id', o) ∈ L) ↔ ∃ t freg, m'.place = .placed (some t) freg ∧ tagLe freg t ∧
        tagLe t F)) (m : OpMeta) :
    linRHS ops F L m ↔ qualP ops F m := by
  unfold linRHS qualP
  constructor
  · rintro ⟨t, freg, h1, h2, h3, h4⟩
    refine ⟨t, freg, h1, h2, h3, ?_⟩
    rcases h4 with h | h | ⟨id', m', o', hm', hr, ht, hin⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨t', freg', hp, hf, _⟩ := (h0 id' m' hm' hr).1 ⟨o', hin⟩
      have : t' = t := by
        have := place_tag_eq.2 ⟨freg', hp⟩; rw [this] at ht; exact Option.some.inj ht
      subst this
      exact Or.inr (Or.inr ⟨id', m', freg', hm', hr, hp, hf⟩)
  · rintro ⟨t, freg, h1, h2, h3, h4⟩
    refine ⟨t, freg, h1, h2, h3, ?_⟩
    rcases h4 with h | h | ⟨id', m', freg', hm', hr, hp, hf⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨o', hin⟩ := (h0 id' m' hm' hr).2 ⟨t, freg', hp, hf, h3⟩
      exact Or.inr (Or.inr ⟨id', m', o', hm', hr, place_tag_eq.2 ⟨freg', hp⟩, hin⟩)

theorem rank0_of_char {ops : GMap OpId OpMeta} {F : PTag} {L : List (OpId × RegOutput w64)}
    {P : OpMeta → Prop}
    (h : ∀ id m, ops.lookup id = some m → ((∃ o, (id, o) ∈ L) ↔ P m))
    (hP : ∀ m, rank m.input = 0 → (P m ↔ ∃ t freg, m.place = .placed (some t) freg ∧
      tagLe freg t ∧ tagLe t F)) :
    ∀ id' m', ops.lookup id' = some m' → rank m'.input = 0 →
      ((∃ o, (id', o) ∈ L) ↔ ∃ t freg, m'.place = .placed (some t) freg ∧ tagLe freg t ∧
        tagLe t F) :=
  fun id' m' hm hr => (h id' m' hm).trans (hP m' hr)

theorem qualP_rank0 {ops : GMap OpId OpMeta} {F : PTag} (m : OpMeta) (hr : rank m.input = 0) :
    qualP ops F m ↔ ∃ t freg, m.place = .placed (some t) freg ∧ tagLe freg t ∧ tagLe t F :=
  ⟨fun ⟨t, freg, h1, h2, h3, _⟩ => ⟨t, freg, h1, h2, h3⟩,
   fun ⟨t, freg, h1, h2, h3⟩ => ⟨t, freg, h1, h2, h3, Or.inl hr⟩⟩

theorem linRHS_rank0 {ops : GMap OpId OpMeta} {F : PTag} {L : List (OpId × RegOutput w64)}
    (m : OpMeta) (hr : rank m.input = 0) :
    linRHS ops F L m ↔ ∃ t freg, m.place = .placed (some t) freg ∧ tagLe freg t ∧ tagLe t F :=
  ⟨fun ⟨t, freg, h1, h2, h3, _⟩ => ⟨t, freg, h1, h2, h3⟩,
   fun ⟨t, freg, h1, h2, h3⟩ => ⟨t, freg, h1, h2, h3, Or.inl hr⟩⟩

theorem qualP_mono {ops : GMap OpId OpMeta} {F F' : PTag} (hF : tagLe F F') {m : OpMeta} :
    qualP ops F m → qualP ops F' m := fun ⟨t, freg, h1, h2, h3, h4⟩ =>
  ⟨t, freg, h1, h2, tagLe_trans h3 hF, h4⟩

/-- A qualifying operation placed at or below `F` qualifies at `F` already. -/
theorem qualP_down {ops : GMap OpId OpMeta} {F F' : PTag} {m : OpMeta} (h : qualP ops F' m)
    {t : PTag} (ht : m.place.tag? = some t) (htF : tagLe t F) : qualP ops F m := by
  obtain ⟨t', freg, h1, h2, _, h4⟩ := h
  have : t' = t := by rw [h1] at ht; exact Option.some.inj ht
  subst this
  exact ⟨t', freg, h1, h2, htF, h4⟩

theorem qualP_tag {ops : GMap OpId OpMeta} {F : PTag} {m : OpMeta} (h : qualP ops F m) :
    ∃ t, m.place.tag? = some t ∧ tagLe t F := by
  obtain ⟨t, freg, h1, _, h3, _⟩ := h
  exact ⟨t, by rw [h1]; rfl, h3⟩

/-- The sort key of a linearized operation: its place and its rank. -/
def opKey (ops : GMap OpId OpMeta) (id : OpId) : PTag × Nat :=
  match ops.lookup id with
  | some m => ((m.place.tag?).getD tag0, rank m.input)
  | none => (tag0, 0)

def keyLeB (a b : PTag × Nat) : Bool := decide (tagLt a.1 b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))

theorem keyLeB_trans (a b c : PTag × Nat) : keyLeB a b = true → keyLeB b c = true →
    keyLeB a c = true := by
  unfold keyLeB; simp only [decide_eq_true_eq]
  rintro (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
  · exact Or.inl (tagLt_trans h1 h2)
  · rw [← h2]; exact Or.inl h1
  · rw [h1]; exact Or.inl h2
  · exact Or.inr ⟨h1.trans h2, by omega⟩

theorem keyLeB_total (a b : PTag × Nat) : (keyLeB a b || keyLeB b a) = true := by
  unfold keyLeB
  rcases tagLt_or_le a.1 b.1 with h | h
  · simp [h]
  · rcases h with h | h
    · simp [h]
    · by_cases h' : a.2 ≤ b.2
      · simp [h, h']
      · have : b.2 ≤ a.2 := by omega
        simp [h, this]

/-- Replay a list of operations' inputs from `s`: their outputs and the final state. -/
def replayIds (ops : GMap OpId OpMeta) : w64 → List OpId → List (OpId × RegOutput w64) × w64
  | s, [] => ([], s)
  | s, id :: ids =>
    let i := match ops.lookup id with | some m => m.input | none => .read
    let r := replayIds ops (casApply s i).1 ids
    ((id, (casApply s i).2) :: r.1, r.2)

theorem replayIds_fst (ops : GMap OpId OpMeta) :
    ∀ (s : w64) (ids : List OpId), (replayIds ops s ids).1.map Prod.fst = ids
  | _, [] => rfl
  | s, id :: ids => by simp [replayIds, replayIds_fst ops _ ids]

theorem replayIds_ok (ops : GMap OpId OpMeta) :
    ∀ (s : w64) (ids : List OpId), (∀ id ∈ ids, (ops.lookup id).isSome) →
      replayOk s (entries ops (replayIds ops s ids).1) (replayIds ops s ids).2
  | _, [], _ => rfl
  | s, id :: ids, h => by
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (h id (List.mem_cons_self ..))
    have ih := replayIds_ok ops (casApply s m.input).1 ids
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [replayIds, hm]
    have : entries ops ((id, (casApply s m.input).2) ::
        (replayIds ops (casApply s m.input).1 ids).1) =
        (m.input, (casApply s m.input).2) :: entries ops (replayIds ops (casApply s m.input).1 ids).1 := by
      simp [entries, hm]
    rw [this]
    exact ⟨rfl, ih⟩

/-- The operations the frontier's move from `F` to `F'` linearizes, sorted by place and rank. -/
def newIds (ops : GMap OpId OpMeta) (F F' : PTag) : List OpId :=
  (ops.domList.filter (fun id => @decide (∃ m, ops.lookup id = some m ∧ qualP ops F' m ∧
    ¬ qualP ops F m) (Classical.propDecidable _))).mergeSort
    (fun a b => keyLeB (opKey ops a) (opKey ops b))

theorem mem_newIds {ops : GMap OpId OpMeta} {F F' : PTag} {id : OpId} :
    id ∈ newIds ops F F' ↔ ∃ m, ops.lookup id = some m ∧ qualP ops F' m ∧ ¬ qualP ops F m := by
  unfold newIds
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filter, GMap.mem_dom_list]
  constructor
  · rintro ⟨_, h⟩; exact @of_decide_eq_true _ (Classical.propDecidable _) h
  · rintro ⟨m, hm, h⟩
    exact ⟨by rw [hm]; rfl, @decide_eq_true _ (Classical.propDecidable _) ⟨m, hm, h⟩⟩

theorem newIds_nodup (ops : GMap OpId OpMeta) (F F' : PTag) : (newIds ops F F').Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.2 ((GMap.nodup_dom_list ops).filter _)

theorem newIds_sorted (ops : GMap OpId OpMeta) (F F' : PTag) :
    (newIds ops F F').Pairwise (fun a b => keyLeB (opKey ops a) (opKey ops b) = true) :=
  List.pairwise_mergeSort (le := fun a b => keyLeB (opKey ops a) (opKey ops b))
    (fun a b c => keyLeB_trans _ _ _) (fun a b => keyLeB_total _ _) _


theorem opKey_of {ops : GMap OpId OpMeta} {id : OpId} {m : OpMeta} {t : PTag}
    (hm : ops.lookup id = some m) (ht : m.place.tag? = some t) : opKey ops id = (t, rank m.input) := by
  simp [opKey, hm, ht]

/-- A store's register after an update: each of the three lookups grows. -/
theorem stores_insert_grow {stores : GMap Nat (w64 × PTag)} {k : Nat} {v v' : w64} {t t' : PTag}
    (hk : stores.lookup k = some (v, t)) (hlt : tagLt t t') (i : Nat) (x : w64 × PTag)
    (hx : stores.lookup i = some x) :
    ∃ x', (stores.insert k (v', t')).lookup i = some x' ∧ tagLe x.2 x'.2 := by
  by_cases e : k = i
  · subst e; rw [hk] at hx; cases hx
    exact ⟨(v', t'), GMap.lookup_insert _ _ _, tagLe_of_lt hlt⟩
  · exact ⟨x, by rw [GMap.lookup_insert_ne _ _ e]; exact hx, tagLe_refl _⟩

/-- **The pure core of `store_update`**: replica node `k`'s store moves from `(v, t)` to a greater
stored tag `t'`; the operations the frontier passes are appended to `lin` in place order (`new`,
whose replay from `σ` gives the new abstract state `σ'`), and every fact is preserved. -/
theorem store_update_pure {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)} {k : Nat} {v v' : w64}
    {t t' : PTag}
    (h : invFactsR σ stores tv lbs ops lin insts execS preds turns)
    (hk : stores.lookup k = some (v, t)) (htv : tv.lookup t' = some v') (hlt : tagLt t t') :
    ∃ (new : List (OpId × RegOutput w64)) (σ' : w64),
      (∀ x ∈ new, (ops.lookup x.1).isSome ∧ ∀ o, (x.1, o) ∉ lin) ∧ (new.map Prod.fst).Nodup ∧
      replayOk σ (entries ops new) σ' ∧
      invFactsR σ' (stores.insert k (v', t')) tv (lbs.insert (k, t') ()) ops (lin ++ new) insts
        execS preds turns := by
  obtain ⟨⟨a, b, c, ha, hb, hc, f_tv0, f_sv, f_lbs, f_σ, f_lin, f_t1, f_t2, f_prod, f_linops,
    f_nodup, f_ord, f_replay, f_hist, f_uniq, f_exec, f_chainS, f_chainP, f_pred1, f_pred2⟩,
    hx⟩ := h
  have hx' := hx
  obtain ⟨x_ge0, _, _⟩ := hx'
  -- the frontiers
  generalize hF : median3 a.2 b.2 c.2 = F at *
  obtain ⟨a', ha', haa⟩ := stores_insert_grow hk hlt 0 a ha (v' := v')
  obtain ⟨b', hb', hbb⟩ := stores_insert_grow hk hlt 1 b hb (v' := v')
  obtain ⟨c', hc', hcc⟩ := stores_insert_grow hk hlt 2 c hc (v' := v')
  have hFF : tagLe F (median3 a'.2 b'.2 c'.2) := hF ▸ median3_mono haa hbb hcc
  generalize hF' : median3 a'.2 b'.2 c'.2 = F' at hFF
  have hF0 : tagLe tag0 F := by
    rw [← hF]
    rcases median3_mem a.2 b.2 c.2 with e | e | e <;> rw [e]
    · exact x_ge0 _ _ (f_sv 0 a ha)
    · exact x_ge0 _ _ (f_sv 1 b hb)
    · exact x_ge0 _ _ (f_sv 2 c hc)
  -- the old linearization, in the non-recursive form
  have hchar : ∀ id m, ops.lookup id = some m → ((∃ o, (id, o) ∈ lin) ↔ qualP ops F m) := by
    have h0 := rank0_of_char (L := lin) (F := F) (P := linRHS ops F lin) f_lin
      (fun m hr => linRHS_rank0 m hr)
    exact fun id m hm => (f_lin id m hm).trans (linRHS_iff_qualP h0 m)
  -- the new operations
  let ids := newIds ops F F'
  let new := (replayIds ops σ ids).1
  let σ' := (replayIds ops σ ids).2
  have hfst : new.map Prod.fst = ids := replayIds_fst ops σ ids
  have hmem_new : ∀ x ∈ new, x.1 ∈ ids := fun x hx => hfst ▸ List.mem_map_of_mem hx
  have hmem_new' : ∀ id, id ∈ ids → ∃ o, (id, o) ∈ new := by
    intro id hid
    rw [← hfst] at hid
    obtain ⟨x, hx, e⟩ := List.mem_map.1 hid
    exact ⟨x.2, by rw [← e]; exact hx⟩
  have hids_ops : ∀ id ∈ ids, (ops.lookup id).isSome := by
    intro id hid
    obtain ⟨m, hm, _⟩ := mem_newIds.1 hid
    rw [hm]; rfl
  have hnew_notlin : ∀ x ∈ new, (ops.lookup x.1).isSome ∧ ∀ o, (x.1, o) ∉ lin := by
    intro x hx
    obtain ⟨m, hm, _, hq⟩ := mem_newIds.1 (hmem_new x hx)
    refine ⟨by rw [hm]; rfl, fun o ho => hq ((hchar x.1 m hm).1 ⟨o, ho⟩)⟩
  have hnew_nodup : (new.map Prod.fst).Nodup := hfst ▸ newIds_nodup ops F F'
  have hnew_replay : replayOk σ (entries ops new) σ' := replayIds_ok ops σ ids hids_ops
  -- the new linearization
  let L' := lin ++ new
  have hchar' : ∀ id m, ops.lookup id = some m → ((∃ o, (id, o) ∈ L') ↔ qualP ops F' m) := by
    intro id m hm
    constructor
    · rintro ⟨o, ho⟩
      rcases List.mem_append.1 ho with ho | ho
      · exact qualP_mono hFF ((hchar id m hm).1 ⟨o, ho⟩)
      · obtain ⟨m', hm', hq, _⟩ := mem_newIds.1 (hmem_new _ ho)
        simp only at hm'; rw [hm] at hm'; cases hm'; exact hq
    · intro hq
      by_cases hq0 : qualP ops F m
      · obtain ⟨o, ho⟩ := (hchar id m hm).2 hq0
        exact ⟨o, List.mem_append_left _ ho⟩
      · obtain ⟨o, ho⟩ := hmem_new' id (mem_newIds.2 ⟨m, hm, hq, hq0⟩)
        exact ⟨o, List.mem_append_right _ ho⟩
  -- every new operation is placed above `F`
  have hnew_above : ∀ x ∈ new, ∃ m tx, ops.lookup x.1 = some m ∧ m.place.tag? = some tx ∧
      tagLt F tx ∧ tagLe tx F' := by
    intro x hx
    obtain ⟨m, hm, hq, hq0⟩ := mem_newIds.1 (hmem_new x hx)
    obtain ⟨tx, htx, htF'⟩ := qualP_tag hq
    refine ⟨m, tx, hm, htx, ?_, htF'⟩
    rcases tagLt_or_le F tx with h | h
    · exact h
    · exact absurd (qualP_down hq htx h) hq0
  have hlin_below : ∀ x ∈ lin, ∃ m tx, ops.lookup x.1 = some m ∧ m.place.tag? = some tx ∧
      tagLe tx F := by
    intro x hx
    obtain ⟨m, hm⟩ := f_linops x.1 x.2 hx
    obtain ⟨tx, htx, htF⟩ := qualP_tag ((hchar x.1 m hm).1 ⟨x.2, hx⟩)
    exact ⟨m, tx, hm, htx, htF⟩
  have hL1 : ∀ x ∈ L', ∃ tx, ptag ops x.1 = some tx := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨m, tx, hm, htx, _⟩ := hlin_below x hx
      exact ⟨tx, by unfold ptag; rw [hm]; simpa using htx⟩
    · obtain ⟨m, tx, hm, htx, _⟩ := hnew_above x hx
      exact ⟨tx, by unfold ptag; rw [hm]; simpa using htx⟩
  -- `lin'` sorted by place
  have hnew_sorted : new.Pairwise (linOrd ops) := by
    have hs : ids.Pairwise (fun a b => keyLeB (opKey ops a) (opKey ops b) = true) :=
      newIds_sorted ops F F'
    rw [← hfst, List.pairwise_map] at hs
    refine List.Pairwise.imp_of_mem ?_ hs
    intro x y hx hy hxy
    obtain ⟨mx, tx, hmx, htx, _⟩ := hnew_above x hx
    obtain ⟨my, ty, hmy, hty, _⟩ := hnew_above y hy
    rw [opKey_of hmx htx, opKey_of hmy hty] at hxy
    unfold keyLeB at hxy
    exact ⟨mx, my, tx, ty, hmx, hmy, htx, hty, of_decide_eq_true hxy⟩
  have hL2 : L'.Pairwise (linOrd ops) := by
    refine List.pairwise_append.2 ⟨f_ord, hnew_sorted, ?_⟩
    intro x hx y hy
    obtain ⟨mx, tx, hmx, htx, hxF⟩ := hlin_below x hx
    obtain ⟨my, ty, hmy, hty, hFy, _⟩ := hnew_above y hy
    exact ⟨mx, my, tx, ty, hmx, hmy, htx, hty, Or.inl (tagLt_of_le_of_lt hxF hFy)⟩
  have hL3 : (L'.map Prod.fst).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨f_nodup, hnew_nodup, ?_⟩
    intro i hi j hj e
    subst e
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hi
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hj
    exact (hnew_notlin y hy).2 x.2 (by rw [e]; exact hx)
  have hL5 : replayOk (W64 0) (entries ops L') σ' := by
    rw [entries_append]
    exact (replayOk_append _ _ _ _).2 ⟨σ, f_replay, hnew_replay⟩
  -- the history
  have hpre_old : ∀ t0, tagLe t0 F → preT ops L' t0 = preT ops lin t0 := by
    intro t0 ht0
    rw [preT_append]
    have : preT ops new t0 = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro x hx
      obtain ⟨hx, tx, h1, h2⟩ := mem_preT.1 hx
      obtain ⟨m, tx', hm, htx', hFx, _⟩ := hnew_above x hx
      unfold ptag at h1; rw [hm] at h1; simp only [Option.bind_some] at h1
      rw [htx'] at h1; cases h1
      exact (not_tagLe_iff _ _).2 (tagLt_of_le_of_lt ht0 hFx) h2
    rw [this, List.append_nil]
  have hhist : ∀ t0 v0, tv.lookup t0 = some v0 → tagLe t0 F' →
      replayOk (W64 0) (entries ops (preT ops L' t0)) v0 := by
    refine history_extend ops tv insts execS L' F F' σ' hL1 hL2 hL3 hL5 ?_ f_uniq ?_ hF0 hx
      f_exec f_chainS
    · intro id m x freg hm hr hpl hf hxF
      exact (hchar' id m hm).2 ((qualP_rank0 m hr).2 ⟨x, freg, hpl, hf, hxF⟩)
    · intro t0 v0 ht0 hle
      rw [hpre_old t0 hle]
      exact f_hist t0 v0 ht0 hle
  -- the new stores
  have hsv' : ∀ k' vt, (stores.insert k (v', t')).lookup k' = some vt → tv.lookup vt.2 = some vt.1 := by
    intro k' vt h'
    by_cases e : k = k'
    · subst e; rw [GMap.lookup_insert] at h'; cases h'; exact htv
    · rw [GMap.lookup_insert_ne _ _ e] at h'; exact f_sv k' vt h'
  have hF'stored : ∃ vF, tv.lookup F' = some vF := by
    rw [← hF']
    rcases median3_mem a'.2 b'.2 c'.2 with e | e | e <;> rw [e]
    · exact ⟨_, hsv' 0 a' ha'⟩
    · exact ⟨_, hsv' 1 b' hb'⟩
    · exact ⟨_, hsv' 2 c' hc'⟩
  obtain ⟨vF, hvF⟩ := hF'stored
  have hσ' : tv.lookup F' = some σ' := by
    have h1 := hhist F' vF hvF (tagLe_refl _)
    have hall : preT ops L' F' = L' := by
      unfold preT
      rw [List.filter_eq_self]
      intro x hx
      obtain ⟨tx, htx⟩ := hL1 x hx
      have htx' : (ops.lookup x.1).bind (fun m => m.place.tag?) = some tx := htx
      rw [htx']
      simp only [decide_eq_true_eq]
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨m, tx', hm, htx'', hle⟩ := hlin_below x hx
        unfold ptag at htx; rw [hm] at htx; simp only [Option.bind_some] at htx
        rw [htx''] at htx; cases htx; exact tagLe_trans hle hFF
      · obtain ⟨m, tx', hm, htx'', _, hle⟩ := hnew_above x hx
        unfold ptag at htx; rw [hm] at htx; simp only [Option.bind_some] at htx
        rw [htx''] at htx; cases htx; exact hle
    rw [hall] at h1
    rw [hvF, replayOk_det hL5 h1]
  refine ⟨new, σ', hnew_notlin, hnew_nodup, hnew_replay, ?_, hx⟩
  refine ⟨a', b', c', ha', hb', hc', ?_⟩
  simp only [hF']
  refine ⟨f_tv0, hsv', ?_, hσ', ?_, f_t1, ?_, f_prod, ?_, hL3, hL2, hL5, ?_, f_uniq, f_exec,
    f_chainS, f_chainP, f_pred1, f_pred2⟩
  · -- the stores' lower bounds
    intro k' t0 h'
    by_cases e : (k, t') = (k', t0)
    · cases e; exact ⟨(v', t'), GMap.lookup_insert _ _ _, tagLe_refl _⟩
    · rw [GMap.lookup_insert_ne _ _ e] at h'
      obtain ⟨vt, hvt, hle⟩ := f_lbs k' t0 h'
      by_cases e' : k = k'
      · subst e'; rw [hk] at hvt; cases hvt
        exact ⟨(v', t'), GMap.lookup_insert _ _ _, tagLe_trans hle (tagLe_of_lt hlt)⟩
      · exact ⟨vt, by rw [GMap.lookup_insert_ne _ _ e']; exact hvt, hle⟩
  · -- the linearization fact
    have h0 := rank0_of_char (L := L') (F := F') (P := qualP ops F') hchar'
      (fun m hr => qualP_rank0 m hr)
    exact fun id m hm => (hchar' id m hm).trans (linRHS_iff_qualP h0 m).symm
  · intro cid r1 r2 hlt' h1 h2
    obtain ⟨o, ho⟩ := f_t2 cid r1 r2 hlt' h1 h2
    exact ⟨o, List.mem_append_left _ ho⟩
  · intro id o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact f_linops id o ho
    · exact Option.isSome_iff_exists.1 (hnew_notlin _ ho).1
  · exact hhist


/-! ## The commit witnesses (`opDone_intro_*`) -/

/-- Two stores (of the three) at or above `t` put the frontier at or above `t`. -/
theorem frontier_ge_of_two {stores : GMap Nat (w64 × PTag)} {a b c : w64 × PTag}
    (ha : stores.lookup 0 = some a) (hb : stores.lookup 1 = some b)
    (hc : stores.lookup 2 = some c) {k1 k2 : Nat} (hk : k1 ≠ k2) (hk1 : k1 < 3) (hk2 : k2 < 3)
    {t : PTag} {x1 x2 : w64 × PTag} (h1 : stores.lookup k1 = some x1) (h2 : stores.lookup k2 = some x2)
    (hx1 : tagLe t x1.2) (hx2 : tagLe t x2.2) : tagLe t (median3 a.2 b.2 c.2) := by
  apply le_median3_of_two
  have g : ∀ k x, k < 3 → stores.lookup k = some x → tagLe t x.2 →
      (k = 0 ∧ tagLe t a.2) ∨ (k = 1 ∧ tagLe t b.2) ∨ (k = 2 ∧ tagLe t c.2) := by
    intro k x hk h hx
    match k, hk with
    | 0, _ => rw [ha] at h; cases h; exact Or.inl ⟨rfl, hx⟩
    | 1, _ => rw [hb] at h; cases h; exact Or.inr (Or.inl ⟨rfl, hx⟩)
    | 2, _ => rw [hc] at h; cases h; exact Or.inr (Or.inr ⟨rfl, hx⟩)
  rcases g k1 x1 hk1 h1 hx1 with ⟨e1, g1⟩ | ⟨e1, g1⟩ | ⟨e1, g1⟩ <;>
    rcases g k2 x2 hk2 h2 hx2 with ⟨e2, g2⟩ | ⟨e2, g2⟩ | ⟨e2, g2⟩ <;>
    first
    | exact absurd (e1.trans e2.symm) hk
    | exact Or.inl ⟨g1, g2⟩ | exact Or.inl ⟨g2, g1⟩
    | exact Or.inr (Or.inl ⟨g1, g2⟩) | exact Or.inr (Or.inl ⟨g2, g1⟩)
    | exact Or.inr (Or.inr ⟨g1, g2⟩) | exact Or.inr (Or.inr ⟨g2, g1⟩)

/-- A linearized operation's output is its input's step from some state. -/
theorem replayOk_output (ops : GMap OpId OpMeta) :
    ∀ (L : List (OpId × RegOutput w64)) (s s' : w64), replayOk s (entries ops L) s' →
      ∀ id o m, (id, o) ∈ L → ops.lookup id = some m → ∃ s0, (casApply s0 m.input).2 = o
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | x :: L, s, s', h, id, o, m, hx, hm => by
    cases hmx : ops.lookup x.1 with
    | none =>
      have : entries ops (x :: L) = entries ops L := by simp [entries, hmx]
      rw [this] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hm] at hmx; cases hmx
      · exact replayOk_output ops L s s' h id o m hx hm
    | some mx =>
      have : entries ops (x :: L) = (mx.input, x.2) :: entries ops L := by simp [entries, hmx]
      rw [this] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hm] at hmx; cases hmx; exact ⟨s, h.1⟩
      · exact replayOk_output ops L _ s' h.2 id o m hx hm

/-- The facts' linearization characterization (from `invFacts`). -/
theorem invFacts_char {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)} {a b c : w64 × PTag}
    (ha : stores.lookup 0 = some a) (hb : stores.lookup 1 = some b) (hc : stores.lookup 2 = some c)
    (h : invFactsCore σ stores tv lbs ops lin insts execS preds turns) :
    ∀ id m, ops.lookup id = some m →
      ((∃ o, (id, o) ∈ lin) ↔ qualP ops (median3 a.2 b.2 c.2) m) := by
  obtain ⟨a', b', c', ha', hb', hc', -, -, -, -, f_lin, -⟩ := h
  rw [ha] at ha'; rw [hb] at hb'; rw [hc] at hc'
  cases ha'; cases hb'; cases hc'
  have h0 := rank0_of_char (P := linRHS ops _ lin) f_lin (fun m hr => linRHS_rank0 m hr)
  exact fun id m hm => (f_lin id m hm).trans (linRHS_iff_qualP h0 m)

/-- **`opDone_intro_update`'s pure core**: a write or an RMW placed at `t` (from a frontier at or
below `t`) with two of the three stores at or above `t` is linearized, with output `.done`. -/
theorem opDone_update_pure {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)}
    (h : invFactsCore σ stores tv lbs ops lin insts execS preds turns)
    {id : OpId} {m : OpMeta} {t freg : PTag} {k1 k2 : Nat}
    (hm : ops.lookup id = some m) (hi : m.input ≠ .read) (hpl : m.place = .placed (some t) freg)
    (hf : tagLe freg t) (hk : k1 ≠ k2) (hk1 : k1 < 3) (hk2 : k2 < 3)
    (hl1 : lbs.lookup (k1, t) = some ()) (hl2 : lbs.lookup (k2, t) = some ()) :
    (id, RegOutput.done) ∈ lin := by
  have h' := h
  obtain ⟨a, b, c, ha, hb, hc, -, -, f_lbs, -, -, -, -, -, -, -, -, f_replay, -⟩ := h'
  obtain ⟨x1, hx1, hle1⟩ := f_lbs k1 t hl1
  obtain ⟨x2, hx2, hle2⟩ := f_lbs k2 t hl2
  have hF := frontier_ge_of_two ha hb hc hk hk1 hk2 hx1 hx2 hle1 hle2
  have hr : rank m.input = 0 := by cases hmi : m.input <;> simp_all [rank]
  obtain ⟨o, ho⟩ := (invFacts_char ha hb hc h id m hm).2
    ((qualP_rank0 m hr).2 ⟨t, freg, hpl, hf, hF⟩)
  obtain ⟨s0, hs0⟩ := replayOk_output ops lin _ _ f_replay id o m ho hm
  have : o = .done := by
    rw [← hs0]; cases hmi : m.input with
    | read => exact absurd hmi hi
    | write v => rfl
    | cas o n => rfl
  subst this; exact ho


theorem replayOk_reads_out (ops : GMap OpId OpMeta) :
    ∀ (R : List (OpId × RegOutput w64)) (s s' : w64),
      (∀ y ∈ R, ∃ m, ops.lookup y.1 = some m ∧ m.input = .read) →
      replayOk s (entries ops R) s' → s' = s ∧ ∀ x ∈ R, x.2 = .value s
  | [], s, s', _, h => ⟨h, by simp⟩
  | y :: R, s, s', hr, h => by
    obtain ⟨m, hm, hi⟩ := hr y (List.mem_cons_self ..)
    have : entries ops (y :: R) = (m.input, y.2) :: entries ops R := by simp [entries, hm]
    rw [this, hi] at h
    obtain ⟨h1, h2⟩ := h
    simp only [casApply] at h1 h2
    obtain ⟨e, hall⟩ := replayOk_reads_out ops R s s' (fun z hz => hr z (List.mem_cons_of_mem _ hz)) h2
    refine ⟨e, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1.symm
    · exact hall x hx

/-- **`opDone_intro_read`'s pure core** (with H-U4-2's facts): a read placed at a stored tag `t`
(from a frontier at or below `t`) with two of the three stores at or above `t` is linearized, and
returns `t`'s value. -/
theorem opDone_read_pure {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)}
    (h : invFactsR σ stores tv lbs ops lin insts execS preds turns)
    {id : OpId} {m : OpMeta} {t freg : PTag} {k1 k2 : Nat} {v : w64}
    (hm : ops.lookup id = some m) (hi : m.input = .read) (hpl : m.place = .placed (some t) freg)
    (hf : tagLe freg t) (hk : k1 ≠ k2) (hk1 : k1 < 3) (hk2 : k2 < 3)
    (hl1 : lbs.lookup (k1, t) = some ()) (hl2 : lbs.lookup (k2, t) = some ())
    (htv : tv.lookup t = some v) :
    (id, RegOutput.value v) ∈ lin := by
  obtain ⟨hI, -, hprod, -⟩ := h
  have hI' := hI
  obtain ⟨a, b, c, ha, hb, hc, -, -, f_lbs, -, -, -, -, -, f_linops, f_nodup, f_ord, f_replay,
    f_hist, f_uniq, -⟩ := hI'
  have hchar := invFacts_char ha hb hc hI
  generalize hF : median3 a.2 b.2 c.2 = F at hchar f_hist
  obtain ⟨x1, hx1, hle1⟩ := f_lbs k1 t hl1
  obtain ⟨x2, hx2, hle2⟩ := f_lbs k2 t hl2
  have htF : tagLe t F := hF ▸ frontier_ge_of_two ha hb hc hk hk1 hk2 hx1 hx2 hle1 hle2
  -- the read qualifies: its tag is `tag0` or its producer qualifies
  have hq : qualP ops F m := by
    refine ⟨t, freg, hpl, hf, htF, ?_⟩
    by_cases ht0 : t = tag0
    · exact Or.inr (Or.inl ht0)
    · obtain ⟨id', m', freg', hm', hpl', hf', hin⟩ := hprod t v htv ht0
      have hr' : rank m'.input = 0 := by
        rcases hin with e | ⟨_, _, _, _, _, _, _, e⟩ <;> rw [e] <;> rfl
      exact Or.inr (Or.inr ⟨id', m', freg', hm', hr', hpl', hf'⟩)
  obtain ⟨o, ho⟩ := (hchar id m hm).2 hq
  -- its output is the state after the operations placed at or below `t`
  have hL1 : ∀ x ∈ lin, ∃ tx, ptag ops x.1 = some tx := by
    intro x hx
    obtain ⟨mx, hmx⟩ := f_linops x.1 x.2 hx
    obtain ⟨tx, htx, _⟩ := qualP_tag ((hchar x.1 mx hmx).1 ⟨x.2, hx⟩)
    exact ⟨tx, by unfold ptag; rw [hmx]; simpa using htx⟩
  have hsplit := preT_eq_lt_eq ops t lin hL1 f_ord
  have hpre : replayOk (W64 0) (entries ops (preT ops lin t)) v := f_hist t v htv htF
  rw [hsplit, entries_append] at hpre
  obtain ⟨s1, hs1, hs2⟩ := (replayOk_append _ _ _ _).1 hpre
  have hptag : ptag ops id = some t := by unfold ptag; rw [hm]; simp [hpl, Placement.tag?]
  have hinE : (id, o) ∈ eqT ops lin t := by unfold eqT; simp [ho, hptag]
  by_cases hP : ∃ P ∈ eqT ops lin t, ∃ mP, ops.lookup P.1 = some mP ∧ rank mP.input = 0
  · obtain ⟨P, hPE, mP, hmP, hrP⟩ := hP
    have hPE' : P ∈ lin ∧ ptag ops P.1 = some t := by unfold eqT at hPE; simpa using hPE
    have hPt : mP.place.tag? = some t := by
      have := hPE'.2; unfold ptag at this; rw [hmP] at this; simpa using this
    obtain ⟨rest, hE, hreads⟩ := eqT_struct ops lin t f_ord f_nodup f_uniq P mP hPE'.1 hmP hPt hrP
    rw [hE] at hs2 hinE
    have : entries ops (P :: rest) = (mP.input, P.2) :: entries ops rest := by
      simp [entries, hmP]
    rw [this] at hs2
    obtain ⟨-, hs3⟩ := hs2
    obtain ⟨e, hall⟩ := replayOk_reads_out ops rest _ _ hreads hs3
    rcases List.mem_cons.1 hinE with e' | hin
    · rw [← e'] at hmP; simp only at hmP; rw [hm] at hmP; cases hmP; rw [hi] at hrP
      exact absurd hrP (by decide)
    · have := hall _ hin; simp only at this; rw [e, ← this]; exact ho
  · have hreads : ∀ y ∈ eqT ops lin t, ∃ m, ops.lookup y.1 = some m ∧ m.input = .read := by
      intro y hy
      have hy' : y ∈ lin ∧ ptag ops y.1 = some t := by unfold eqT at hy; simpa using hy
      obtain ⟨my, hmy⟩ := f_linops y.1 y.2 hy'.1
      exact ⟨my, hmy, rank_ne_zero fun hr => hP ⟨y, hy, my, hmy, hr⟩⟩
    obtain ⟨e, hall⟩ := replayOk_reads_out ops _ _ _ hreads hs2
    have := hall _ hinE; simp only at this; rw [e, ← this]; exact ho

end Perennial.gryff
