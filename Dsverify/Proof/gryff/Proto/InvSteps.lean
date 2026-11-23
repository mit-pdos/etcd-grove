/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/InvSteps.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The pure steps of the invariant's laws (U4): registering an operation (`op_begin`), fixing its
place (`op_place`), claiming its commit (`op_end`), each preserving `invFactsB`, `opsJoin` and
`connFacts`.
-/
module

public import Dsverify.Proof.gryff.Proto.InvPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open proto dsverify_lab.harness

/-- When `op_place` records a predicted place `t` from the frontier `freg` (a read at or above
it; a write strictly above it, at its own client id with `rmwc = 0`; an RMW strictly above it with
`rmwc ≥ 1`). -/
def placeOk (i : RegInput w64) (id : OpId) (freg t : PTag) : Prop :=
  match i with
  | .read => tagLe freg t
  | .write _ => tagLt freg t ∧ t.2.1 = id.1 ∧ t.2.2 = 0
  | .cas _ _ => tagLt freg t ∧ 1 ≤ t.2.2

/-- The place `op_place` records for prediction `p` (`q`): the prediction, or `none` when it is
not `placeOk` (or, for an RMW, when its place is another operation's: D6). -/
def placeRec (i : RegInput w64) (id : OpId) (freg : PTag) (p q : Option PTag) : Prop :=
  q = p ∨ (q = none ∧ ∀ t, p = some t → ¬ placeOk i id freg t ∨ ∃ o n, i = .cas o n)

/-- All the invariant's pure facts. -/
def allFacts (σ : w64) (stores : GMap Nat (w64 × PTag)) (tv : GMap PTag w64)
    (lbs : GMap (Nat × PTag) Unit) (ops : GMap OpId OpMeta) (info : GMap OpId OpInfo)
    (places : GMap OpId Placement) (lin : List (OpId × RegOutput w64))
    (insts : GMap (Int × Int) InstAttrs) (execS : List ExecEntry)
    (preds : GMap Nat (List ExecEntry)) (turns : GMap Int (Int × Bool))
    (conns : GMap w32 (Option w64)) (placers : GMap w64 Int) : Prop :=
  invFactsB σ stores tv lbs ops lin insts execS preds turns ∧ opsJoin ops info places ∧
    connFacts conns placers places

theorem entries_congr {ops ops' : GMap OpId OpMeta} :
    ∀ {L : List (OpId × RegOutput w64)}, (∀ x ∈ L, ops'.lookup x.1 = ops.lookup x.1) →
      entries ops' L = entries ops L
  | [], _ => rfl
  | x :: L, h => by
    have ih := entries_congr (L := L) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [entries, List.filterMap_cons] at ih ⊢
    rw [h x (List.mem_cons_self ..), ih]

theorem preT_congr {ops ops' : GMap OpId OpMeta} {L : List (OpId × RegOutput w64)} (t : PTag)
    (h : ∀ x ∈ L, ops'.lookup x.1 = ops.lookup x.1) : preT ops' L t = preT ops L t := by
  unfold preT
  exact List.filter_congr (fun x hx => by rw [h x hx])

/-! ## Changing one operation that is not linearized -/

/-- Changing `ops` at one operation `id` that is not linearized and was not placed (absent or
`unplaced`), to `m'` (not qualifying, its place not another rank-0 operation's, consistent with
the chain), keeps the facts that do not mention the turns. The turn facts are given for the new
map (`ht1`, `ht2`, `hb3`). -/
theorem core_change {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops ops' : GMap OpId OpMeta} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns turns' : GMap Int (Int × Bool)}
    (h : invFactsB σ stores tv lbs ops lin insts execS preds turns)
    (id : OpId) (m' : OpMeta)
    (hne : ∀ id', id' ≠ id → ops'.lookup id' = ops.lookup id')
    (hid : ops'.lookup id = some m')
    (hold : ∀ m, ops.lookup id = some m → m.place = .unplaced)
    (hnl : ∀ o, (id, o) ∉ lin)
    (hnq : ∀ a b c : w64 × PTag, stores.lookup 0 = some a → stores.lookup 1 = some b →
      stores.lookup 2 = some c → ¬ ∃ t freg, m'.place = .placed (some t) freg ∧ tagLe freg t ∧
      tagLe t (median3 a.2 b.2 c.2) ∧
      (rank m'.input = 0 ∨ t = tag0 ∨ ∃ id' m'' o', ops'.lookup id' = some m'' ∧
        rank m''.input = 0 ∧ m''.place.tag? = some t ∧ (id', o') ∈ lin))
    (huq : ∀ id2 m2 t, id2 ≠ id → ops.lookup id2 = some m2 → m'.place.tag? = some t →
      m2.place.tag? = some t → rank m'.input = 0 → rank m2.input = 0 → False)
    (hch : ∀ e a, e ∈ execS → insts.lookup e.inst = some a → a.op = id →
      m'.place.tag? = some e.res.2)
    (ht1 : ∀ cid r b r', turns'.lookup cid = some (r, b) → (ops'.lookup (cid, r')).isSome → r' < r)
    (ht2 : ∀ cid r1 r2, r1 < r2 → (ops'.lookup (cid, r1)).isSome →
      (ops'.lookup (cid, r2)).isSome → ∃ o, ((cid, r1), o) ∈ lin)
    (hb3 : ∀ cid r r', turns'.lookup cid = some (r, false) → (ops'.lookup (cid, r')).isSome →
      ∃ o, ((cid, r'), o) ∈ lin) :
    invFactsB σ stores tv lbs ops' lin insts execS preds turns' := by
  obtain ⟨⟨a, b, c, ha, hb, hc, f_tv0, f_sv, f_lbs, f_σ, f_lin, _, _, f_prod, f_linops,
    f_nodup, f_ord, f_replay, f_hist, f_uniq, f_exec, f_chainS, f_chainP, f_pred1, f_pred2⟩,
    ⟨x1, x2, x3⟩, ⟨b1, b2, _⟩⟩ := h
  -- lin's operations are not `id`, so their lookups are unchanged
  have hlinne : ∀ x ∈ lin, x.1 ≠ id := fun x hx e => hnl x.2 (by rw [← e]; exact hx)
  have hlk : ∀ x ∈ lin, ops'.lookup x.1 = ops.lookup x.1 := fun x hx => hne _ (hlinne x hx)
  -- an operation with a tag in the old map is not `id`
  have htag_ne : ∀ id2 m2 t, ops.lookup id2 = some m2 → m2.place.tag? = some t → id2 ≠ id := by
    intro id2 m2 t h2 ht e; subst e
    rw [hold m2 h2] at ht; cases ht
  refine ⟨⟨a, b, c, ha, hb, hc, f_tv0, f_sv, f_lbs, f_σ, ?_, ht1, ht2, ?_, ?_, f_nodup, ?_, ?_, ?_,
    ?_, f_exec, f_chainS, ?_, f_pred1, f_pred2⟩, ⟨x1, ?_, x3⟩, ⟨b1, b2, hb3⟩⟩
  · -- the linearization fact
    intro id2 m2 hm2
    by_cases e : id2 = id
    · subst e
      rw [hid] at hm2; cases hm2
      exact ⟨fun ⟨o, ho⟩ => absurd ho (hnl o), fun h' => absurd h' (hnq a b c ha hb hc)⟩
    · rw [hne _ e] at hm2
      rw [f_lin id2 m2 hm2]
      apply exists_congr; intro t; apply exists_congr; intro freg
      apply and_congr_right; intro _; apply and_congr_right; intro _; apply and_congr_right
      intro _; apply or_congr_right; apply or_congr_right
      constructor
      · rintro ⟨id', m'', o', h1, h2, h3, h4⟩
        exact ⟨id', m'', o', by rw [hne _ (htag_ne _ _ _ h1 h3)]; exact h1, h2, h3, h4⟩
      · rintro ⟨id', m'', o', h1, h2, h3, h4⟩
        have hne' : id' ≠ id := hlinne _ h4
        exact ⟨id', m'', o', by rw [← hne _ hne']; exact h1, h2, h3, h4⟩
  · -- producers
    intro t v ht ht0
    obtain ⟨id2, m2, h1, h2, h3⟩ := f_prod t v ht ht0
    exact ⟨id2, m2, by rw [hne _ (htag_ne _ _ _ h1 h2)]; exact h1, h2, h3⟩
  · intro id2 o ho
    rw [hne _ (hlinne _ ho)]; exact f_linops id2 o ho
  · refine List.Pairwise.imp_of_mem ?_ f_ord
    intro x y hx hy ⟨mx, my, tx, ty, h1, h2, h3, h4, h5⟩
    exact ⟨mx, my, tx, ty, by rw [hlk x hx]; exact h1, by rw [hlk y hy]; exact h2, h3, h4, h5⟩
  · show replayOk (W64 0) (entries ops' lin) σ
    rw [entries_congr hlk]; exact f_replay
  · intro t v ht hle
    show replayOk (W64 0) (entries ops' (preT ops' lin t)) v
    rw [preT_congr t hlk, entries_congr (fun x hx => hlk x (mem_preT.1 hx).1)]
    exact f_hist t v ht hle
  · intro id1 id2 m1 m2 t h1 h2 ht1' ht2' hr1 hr2
    by_cases e1 : id1 = id <;> by_cases e2 : id2 = id
    · rw [e1, e2]
    · subst e1; rw [hid] at h1; cases h1; rw [hne _ e2] at h2
      exact (huq id2 m2 t e2 h2 ht1' ht2' hr1 hr2).elim
    · subst e2; rw [hid] at h2; cases h2; rw [hne _ e1] at h1
      exact (huq id1 m1 t e1 h1 ht2' ht1' hr2 hr1).elim
    · rw [hne _ e1] at h1; rw [hne _ e2] at h2
      exact f_uniq id1 id2 m1 m2 t h1 h2 ht1' ht2' hr1 hr2
  · intro e a' m2 he ha' hm2
    by_cases eq : a'.op = id
    · rw [eq, hid] at hm2; cases hm2; exact hch e a' he ha' eq
    · rw [hne _ eq] at hm2; exact f_chainP e a' m2 he ha' hm2
  · intro t v ht ht0
    obtain ⟨id2, m2, freg, h1, h2, h3, h4⟩ := x2 t v ht ht0
    have hne2 : id2 ≠ id := htag_ne _ _ t h1 (by rw [h2]; rfl)
    exact ⟨id2, m2, freg, by rw [hne _ hne2]; exact h1, h2, h3, h4⟩


/-- The registered-operation map's join entry. -/
abbrev joinMeta (n : OpInfo) (pl : Placement) : OpMeta := ⟨n.input, pl, n.au, n.rcpt, n.claim⟩

theorem ops_lookup_join {ops : GMap OpId OpMeta} {info : GMap OpId OpInfo}
    {places : GMap OpId Placement} (hj : opsJoin ops info places) (id : OpId) :
    ops.lookup id = (info.lookup id).map (fun n => joinMeta n ((places.lookup id).getD .unplaced)) :=
  hj.1 id

/-- **`op_begin`'s pure step**: registering `(cid, req)` (the turn `(r, false)`, `r ≤ req`) with
its names `n` keeps every fact; the turn becomes `(req + 1, true)`. `hreg` is hub request H-U4-9's
fact (every chain entry's operation is registered). -/
theorem op_begin_pure {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {info : GMap OpId OpInfo}
    {places : GMap OpId Placement} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)}
    {conns : GMap w32 (Option w64)} {placers : GMap w64 Int}
    (h : allFacts σ stores tv lbs ops info places lin insts execS preds turns conns placers)
    (cid r req : Int) (hr : r ≤ req) (hturn : turns.lookup cid = some (r, false)) (n : OpInfo)
    (hreg : ∀ e a, e ∈ execS → insts.lookup e.inst = some a → (ops.lookup a.op).isSome) :
    info.lookup (cid, req) = none ∧
    allFacts σ stores tv lbs (ops.insert (cid, req) (joinMeta n .unplaced))
      (info.insert (cid, req) n) places lin insts execS preds (turns.insert cid (req + 1, true))
      conns placers := by
  obtain ⟨hI, hj, hc⟩ := h
  have hI' := hI
  obtain ⟨⟨a, b, c, ha, hb, hc', _, _, _, _, _, f_t1, f_t2, _, f_linops, _⟩, _, ⟨_, _, b3⟩⟩ := hI'
  have hops : ops.lookup (cid, req) = none := by
    cases e : ops.lookup (cid, req) with
    | none => rfl
    | some m => have := f_t1 cid r false req hturn (by rw [e]; rfl); omega
  have hinfo : info.lookup (cid, req) = none := by
    rw [ops_lookup_join hj] at hops
    cases e : info.lookup (cid, req) with
    | none => rfl
    | some _ => rw [e] at hops; simp at hops
  have hplace : places.lookup (cid, req) = none := by
    cases e : places.lookup (cid, req) with
    | none => rfl
    | some _ => have := hj.2 (cid, req) (by rw [e]; rfl); rw [hinfo] at this; simp at this
  refine ⟨hinfo, ?_, ?_, hc⟩
  · refine core_change hI (cid, req) (joinMeta n .unplaced) (fun id' e => ?_)
      (GMap.lookup_insert _ _ _) (fun m hm => by rw [hops] at hm; cases hm)
      (fun o ho => by obtain ⟨m, hm⟩ := f_linops _ o ho; rw [hops] at hm; cases hm)
      (fun _ _ _ _ _ _ ⟨t, freg, hpl, _⟩ => by simp [joinMeta] at hpl)
      (fun _ _ t _ _ ht => by simp [joinMeta, Placement.tag?] at ht)
      (fun e a he ha' hop => by
        have := hreg e a he ha'; rw [hop, hops] at this; cases this) ?_ ?_ ?_
    · exact GMap.lookup_insert_ne _ _ (Ne.symm e)
    · intro cid' r' b' r'' ht hs
      by_cases ec : cid = cid'
      · subst ec
        rw [GMap.lookup_insert] at ht; cases ht
        by_cases er : (cid, req) = (cid, r'')
        · cases er; omega
        · rw [GMap.lookup_insert_ne _ _ er] at hs
          have := f_t1 cid r false r'' hturn hs; omega
      · rw [GMap.lookup_insert_ne _ _ ec] at ht
        have er : (cid, req) ≠ (cid', r'') := fun e => ec (Prod.mk.inj e).1
        rw [GMap.lookup_insert_ne _ _ er] at hs
        exact f_t1 cid' r' b' r'' ht hs
    · intro c' r1 r2 hlt h1 h2
      by_cases e1 : (cid, req) = (c', r1)
      · cases e1
        have e2 : (cid, req) ≠ (cid, r2) := fun e => by cases e; omega
        rw [GMap.lookup_insert_ne _ _ e2] at h2
        have := f_t1 cid r false r2 hturn h2; omega
      · rw [GMap.lookup_insert_ne _ _ e1] at h1
        by_cases e2 : (cid, req) = (c', r2)
        · cases e2; exact b3 cid r r1 hturn h1
        · rw [GMap.lookup_insert_ne _ _ e2] at h2
          exact f_t2 c' r1 r2 hlt h1 h2
    · intro c' r' r'' ht hs
      by_cases ec : cid = c'
      · subst ec; rw [GMap.lookup_insert] at ht; cases ht
      · rw [GMap.lookup_insert_ne _ _ ec] at ht
        have er : (cid, req) ≠ (c', r'') := fun e => ec (Prod.mk.inj e).1
        rw [GMap.lookup_insert_ne _ _ er] at hs
        exact b3 c' r' r'' ht hs
  · refine ⟨fun id' => ?_, fun id' hs => ?_⟩
    · by_cases e : (cid, req) = id'
      · subst e; rw [GMap.lookup_insert, GMap.lookup_insert, hplace]; rfl
      · rw [GMap.lookup_insert_ne _ _ e, GMap.lookup_insert_ne _ _ e]; exact hj.1 id'
    · by_cases e : (cid, req) = id'
      · subst e; rw [GMap.lookup_insert]; rfl
      · rw [GMap.lookup_insert_ne _ _ e]; exact hj.2 id' hs


/-- **`op_end`'s pure step**: a linearized request `(cid, req)` whose turn is pending
(`(req + 1, true)`) gives the turn back (`(req + 1, false)`). -/
theorem op_end_pure {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {info : GMap OpId OpInfo}
    {places : GMap OpId Placement} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)}
    {conns : GMap w32 (Option w64)} {placers : GMap w64 Int}
    (h : allFacts σ stores tv lbs ops info places lin insts execS preds turns conns placers)
    (cid req : Int) (o : RegOutput w64) (hturn : turns.lookup cid = some (req + 1, true))
    (hreg : (ops.lookup (cid, req)).isSome) (hlin : ((cid, req), o) ∈ lin) :
    allFacts σ stores tv lbs ops info places lin insts execS preds
      (turns.insert cid (req + 1, false)) conns placers := by
  obtain ⟨⟨⟨a, b, c, ha, hb, hc, f1, f2, f3, f4, f5, f_t1, f_t2, rest⟩, hx, ⟨b1, b2, b3⟩⟩, hj, hcn⟩ := h
  refine ⟨⟨⟨a, b, c, ha, hb, hc, f1, f2, f3, f4, f5, ?_, f_t2, rest⟩, hx, ⟨b1, b2, ?_⟩⟩, hj, hcn⟩
  · intro cid' r b' r' ht hs
    by_cases e : cid = cid'
    · subst e; rw [GMap.lookup_insert] at ht; cases ht
      exact f_t1 cid _ true r' hturn hs
    · rw [GMap.lookup_insert_ne _ _ e] at ht; exact f_t1 cid' r b' r' ht hs
  · intro cid' r r' ht hs
    by_cases e : cid = cid'
    · subst e; rw [GMap.lookup_insert] at ht; cases ht
      have hlt := f_t1 cid _ true r' hturn hs
      by_cases er : r' = req
      · subst er; exact ⟨o, hlin⟩
      · exact f_t2 cid r' req (by omega) hs hreg
    · rw [GMap.lookup_insert_ne _ _ e] at ht; exact b3 cid' r r' ht hs


/-! ## `op_place` -/

/-- H-U4-9's fact survives any insertion into `ops`. -/
theorem chainReg_insert {ops : GMap OpId OpMeta} {insts : GMap (Int × Int) InstAttrs}
    {execS : List ExecEntry} (h : chainReg ops insts execS) (id : OpId) (m : OpMeta) :
    chainReg (ops.insert id m) insts execS := by
  intro e a he ha
  by_cases e' : id = a.op
  · rw [e', GMap.lookup_insert]; rfl
  · rw [GMap.lookup_insert_ne _ _ e']; exact h e a he ha

/-- H-U4-10's fact survives registering an unplaced operation. -/
theorem placeShapes_insert_unplaced {ops : GMap OpId OpMeta} (h : placeShapes ops) (id : OpId)
    (n : OpInfo) : placeShapes (ops.insert id (joinMeta n .unplaced)) := by
  intro id' m t hm ht
  by_cases e : id = id'
  · subst e; rw [GMap.lookup_insert] at hm; cases hm
    simp [joinMeta, Placement.tag?] at ht
  · rw [GMap.lookup_insert_ne _ _ e] at hm; exact h id' m t hm ht

open Classical in
/-- The place `op_place` records for the prediction `p` at the frontier `F`. -/
def recPlace (ops : GMap OpId OpMeta) (i : RegInput w64) (id : OpId) (F : PTag)
    (p : Option PTag) : Option PTag :=
  match p with
  | none => none
  | some t => if placeOk i id F t ∧ (rank i = 0 → ∀ id2 m2, id2 ≠ id → ops.lookup id2 = some m2 →
      rank m2.input = 0 → m2.place.tag? ≠ some t) then some t else none

theorem sintZ_inj32 {a b : w32} (h : sint.Z a = sint.Z b) : a = b := BitVec.toInt_inj.1 h

/-- The registration and binding maps after placing `id = (hs, req)` on connection `cid`. -/
theorem place_join_conn {ops : GMap OpId OpMeta} {info : GMap OpId OpInfo}
    {places : GMap OpId Placement} {conns : GMap w32 (Option w64)} {placers : GMap w64 Int}
    (hj : opsJoin ops info places) (hc : connFacts conns placers places)
    {hs : w32} {cid : w64} {req last : Int} {n : OpInfo} (pl : Placement)
    (hinfo : info.lookup (sint.Z hs, req) = some n)
    (hconn : conns.lookup hs = some (some cid)) (hplacer : placers.lookup cid = some last)
    (hlt : last < req) :
    opsJoin (ops.insert (sint.Z hs, req) (joinMeta n pl)) info (places.insert (sint.Z hs, req) pl) ∧
    connFacts conns (placers.insert cid req) (places.insert (sint.Z hs, req) pl) := by
  refine ⟨⟨fun id' => ?_, fun id' h => ?_⟩, ⟨fun id' h => ?_, fun hs2 cid2 r h2 hp => ?_⟩⟩
  · by_cases e : (sint.Z hs, req) = id'
    · subst e; rw [GMap.lookup_insert, GMap.lookup_insert, hinfo]; rfl
    · rw [GMap.lookup_insert_ne _ _ e, GMap.lookup_insert_ne _ _ e]; exact hj.1 id'
  · by_cases e : (sint.Z hs, req) = id'
    · subst e; rw [hinfo]; rfl
    · rw [GMap.lookup_insert_ne _ _ e] at h; exact hj.2 id' h
  · by_cases e : (sint.Z hs, req) = id'
    · subst e; exact ⟨hs, cid, rfl, hconn⟩
    · rw [GMap.lookup_insert_ne _ _ e] at h; exact hc.1 id' h
  · by_cases e : (sint.Z hs, req) = (sint.Z hs2, r)
    · obtain ⟨e1, e2⟩ := Prod.mk.inj e
      have := sintZ_inj32 e1; subst this; subst e2
      rw [hconn] at h2; cases h2
      exact ⟨req, GMap.lookup_insert _ _ _, Int.le_refl _⟩
    · rw [GMap.lookup_insert_ne _ _ e] at hp
      obtain ⟨n', hn', hr⟩ := hc.2 hs2 cid2 r h2 hp
      by_cases ec : cid = cid2
      · subst ec; rw [hplacer] at hn'; cases hn'
        exact ⟨req, GMap.lookup_insert _ _ _, by omega⟩
      · exact ⟨n', by rw [GMap.lookup_insert_ne _ _ ec]; exact hn', hr⟩

/-- An unplaced registered operation is not linearized. -/
theorem unplaced_not_lin {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)}
    (h : invFactsCore σ stores tv lbs ops lin insts execS preds turns) {id : OpId} {m : OpMeta}
    (hm : ops.lookup id = some m) (hu : m.place = .unplaced) : ∀ o, (id, o) ∉ lin := by
  intro o ho
  obtain ⟨a, b, c, -, -, -, -, -, -, -, f_lin, -⟩ := h
  obtain ⟨t, freg, hp, -⟩ := (f_lin id m hm).1 ⟨o, ho⟩
  rw [hu] at hp; cases hp

/-- A write placed above the frontier at its own client's tag collides with no rank-0 place. -/
theorem write_no_clash {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)}
    (h : invFactsCore σ stores tv lbs ops lin insts execS preds turns) (hsh : placeShapes ops)
    {a b c : w64 × PTag} (ha : stores.lookup 0 = some a) (hb : stores.lookup 1 = some b)
    (hc : stores.lookup 2 = some c)
    {id : OpId} {m : OpMeta} (hm : ops.lookup id = some m) (hu : m.place = .unplaced)
    {t : PTag} (hlt : tagLt (median3 a.2 b.2 c.2) t) (hcid : t.2.1 = id.1) (h0 : t.2.2 = 0) :
    ∀ id2 m2, id2 ≠ id → ops.lookup id2 = some m2 → rank m2.input = 0 →
      m2.place.tag? ≠ some t := by
  intro id2 m2 hne hm2 hr2 ht2
  have hnl := unplaced_not_lin h hm hu
  have hchar := invFacts_char ha hb hc h
  obtain ⟨a', b', c', -, -, -, -, -, -, -, -, -, f_t2, -⟩ := h
  have hcid2 : id2.1 = id.1 := by
    cases hi : m2.input with
    | read => rw [hi] at hr2; cases hr2
    | write v => rw [← hcid]; exact ((hsh id2 m2 t hm2 ht2).1 v hi).1.symm
    | cas o n => have := (hsh id2 m2 t hm2 ht2).2 o n hi; omega
  obtain ⟨c1, r1⟩ := id; obtain ⟨c2, r2⟩ := id2
  simp only at hcid2; subst hcid2
  have hrne : r1 ≠ r2 := fun e => hne (by rw [e])
  rcases Int.lt_or_gt_of_ne hrne with hlt' | hlt'
  · obtain ⟨o, ho⟩ := f_t2 c2 r1 r2 hlt' (by rw [hm]; rfl) (by rw [hm2]; rfl)
    exact hnl o ho
  · obtain ⟨o, ho⟩ := f_t2 c2 r2 r1 hlt' (by rw [hm2]; rfl) (by rw [hm]; rfl)
    obtain ⟨tq', freg', hp', -, htF', -⟩ := (hchar _ m2 hm2).1 ⟨o, ho⟩
    have : tq' = t := by rw [hp'] at ht2; exact Option.some.inj ht2
    subst this
    exact (not_tagLe_iff _ _).2 hlt htF'


theorem recPlace_some {ops : GMap OpId OpMeta} {i : RegInput w64} {id : OpId} {F : PTag}
    {p : Option PTag} {t : PTag} (h : recPlace ops i id F p = some t) :
    p = some t ∧ placeOk i id F t ∧ (rank i = 0 → ∀ id2 m2, id2 ≠ id → ops.lookup id2 = some m2 →
      rank m2.input = 0 → m2.place.tag? ≠ some t) := by
  unfold recPlace at h
  cases p with
  | none => cases h
  | some t' =>
    simp only at h
    by_cases hc : placeOk i id F t' ∧ (rank i = 0 → ∀ id2 m2, id2 ≠ id →
        ops.lookup id2 = some m2 → rank m2.input = 0 → m2.place.tag? ≠ some t')
    · rw [if_pos hc] at h; cases h; exact ⟨rfl, hc⟩
    · rw [if_neg hc] at h; cases h

/-- What `op_place` records is `placeRec`'s. -/
theorem recPlace_rec {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)}
    (h : invFactsCore σ stores tv lbs ops lin insts execS preds turns) (hsh : placeShapes ops)
    {a b c : w64 × PTag} (ha : stores.lookup 0 = some a) (hb : stores.lookup 1 = some b)
    (hc : stores.lookup 2 = some c)
    {id : OpId} {m : OpMeta} (hm : ops.lookup id = some m) (hu : m.place = .unplaced)
    (p : Option PTag) :
    placeRec m.input id (median3 a.2 b.2 c.2) p (recPlace ops m.input id (median3 a.2 b.2 c.2) p) := by
  unfold placeRec
  cases p with
  | none => left; rfl
  | some t =>
    by_cases hc' : placeOk m.input id (median3 a.2 b.2 c.2) t ∧ (rank m.input = 0 → ∀ id2 m2,
        id2 ≠ id → ops.lookup id2 = some m2 → rank m2.input = 0 → m2.place.tag? ≠ some t)
    · left; unfold recPlace; simp only; rw [if_pos hc']
    · right
      refine ⟨by unfold recPlace; simp only; rw [if_neg hc'], fun t' ht' => ?_⟩
      cases ht'
      by_cases hok : placeOk m.input id (median3 a.2 b.2 c.2) t
      · cases hi : m.input with
        | read => exact absurd ⟨hok, fun h0 => by rw [hi] at h0; cases h0⟩ hc'
        | write v =>
          rw [hi] at hok
          obtain ⟨hlt, hcid, h0⟩ := hok
          exact absurd ⟨by rw [hi]; exact ⟨hlt, hcid, h0⟩,
            fun _ => write_no_clash h hsh ha hb hc hm hu hlt hcid h0⟩ hc'
        | cas o n => exact Or.inr ⟨o, n, rfl⟩
      · exact Or.inl hok

/-- A read placed at the frontier that qualifies there at once. -/
def placeFires (ops : GMap OpId OpMeta) (i : RegInput w64) (q : Option PTag) (F : PTag) : Prop :=
  i = .read ∧ ∃ t, q = some t ∧ tagLe t F ∧ (t = tag0 ∨ ∃ id' m' freg', ops.lookup id' = some m' ∧
    rank m'.input = 0 ∧ m'.place = .placed (some t) freg' ∧ tagLe freg' t)

/-- **`op_place`'s pure step, when the placed operation does not qualify at once**. -/
theorem op_place_nofire {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)}
    (h : invFactsB σ stores tv lbs ops lin insts execS preds turns) (hsh : placeShapes ops)
    {a b c : w64 × PTag} (ha : stores.lookup 0 = some a) (hb : stores.lookup 1 = some b)
    (hc : stores.lookup 2 = some c)
    {id : OpId} {n : OpInfo} (hm : ops.lookup id = some (joinMeta n .unplaced)) (p : Option PTag)
    (hnf : ¬ placeFires ops n.input (recPlace ops n.input id (median3 a.2 b.2 c.2) p)
      (median3 a.2 b.2 c.2)) :
    invFactsB σ stores tv lbs (ops.insert id (joinMeta n (.placed
        (recPlace ops n.input id (median3 a.2 b.2 c.2) p) (median3 a.2 b.2 c.2)))) lin insts execS
      preds turns ∧
    placeShapes (ops.insert id (joinMeta n (.placed
        (recPlace ops n.input id (median3 a.2 b.2 c.2) p) (median3 a.2 b.2 c.2)))) := by
  generalize hF : median3 a.2 b.2 c.2 = F at hnf
  generalize hq : recPlace ops n.input id F p = q at hnf
  have hcore := h.1
  have hnl := unplaced_not_lin hcore hm rfl
  have hchar := invFacts_char ha hb hc hcore
  rw [hF] at hchar
  have hne : ∀ id', id' ≠ id → (ops.insert id (joinMeta n (.placed q F))).lookup id' =
      ops.lookup id' := fun id' e => GMap.lookup_insert_ne _ _ (Ne.symm e)
  have hsome : ∀ id', ((ops.insert id (joinMeta n (.placed q F))).lookup id').isSome =
      (ops.lookup id').isSome := by
    intro id'
    by_cases e : id' = id
    · subst e; rw [GMap.lookup_insert, hm]; rfl
    · rw [hne _ e]
  have h0 := h
  obtain ⟨⟨a', b', c', ha', hb', hc', -, -, -, -, -, f_t1, f_t2, -, -, -, -, -, -, -, -, -,
    f_chainP, -⟩, -, ⟨-, -, b3⟩⟩ := h
  refine ⟨core_change h0 id _ hne (GMap.lookup_insert _ _ _)
    (fun m hm' => by rw [hm] at hm'; cases hm'; rfl) hnl ?_ ?_ ?_
    (fun cid r b' r' ht hs => f_t1 cid r b' r' ht (by rw [← hsome]; exact hs))
    (fun cid r1 r2 hlt h1 h2 => f_t2 cid r1 r2 hlt (by rw [← hsome]; exact h1)
      (by rw [← hsome]; exact h2))
    (fun cid r r' ht hs => b3 cid r r' ht (by rw [← hsome]; exact hs)), ?_⟩
  · -- the placed operation does not qualify
    intro a2 b2 c2 ha2 hb2 hc2 ⟨t, freg, hpl, hf, htF, hrest⟩
    rw [ha] at ha2; rw [hb] at hb2; rw [hc] at hc2; cases ha2; cases hb2; cases hc2
    rw [hF] at htF
    simp only [joinMeta, Placement.placed.injEq] at hpl
    obtain ⟨rfl, rfl⟩ := hpl
    obtain ⟨-, hok, -⟩ := recPlace_some hq
    cases hi : n.input with
    | read =>
      apply hnf
      refine ⟨hi, t, rfl, htF, ?_⟩
      rcases hrest with hr | h0 | ⟨id', m'', o', hm'', hr, ht, hin⟩
      · simp only [joinMeta, hi, rank] at hr; cases hr
      · exact Or.inl h0
      · have hne' : id' ≠ id := fun e => hnl o' (e ▸ hin)
        rw [hne _ hne'] at hm''
        obtain ⟨t', freg', hp', hf', -⟩ := (hchar id' m'' hm'').1 ⟨o', hin⟩
        have : t' = t := by rw [hp'] at ht; exact Option.some.inj ht
        subst this
        exact Or.inr ⟨id', m'', freg', hm'', hr, hp', hf'⟩
    | write v =>
      rw [hi] at hok; exact (not_tagLe_iff _ _).2 hok.1 htF
    | cas o nn =>
      rw [hi] at hok; exact (not_tagLe_iff _ _).2 hok.1 htF
  · -- distinct rank-0 places
    intro id2 m2 t e2 hm2 ht ht2 hr hr2
    simp only [joinMeta] at ht hr
    cases hq' : q with
    | none => rw [hq'] at ht; cases ht
    | some t' =>
      rw [hq'] at ht; simp only [Placement.tag?, Option.some.injEq] at ht; subst ht
      exact (recPlace_some (hq.trans hq')).2.2 hr id2 m2 e2 hm2 hr2 ht2
  · intro e a2 he ha2 hop
    have := f_chainP e a2 _ he ha2 (by rw [hop]; exact hm)
    simp [joinMeta, Placement.tag?] at this
  · -- the shapes
    intro id2 m2 t hm2 ht
    by_cases e : id2 = id
    · subst e; rw [GMap.lookup_insert] at hm2; cases hm2
      simp only [joinMeta] at ht ⊢
      cases hq' : q with
      | none => rw [hq'] at ht; cases ht
      | some t' =>
        rw [hq'] at ht; simp only [Placement.tag?, Option.some.injEq] at ht; subst ht
        obtain ⟨-, hok, -⟩ := recPlace_some (hq.trans hq')
        refine ⟨fun v hv => ?_, fun o nn hv => ?_⟩
        · rw [hv] at hok; exact ⟨hok.2.1, hok.2.2⟩
        · rw [hv] at hok; exact hok.2
    · rw [hne _ e] at hm2; exact hsh id2 m2 t hm2 ht


/-- **`op_place`'s pure step, when the placed operation (a read at the frontier) qualifies at
once**: it is linearized, returning the abstract state. -/
theorem op_place_fire {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)}
    (h : invFactsB σ stores tv lbs ops lin insts execS preds turns) (hsh : placeShapes ops)
    {a b c : w64 × PTag} (ha : stores.lookup 0 = some a) (hb : stores.lookup 1 = some b)
    (hc : stores.lookup 2 = some c)
    {id : OpId} {n : OpInfo} (hm : ops.lookup id = some (joinMeta n .unplaced)) (p : Option PTag)
    (hfire : placeFires ops n.input (recPlace ops n.input id (median3 a.2 b.2 c.2) p)
      (median3 a.2 b.2 c.2)) :
    recPlace ops n.input id (median3 a.2 b.2 c.2) p = some (median3 a.2 b.2 c.2) ∧
    invFactsB σ stores tv lbs (ops.insert id (joinMeta n (.placed
        (some (median3 a.2 b.2 c.2)) (median3 a.2 b.2 c.2)))) (lin ++ [(id, .value σ)]) insts
      execS preds turns ∧
    placeShapes (ops.insert id (joinMeta n (.placed
        (some (median3 a.2 b.2 c.2)) (median3 a.2 b.2 c.2)))) := by
  obtain ⟨hi, t, hq, htF, hprod⟩ := hfire
  obtain ⟨-, hok, -⟩ := recPlace_some hq
  rw [hi] at hok
  have htF' : t = median3 a.2 b.2 c.2 := tagLe_antisymm htF hok
  subst htF'
  refine ⟨hq, ?_, ?_⟩
  rotate_left
  · intro id2 m2 t' hm2 ht'
    by_cases e : id2 = id
    · rw [e, GMap.lookup_insert] at hm2; cases hm2
      refine ⟨fun v hv => ?_, fun o nn hv => ?_⟩ <;> simp [joinMeta, hi] at hv
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hm2; exact hsh id2 m2 t' hm2 ht'
  generalize hF : median3 a.2 b.2 c.2 = F at *
  have hcore := h.1
  have hnl := unplaced_not_lin hcore hm rfl
  have hchar := invFacts_char ha hb hc hcore
  rw [hF] at hchar
  let m' := joinMeta n (.placed (some F) F)
  have hne : ∀ id', id' ≠ id → (ops.insert id m').lookup id' = ops.lookup id' :=
    fun id' e => GMap.lookup_insert_ne _ _ (Ne.symm e)
  have hid : (ops.insert id m').lookup id = some m' := GMap.lookup_insert _ _ _
  have hlinne : ∀ x ∈ lin, x.1 ≠ id := fun x hx e => hnl x.2 (by rw [← e]; exact hx)
  have hlk : ∀ x ∈ lin, (ops.insert id m').lookup x.1 = ops.lookup x.1 := fun x hx => hne _ (hlinne x hx)
  have htag_ne : ∀ id2 m2 t, ops.lookup id2 = some m2 → m2.place.tag? = some t → id2 ≠ id := by
    intro id2 m2 t h2 ht e; subst e; rw [hm] at h2; cases h2; cases ht
  have hrank_ne : ∀ id2 m2, (ops.insert id m').lookup id2 = some m2 → rank m2.input = 0 → id2 ≠ id := by
    intro id2 m2 h2 hr e; subst e; rw [hid] at h2; cases h2; simp [m', joinMeta, hi, rank] at hr
  obtain ⟨⟨a', b', c', ha', hb', hc', f_tv0, f_sv, f_lbs, f_σ, f_lin, f_t1, f_t2, f_prod, f_linops,
    f_nodup, f_ord, f_replay, f_hist, f_uniq, f_exec, f_chainS, f_chainP, f_pred1, f_pred2⟩,
    ⟨x1, x2, x3⟩, ⟨b1, b2, b3⟩⟩ := h
  rw [ha] at ha'; rw [hb] at hb'; rw [hc] at hc'; cases ha'; cases hb'; cases hc'
  rw [hF] at f_σ f_lin f_hist
  have hsome : ∀ id', ((ops.insert id m').lookup id').isSome = (ops.lookup id').isSome := by
    intro id'
    by_cases e : id' = id
    · subst e; rw [hid, hm]; rfl
    · rw [hne _ e]
  have hmemL : ∀ id2 o, (id2, o) ∈ lin ++ [(id, RegOutput.value σ)] ↔
      (id2, o) ∈ lin ∨ (id2 = id ∧ o = .value σ) := by
    intro id2 o; simp
  refine ⟨⟨a, b, c, ha, hb, hc, f_tv0, f_sv, f_lbs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    f_exec, f_chainS, ?_, f_pred1, f_pred2⟩, ⟨x1, ?_, x3⟩, ⟨b1, b2, ?_⟩⟩
  · rw [hF]; exact f_σ
  · -- the linearization fact
    rw [hF]
    intro id2 m2 hm2
    by_cases e : id2 = id
    · rw [e, hid] at hm2; cases hm2; rw [e]
      refine ⟨fun _ => ⟨F, F, rfl, tagLe_refl _, tagLe_refl _, ?_⟩,
        fun _ => ⟨.value σ, by simp⟩⟩
      rcases hprod with h0 | ⟨id', m'', freg', hm'', hr, hp, hf⟩
      · exact Or.inr (Or.inl h0)
      · obtain ⟨o', ho'⟩ := (hchar id' m'' hm'').2 ((qualP_rank0 m'' hr).2 ⟨F, freg', hp, hf, tagLe_refl _⟩)
        have hne' : id' ≠ id := htag_ne _ _ F hm'' (by rw [hp]; rfl)
        exact Or.inr (Or.inr ⟨id', m'', o', by rw [hne _ hne']; exact hm'', hr,
          by rw [hp]; rfl, List.mem_append_left _ ho'⟩)
    · rw [hne _ e] at hm2
      have hiff := f_lin id2 m2 hm2
      constructor
      · rintro ⟨o, ho⟩
        rcases (hmemL id2 o).1 ho with ho | ⟨e', -⟩
        · obtain ⟨t, freg, h1, h2, h3, h4⟩ := hiff.1 ⟨o, ho⟩
          refine ⟨t, freg, h1, h2, h3, ?_⟩
          rcases h4 with h4 | h4 | ⟨id', m'', o', hm'', hr, ht, hin⟩
          · exact Or.inl h4
          · exact Or.inr (Or.inl h4)
          · exact Or.inr (Or.inr ⟨id', m'', o', by rw [hne _ (hlinne _ hin)]; exact hm'', hr, ht,
              List.mem_append_left _ hin⟩)
        · exact absurd e' e
      · rintro ⟨t, freg, h1, h2, h3, h4⟩
        obtain ⟨o, ho⟩ := hiff.2 ⟨t, freg, h1, h2, h3, by
          rcases h4 with h4 | h4 | ⟨id', m'', o', hm'', hr, ht, hin⟩
          · exact Or.inl h4
          · exact Or.inr (Or.inl h4)
          · have hne' := hrank_ne id' m'' hm'' hr
            rw [hne _ hne'] at hm''
            rcases (hmemL id' o').1 hin with hin | ⟨e', -⟩
            · exact Or.inr (Or.inr ⟨id', m'', o', hm'', hr, ht, hin⟩)
            · exact absurd e' hne'⟩
        exact ⟨o, List.mem_append_left _ ho⟩
  · intro cid r b' r' ht hs; exact f_t1 cid r b' r' ht (by rw [← hsome]; exact hs)
  · intro cid r1 r2 hlt h1 h2
    obtain ⟨o, ho⟩ := f_t2 cid r1 r2 hlt (by rw [← hsome]; exact h1) (by rw [← hsome]; exact h2)
    exact ⟨o, List.mem_append_left _ ho⟩
  · intro t v ht ht0
    obtain ⟨id2, m2, h1, h2, h3⟩ := f_prod t v ht ht0
    exact ⟨id2, m2, by rw [hne _ (htag_ne _ _ _ h1 h2)]; exact h1, h2, h3⟩
  · intro id2 o ho
    rcases (hmemL id2 o).1 ho with ho | ⟨rfl, -⟩
    · rw [hne _ (hlinne _ ho)]; exact f_linops id2 o ho
    · exact ⟨m', hid⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨f_nodup, by simp, ?_⟩
    intro x hx y hy e; simp at hy; subst hy; subst e
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    exact hlinne z hz rfl
  · rw [List.pairwise_append]
    refine ⟨List.Pairwise.imp_of_mem ?_ f_ord, by simp, ?_⟩
    · intro x y hx hy ⟨mx, my, tx, ty, h1, h2, h3, h4, h5⟩
      exact ⟨mx, my, tx, ty, by rw [hlk x hx]; exact h1, by rw [hlk y hy]; exact h2, h3, h4, h5⟩
    · intro x hx y hy
      simp only [List.mem_singleton] at hy; subst hy
      obtain ⟨mx, hmx⟩ := f_linops x.1 x.2 hx
      obtain ⟨tx, freg, hpx, -, hxF, -⟩ := (f_lin x.1 mx hmx).1 ⟨x.2, hx⟩
      refine ⟨mx, m', tx, F, by rw [hlk x hx]; exact hmx, hid, by rw [hpx]; rfl, rfl, ?_⟩
      rcases hxF with hlt | heq
      · exact Or.inl hlt
      · refine Or.inr ⟨heq, ?_⟩
        simp only [m', joinMeta, hi, rank]
        cases mx.input <;> simp [rank]
  · -- the replay
    show replayOk (W64 0) (entries (ops.insert id m') (lin ++ [(id, .value σ)])) σ
    rw [entries_append, entries_congr hlk, replayOk_append]
    refine ⟨σ, f_replay, ?_⟩
    simp [entries, hid, m', joinMeta, hi, replayOk, casApply]
  · -- the history
    intro t v ht hle
    rw [hF] at hle
    show replayOk (W64 0) (entries (ops.insert id m') (preT (ops.insert id m')
      (lin ++ [(id, .value σ)]) t)) v
    rw [preT_append, preT_congr t hlk, entries_append,
      entries_congr (fun x hx => hlk x (mem_preT.1 hx).1)]
    have hold := f_hist t v ht hle
    by_cases hFt : tagLe F t
    · have heq : t = F := tagLe_antisymm hle hFt
      rw [heq] at ht hold ⊢
      have hvσ : v = σ := by rw [ht] at f_σ; exact Option.some.inj f_σ
      rw [hvσ] at hold ⊢
      rw [replayOk_append]
      refine ⟨σ, hold, ?_⟩
      have : preT (ops.insert id m') [(id, RegOutput.value σ)] F = [(id, .value σ)] := by
        simp [preT, hid, m', joinMeta, Placement.tag?, tagLe_refl]
      rw [this]
      simp [entries, hid, m', joinMeta, hi, replayOk, casApply]
    · have : preT (ops.insert id m') [(id, RegOutput.value σ)] t = [] := by
        simp [preT, hid, m', joinMeta, Placement.tag?, hFt]
      rw [this, show entries (ops.insert id m') [] = [] from rfl, List.append_nil]; exact hold
  · intro id1 id2 m1 m2 t h1 h2 ht1 ht2 hr1 hr2
    have e1 := hrank_ne id1 m1 h1 hr1
    have e2 := hrank_ne id2 m2 h2 hr2
    rw [hne _ e1] at h1; rw [hne _ e2] at h2
    exact f_uniq id1 id2 m1 m2 t h1 h2 ht1 ht2 hr1 hr2
  · intro e a2 m2 he ha2 hm2
    by_cases eq : a2.op = id
    · have := f_chainP e a2 _ he ha2 (by rw [eq]; exact hm)
      simp [joinMeta, Placement.tag?] at this
    · rw [hne _ eq] at hm2; exact f_chainP e a2 m2 he ha2 hm2
  · intro t v ht ht0
    obtain ⟨id2, m2, freg, h1, h2, h3, h4⟩ := x2 t v ht ht0
    have hne2 : id2 ≠ id := htag_ne _ _ t h1 (by rw [h2]; rfl)
    exact ⟨id2, m2, freg, by rw [hne _ hne2]; exact h1, h2, h3, h4⟩
  · intro cid r r' ht hs
    obtain ⟨o, ho⟩ := b3 cid r r' ht (by rw [← hsome]; exact hs)
    exact ⟨o, List.mem_append_left _ ho⟩


/-- **`store_update`'s pure step, all facts**: `store_update_pure` with the book-keeping facts. -/
theorem store_update_all {σ : w64} {stores : GMap Nat (w64 × PTag)} {tv : GMap PTag w64}
    {lbs : GMap (Nat × PTag) Unit} {ops : GMap OpId OpMeta} {info : GMap OpId OpInfo}
    {places : GMap OpId Placement} {lin : List (OpId × RegOutput w64)}
    {insts : GMap (Int × Int) InstAttrs} {execS : List ExecEntry}
    {preds : GMap Nat (List ExecEntry)} {turns : GMap Int (Int × Bool)}
    {conns : GMap w32 (Option w64)} {placers : GMap w64 Int} {k : Nat} {v v' : w64}
    {t t' : PTag}
    (h : allFacts σ stores tv lbs ops info places lin insts execS preds turns conns placers)
    (hk : stores.lookup k = some (v, t)) (htv : tv.lookup t' = some v') (hlt : tagLt t t') :
    ∃ (new : List (OpId × RegOutput w64)) (σ' : w64),
      (∀ x ∈ new, (ops.lookup x.1).isSome ∧ ∀ o, (x.1, o) ∉ lin) ∧ (new.map Prod.fst).Nodup ∧
      replayOk σ (entries ops new) σ' ∧
      allFacts σ' (stores.insert k (v', t')) tv (lbs.insert (k, t') ()) ops info places
        (lin ++ new) insts execS preds turns conns placers := by
  obtain ⟨hI, hj, hc⟩ := h
  obtain ⟨new, σ', h1, h2, h3, ⟨hcore, hx⟩⟩ := store_update_pure (invFacts_R hI) hk htv hlt
  obtain ⟨-, -, ⟨b1, b2, b3⟩⟩ := hI
  refine ⟨new, σ', h1, h2, h3, ⟨hcore, hx, ⟨?_, ?_, ?_⟩⟩, hj, hc⟩
  · intro k' vt h'
    by_cases e : k = k'
    · subst e; exact b1 k _ hk
    · rw [GMap.lookup_insert_ne _ _ e] at h'; exact b1 k' vt h'
  · intro k' vt h'
    by_cases e : k = k'
    · subst e; rw [GMap.lookup_insert] at h'; cases h'; exact GMap.lookup_insert _ _ _
    · rw [GMap.lookup_insert_ne _ _ e] at h'
      have hne : (k, t') ≠ (k', vt.2) := fun e' => e (Prod.mk.inj e').1
      rw [GMap.lookup_insert_ne _ _ hne]; exact b2 k' vt h'
  · intro cid r r' ht hs
    obtain ⟨o, ho⟩ := b3 cid r r' ht hs
    exact ⟨o, List.mem_append_left _ ho⟩

end Perennial.gryff
