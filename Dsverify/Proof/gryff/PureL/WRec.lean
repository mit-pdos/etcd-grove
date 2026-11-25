/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/WRec.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: **the coordinator's write records** (`WInv`): the invariant over runs (with the messages
in flight) from which L1 for writes follows (`l1_write_of_inv`).

* `WOrig`: replica ids; every `Write1` in flight names a coordinator `R` (its `ReplicaId`) where
  its key is used; every `Write1Reply` in flight to `R` has a key used at `R`; client ids ≥ 0; every
  operation's key is used at its coordinator (so a key is never created twice at a replica:
  the guard `RState.used`).
* `WRec1 l c o`, for each write `o`: the `Write1Reply`s sent for it, at most one per replier, each
  at least the replier's store at `o`'s creation, split into consumed (`C`) and in flight (`I`,
  exactly the replies with `o`'s key in flight to `o.r`); at most one `Write1` of `o` in flight to
  each replica, none to a replica that already replied; `o`'s record (`RecOk`) has counted `C`, its
  `maxValTag` is at least each of them, its `WriteTag` is `mv + 1` with `mv` at least two of `C`
  from distinct repliers.
-/
module

public import Dsverify.Proof.gryff.PureL.CfgInv
public import Dsverify.Proof.gryff.PureL.Frame
public import Dsverify.Proof.gryff.PureL.Witness

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-! ## Words, lists -/

theorem msb_false_of_nonneg {b : w32} (hb : 0 ≤ sint.Z b) : b.msb = false :=
  BitVec.msb_eq_false_iff_two_mul_lt.2 (BitVec.toInt_pos_iff.1 hb)

theorem shiftInts_inj {a b a' b' : w32} (hb : 0 ≤ sint.Z b) (hb' : 0 ≤ sint.Z b')
    (h : shiftInts a b = shiftInts a' b') : a = a' ∧ b = b' := by
  have e1 := msb_false_of_nonneg hb
  have e2 := msb_false_of_nonneg hb'
  unfold shiftInts at h
  constructor
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    have := congrArg (fun x => x.getLsbD (k + 32)) h
    simp [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, e1, e2] at this
    have h1 : k < 64 := by omega
    have h2 : k + 32 < 64 := by omega
    have h3 : ¬ (k + 32 < 32) := by omega
    simpa [h1, h2, h3, hk] using this
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    have := congrArg (fun x => x.getLsbD k) h
    simp [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, e1, e2] at this
    have h1 : k < 64 := by omega
    have h2 : k + 32 < 64 := by omega
    have h3 : ¬ (k + 32 < 32) := by omega
    simpa [h1, h2, h3, hk] using this

theorem Z_succ64 {x : w64} {n : Int} (h : sint.Z x = n) (h0 : 0 ≤ n) (h1 : n < 10) :
    sint.Z (x + 1) = n + 1 := by
  simp only [sint.Z] at *
  rw [BitVec.toInt_add, h]
  simp [Int.bmod]; omega

theorem Z_succ32 {x : w32} (h1 : sint.Z x < 2 ^ 31 - 1) : sint.Z (x + 1) = sint.Z x + 1 := by
  simp only [sint.Z] at *
  rw [BitVec.toInt_add]
  have := BitVec.toInt_le (x := x); have := BitVec.le_toInt (x := x)
  simp [Int.bmod]; omega

theorem rid32_inj {a b : Fin 3} (h : rid32 a = rid32 b) : a = b := by
  revert a b; decide

theorem dstOf_rid32 (R : Fin 3) : dstOf (rid32 R) = some R := by
  revert R; decide

theorem nodup_fin3_len {l : List (Fin 3)} (h : l.Nodup) : l.length ≤ 3 := by
  have := List.Nodup.length_le_of_subset h (l₂ := List.finRange 3) (fun x _ => List.mem_finRange x)
  simpa using this

theorem filter_erase_of_false {α : Type} [DecidableEq α] (f : α → Bool) (l : List α) (a : α)
    (h : f a = false) : (l.erase a).filter f = l.filter f := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.erase_cons]
    by_cases hb : b = a
    · subst hb; simp [List.filter_cons, h]
    · have : (b == a) = false := by simp [hb]
      simp only [this, Bool.false_eq_true, if_false, List.filter_cons, ih]

theorem countP_erase_le {α : Type} [DecidableEq α] (f : α → Bool) (l : List α) (a : α) :
    (l.erase a).countP f ≤ l.countP f :=
  (List.erase_sublist).countP_le

theorem countP_erase_true {α : Type} [DecidableEq α] (f : α → Bool) {l : List α} {a : α}
    (ha : a ∈ l) (h : f a = true) : (l.erase a).countP f + 1 = l.countP f := by
  have := (List.perm_cons_erase ha).countP_eq f
  rw [this, List.countP_cons, if_pos h]

theorem countP_erase_false {α : Type} [DecidableEq α] (f : α → Bool) (l : List α) (a : α)
    (h : f a = false) : (l.erase a).countP f = l.countP f := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter, filter_erase_of_false f l a h]

/-! ## The invariant -/

/-- A configuration's in-flight messages and states at `Fin 3` (`Cfg gNet`'s fields are typed
by `gNet`'s components). -/
def infR (c : Cfg gNet) (j : Fin 3) : List Msg := c.inflight j
def stR (c : Cfg gNet) (j : Fin 3) : RState := c.st j

/-- A `Write1` of write `o`. -/
def w1of (o : Op) : Msg → Bool
  | .write1 m => m.requestId == o.rid && m.clientId == o.cid && m.replicaId == rid32 o.r
  | _ => false

/-- A `Write1Reply` with write `o`'s key. -/
def w1rOf (o : Op) : Msg → Bool
  | .write1Reply m => m.requestId == o.rid && m.clientId == o.cid
  | _ => false

theorem w1of_isW {o : Op} {m : Msg} (h : w1of o m = true) : isWMsg m = true := by
  cases m <;> simp_all [w1of, isWMsg]
theorem w1rOf_isW {o : Op} {m : Msg} (h : w1rOf o m = true) : isWMsg m = true := by
  cases m <;> simp_all [w1rOf, isWMsg]

/-- Origins of the write path's messages and keys. -/
structure WOrig (l : List Label) (c : Cfg gNet) : Prop where
  id : ∀ R : Fin 3, (stR c R).id = rid32 R
  w1 : ∀ (q : Fin 3) (m : Write1ProxiedM), Msg.write1 m ∈ infR c q → ∃ R : Fin 3,
    m.replicaId = rid32 R ∧ (m.clientId, m.requestId) ∈ (stR c R).used ∧ 0 ≤ sint.Z m.clientId
  w1r : ∀ (R : Fin 3) (m : Write1ReplyM), Msg.write1Reply m ∈ infR c R →
    (m.clientId, m.requestId) ∈ (stR c R).used ∧ 0 ≤ sint.Z m.clientId
  ops : ∀ o ∈ ops l, (o.cid, o.rid) ∈ (stR c o.r).used ∧ 0 ≤ sint.Z o.cid

/-- A write record that has counted the consumed replies `C`. -/
def RecOk (C : List (Fin 3 × model.Tag)) (w : WriteOp) : Prop :=
  sint.Z w.numWrite1Replies = C.length ∧
  (∀ p ∈ C, sint.Z p.2.ts ≤ sint.Z w.maxValTag.t.ts) ∧
  ∀ t, w.writeTag = some t → ∃ mv : w32, t.ts = mv + 1 ∧ sint.Z mv ≤ sint.Z w.maxValTag.t.ts ∧
    ∃ p1 ∈ C, ∃ p2 ∈ C, p1.1 ≠ p2.1 ∧ sint.Z p1.2.ts ≤ sint.Z mv ∧ sint.Z p2.2.ts ≤ sint.Z mv

/-- Write `o`'s replies and record. -/
def WRec1 (l : List Label) (c : Cfg gNet) (o : Op) : Prop :=
  ∃ C I : List (Fin 3 × model.Tag),
    ((C ++ I).map Prod.fst).Nodup ∧
    (∀ p ∈ C ++ I, sint.Z (cutSt l o.g p.1).tag.ts ≤ sint.Z p.2.ts) ∧
    ((infR c o.r).filter (w1rOf o)).Perm (I.map fun p => w1rep o p.2) ∧
    (∀ q, (infR c q).countP (w1of o) ≤ 1 ∧
      (q ∈ (C ++ I).map Prod.fst → (infR c q).countP (w1of o) = 0)) ∧
    ∀ w, (stR c o.r).wops.get? o.key = some w → RecOk C w

/-- **The write-record invariant.** -/
def WInv (l : List Label) (c : Cfg gNet) : Prop :=
  WOrig l c ∧ ∀ o ∈ ops l, ∀ v, o.inp = .write v → WRec1 l c o

/-! ## Steps -/

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (by simp),
      filterMap_congr' (fun b hb => h b (by simp [hb]))]

/-- The messages to replica `j` among outputs `o` (`kahn.sentTo` at `Fin 3`). -/
def sentR (j : Fin 3) (o : List Out) : List Msg :=
  o.filterMap (fun x => match x with | .send d m => if d = j then some m else none | .ext _ => none)

theorem sentTo_nil' {N : kahn.Net} (j : Fin N.n) : kahn.sentTo N j [] = [] := rfl
theorem sentTo_cons' {N : kahn.Net} (j : Fin N.n) (x : kahn.Out N.n N.M N.X)
    (o : List (kahn.Out N.n N.M N.X)) :
    kahn.sentTo N j (x :: o) = (match x with | .send d m => if d = j then [m] else [] | .ext _ => [])
      ++ kahn.sentTo N j o := by
  cases x with
  | send d m => simp only [kahn.sentTo, List.filterMap_cons]; split <;> simp_all
  | ext x => simp [kahn.sentTo]
theorem sentR_cons (j : Fin 3) (x : Out) (o : List Out) :
    sentR j (x :: o) = (match x with | .send d m => if d = j then [m] else [] | .ext _ => [])
      ++ sentR j o := by
  cases x with
  | send d m => simp only [sentR, List.filterMap_cons]; split <;> simp_all
  | ext x => simp [sentR]
theorem sentTo_eq (j : Fin 3) (o : List Out) : kahn.sentTo (N := gNet) j o = sentR j o := by
  induction o with
  | nil => exact sentTo_nil' (N := gNet) j
  | cons x o ih =>
    refine (sentTo_cons' (N := gNet) j x o).trans ?_
    rw [sentR_cons]
    cases x with
    | send d m => exact congrArg (_ ++ ·) ih
    | ext => exact congrArg (_ ++ ·) ih

theorem ops_snoc (l : List Label) (x : Label) :
    ops (l ++ [x]) = ops l ++ (opAt (l ++ [x]) l.length).toList := by
  rw [ops_eq, ops_eq, List.length_append, List.length_singleton, List.range_succ,
    List.filterMap_append]
  congr 1
  · apply filterMap_congr'
    intro g hg
    have hg' : g < l.length := List.mem_range.1 hg
    have := opAt_take (l := l ++ [x]) (k := l.length) (g := g)
    rw [List.take_left' rfl] at this
    rw [this]
    cases h : opAt (l ++ [x]) g with
    | none => rfl
    | some o => have := opAt_g h; simp [Option.filter, this, hg']

theorem opAt_snoc_new (l : List Label) (i : Fin 3) (e : Ev) :
    opAt (l ++ [(i, e)]) l.length = e.clientReq.map fun x =>
      { g := l.length, r := i, j := (projR l i).length, cid := x.1, rid := x.2.1, inp := x.2.2 } := by
  unfold opAt
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  simp [List.take_left' rfl]

theorem toOption_ok {r : StepRes} {a : RState × List Out} (h : Except.toOption r = some a) :
    r = .ok a := by
  cases r <;> simp_all [Except.toOption]

theorem noW_sentTo {o : List Out} (h : NoW o) (j : Fin 3) :
    ∀ m ∈ sentR j o, isWMsg m = false := by
  intro m hm
  unfold sentR at hm
  obtain ⟨y, hy, hy'⟩ := List.mem_filterMap.1 hm
  have := h y hy
  cases y with
  | send d m' =>
    simp only at hy'
    split at hy'
    · cases hy'; exact this
    · cases hy'
  | ext _ => cases hy'

theorem filter_sentTo_nil {o : List Out} (h : NoW o) (j : Fin 3) (f : Msg → Bool)
    (hf : ∀ m, f m = true → isWMsg m = true) : (sentR j o).filter f = [] := by
  rw [List.filter_eq_nil_iff]
  intro m hm hfm
  have := noW_sentTo h j m hm
  rw [hf m hfm] at this; cases this

theorem countP_sentTo_zero {o : List Out} (h : NoW o) (j : Fin 3) (f : Msg → Bool)
    (hf : ∀ m, f m = true → isWMsg m = true) : (sentR j o).countP f = 0 := by
  rw [List.countP_eq_length_filter, filter_sentTo_nil h j f hf]; rfl

theorem consume_filter (r : Option Msg) (l : List Msg) (f : Msg → Bool)
    (h : ∀ m, r = some m → f m = false) : (consume r l).filter f = l.filter f := by
  cases r with
  | none => rfl
  | some m => exact filter_erase_of_false f l m (h m rfl)

theorem consume_countP_le (r : Option Msg) (l : List Msg) (f : Msg → Bool) :
    (consume r l).countP f ≤ l.countP f := by
  cases r with
  | none => exact Nat.le_refl _
  | some m => exact countP_erase_le f l m

theorem mem_consume {r : Option Msg} {l : List Msg} {m : Msg} (h : m ∈ consume r l) : m ∈ l := by
  cases r with
  | none => exact h
  | some a => exact List.mem_of_mem_erase h

/-- The common shape of a step. -/
structure StepAt (l : List Label) (c : Cfg gNet) (i : Fin 3) (e : Ev) (c' : Cfg gNet)
    (s' : RState) (o : List Out) : Prop where
  run : GRun (Cfg.init gNet) l c
  ok : stepR i (stR c i) e = .ok (s', o)
  recv : ∀ m, e.recv = some m → m ∈ infR c i
  st : ∀ j : Fin 3, stR c' j = if j = i then s' else stR c j
  inf : ∀ j : Fin 3, infR c' j =
    (if j = i then consume e.recv (infR c j) else infR c j) ++ sentR j o

theorem StepAt.of {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {x : List Ext}
    (h : GRun (Cfg.init gNet) l c) (hs : GStep c i e c' x) :
    ∃ s' o, StepAt l c i e c' s' o := by
  obtain ⟨s', o, hstep, hmem, -, hst, hinf⟩ := hs
  refine ⟨s', o, h, toOption_ok hstep, hmem, fun j => congrFun hst j, fun j => ?_⟩
  have := congrFun hinf j
  unfold infR; rw [this]
  exact congrArg (_ ++ ·) (sentTo_eq j o)

theorem StepAt.filter_eq {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) (j : Fin 3) (f : Msg → Bool)
    (hr : ∀ m, e.recv = some m → f m = false)
    (hf : (sentR j o).filter f = []) :
    (infR c' j).filter f = (infR c j).filter f := by
  rw [hs.inf j, List.filter_append, hf, List.append_nil]
  split
  · exact consume_filter _ _ f hr
  · rfl

theorem StepAt.countP_le {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) (j : Fin 3) (f : Msg → Bool)
    (hf : (sentR j o).countP f = 0) :
    (infR c' j).countP f ≤ (infR c j).countP f := by
  rw [hs.inf j, List.countP_append, hf, Nat.add_zero]
  split
  · exact consume_countP_le _ _ f
  · exact Nat.le_refl _

theorem StepAt.mem {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) {j : Fin 3} {m : Msg} (h : m ∈ infR c' j) :
    m ∈ infR c j ∨ m ∈ sentR j o := by
  rw [hs.inf j, List.mem_append] at h
  rcases h with h | h
  · left; split at h
    · exact mem_consume h
    · exact h
  · exact Or.inr h

theorem cutSt_snoc {l : List Label} {x : Label} {k : Nat} (hk : k ≤ l.length) (r : Fin 3) :
    cutSt (l ++ [x]) k r = cutSt l k r := by
  unfold cutSt; rw [List.take_append_of_le_length hk]

/-- The frame for one write: its replies in flight and its record unchanged (or with the same
counted fields). -/
theorem wrec1_frame {l : List Label} {x : Label} {c c' : Cfg gNet} {o : Op} (hg : o.g ≤ l.length)
    (hw : WRec1 l c o)
    (hF : (infR c' o.r).filter (w1rOf o) = (infR c o.r).filter (w1rOf o))
    (hC : ∀ q, (infR c' q).countP (w1of o) ≤ (infR c q).countP (w1of o))
    (hR : ∀ C, (∀ w, (stR c o.r).wops.get? o.key = some w → RecOk C w) →
      ∀ w', (stR c' o.r).wops.get? o.key = some w' → RecOk C w') :
    WRec1 (l ++ [x]) c' o := by
  obtain ⟨C, I, h1, h2, h3, h4, h5⟩ := hw
  refine ⟨C, I, h1, fun p hp => ?_, hF ▸ h3, fun q => ?_, hR C h5⟩
  · rw [cutSt_snoc hg]; exact h2 p hp
  · have := hC q
    exact ⟨Nat.le_trans this (h4 q).1, fun hq => Nat.le_zero.1 ((h4 q).2 hq ▸ this)⟩

theorem ops_g_le {l : List Label} {o : Op} (h : o ∈ ops l) : o.g ≤ l.length :=
  Nat.le_of_lt (mem_ops.1 h).1

theorem StepAt.st_used_mono {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) (hu : (stR c i).used ⊆ s'.used) (j : Fin 3) :
    (stR c j).used ⊆ (stR c' j).used := by
  rw [hs.st j]; split
  · subst_vars; exact hu
  · exact fun _ h => h

/-! ### The step, by kind of event -/

/-- Events that keep the write accounting. -/
theorem winv_other {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) (he : Ev.wspecial e = false)
    (hi : WInv l c) : WInv (l ++ [(i, e)]) c' := by
  obtain ⟨⟨hfw1, hfw2, hfw3⟩, hnw⟩ := step_fw_other hs.ok he
  have hcr : e.clientReq = none := by
    cases e <;> simp_all [Ev.wspecial, Ev.clientReq]
  have hops : ops (l ++ [(i, e)]) = ops l := by
    rw [ops_snoc, opAt_snoc_new, hcr]; simp
  have hrw : ∀ m, e.recv = some m → isWMsg m = false := by
    intro m hm
    cases e with
    | msg m' =>
      cases hm
      cases m <;> simp_all [Ev.wspecial, isWMsg]
    | _ => cases hm
  have hstj : ∀ j, (stR c' j).wops = (stR c j).wops ∧ (stR c' j).id = (stR c j).id ∧
      (stR c' j).used = (stR c j).used := by
    intro j; rw [hs.st j]; split
    · subst_vars; exact ⟨hfw1, hfw2, hfw3⟩
    · exact ⟨rfl, rfl, rfl⟩
  obtain ⟨ho, hw⟩ := hi
  refine ⟨⟨fun R => (hstj R).2.1 ▸ ho.id R, fun q m hm => ?_, fun R m hm => ?_, fun o' h' => ?_⟩,
    fun o' h' v hv => ?_⟩
  · rcases hs.mem hm with hm | hm
    · obtain ⟨R, a, b, d⟩ := ho.w1 q m hm
      exact ⟨R, a, (hstj R).2.2 ▸ b, d⟩
    · cases noW_sentTo hnw q _ hm
  · rcases hs.mem hm with hm | hm
    · obtain ⟨b, d⟩ := ho.w1r R m hm
      exact ⟨(hstj R).2.2 ▸ b, d⟩
    · cases noW_sentTo hnw R _ hm
  · rw [hops] at h'; rw [(hstj o'.r).2.2]; exact ho.ops o' h'
  · rw [hops] at h'
    refine wrec1_frame (ops_g_le h') (hw o' h' v hv) ?_ ?_ ?_
    · exact hs.filter_eq _ _ (fun m hm => by
        cases h : w1rOf o' m
        · rfl
        · have := w1rOf_isW h; rw [hrw m hm] at this; cases this)
        (filter_sentTo_nil hnw _ _ (fun _ => w1rOf_isW))
    · exact fun q => hs.countP_le q _ (countP_sentTo_zero hnw q _ (fun _ => w1of_isW))
    · intro C hC w' hw'; rw [(hstj o'.r).1] at hw'; exact hC w' hw'

theorem ops_snoc_req {l : List Label} {i : Fin 3} {e : Ev} {cid rid : w32} {inp : RegInput w64}
    (h : e.clientReq = some (cid, rid, inp)) :
    ops (l ++ [(i, e)]) = ops l ++
      [{ g := l.length, r := i, j := (projR l i).length, cid, rid, inp }] := by
  rw [ops_snoc, opAt_snoc_new, h]; rfl

theorem StepAt.used_of_cons {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev}
    {s' : RState} {o : List Out} (hs : StepAt l c i e c' s' o) {a : w32 × w32}
    (hu : s'.used = a :: (stR c i).used) (j : Fin 3) : (stR c j).used ⊆ (stR c' j).used := by
  apply hs.st_used_mono; rw [hu]; exact fun _ h => List.mem_cons_of_mem _ h

/-- Client reads and RMWs. -/
theorem winv_cr {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) {cid rid : w32} {inp : RegInput w64}
    (hcr : e.clientReq = some (cid, rid, inp)) (hnw : ∀ v, inp ≠ .write v)
    (hrecv : e.recv = none) (hc : CR (stR c i) s' cid rid o)
    (hi : WInv l c) : WInv (l ++ [(i, e)]) c' := by
  obtain ⟨hu0, hcid, hu, hid, hwops, hnow⟩ := hc
  have hops := ops_snoc_req (l := l) (i := i) hcr
  have hmono := hs.used_of_cons hu
  have hstj : ∀ j, (stR c' j).wops = (stR c j).wops ∧ (stR c' j).id = (stR c j).id := by
    intro j; rw [hs.st j]; split
    · subst_vars; exact ⟨hwops, hid⟩
    · exact ⟨rfl, rfl⟩
  obtain ⟨ho, hw⟩ := hi
  refine ⟨⟨fun R => (hstj R).2 ▸ ho.id R, fun q m hm => ?_, fun R m hm => ?_, fun o' h' => ?_⟩,
    fun o' h' v hv => ?_⟩
  · rcases hs.mem hm with hm | hm
    · obtain ⟨R, a, b, d⟩ := ho.w1 q m hm
      exact ⟨R, a, hmono R b, d⟩
    · cases noW_sentTo hnow q _ hm
  · rcases hs.mem hm with hm | hm
    · obtain ⟨b, d⟩ := ho.w1r R m hm
      exact ⟨hmono R b, d⟩
    · cases noW_sentTo hnow R _ hm
  · rw [hops, List.mem_append, List.mem_singleton] at h'
    rcases h' with h' | rfl
    · obtain ⟨a, b⟩ := ho.ops o' h'; exact ⟨hmono _ a, b⟩
    · refine ⟨?_, hcid⟩
      show (cid, rid) ∈ (stR c' i).used
      rw [hs.st i, if_pos rfl, hu]; exact List.mem_cons_self
  · rw [hops, List.mem_append, List.mem_singleton] at h'
    rcases h' with h' | rfl
    · refine wrec1_frame (ops_g_le h') (hw o' h' v hv) ?_ ?_ ?_
      · exact hs.filter_eq _ _ (fun m hm => by rw [hrecv] at hm; cases hm)
          (filter_sentTo_nil hnow _ _ (fun _ => w1rOf_isW))
      · exact fun q => hs.countP_le q _ (countP_sentTo_zero hnow q _ (fun _ => w1of_isW))
      · intro C hC w' hw'; rw [(hstj o'.r).1] at hw'; exact hC w' hw'
    · exact absurd hv (hnw v)

theorem StepAt.inf_none {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) (hrecv : e.recv = none) (j : Fin 3) :
    infR c' j = infR c j ++ sentR j o := by
  rw [hs.inf j, hrecv]; split <;> rfl

theorem sentR_three (w : Msg) (j : Fin 3) :
    sentR j [.send 0 w, .send 1 w, .send 2 w] = [w] := by
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

theorem w1rOf_eq {o : Op} {m : Write1ReplyM} (h : w1rOf o (.write1Reply m) = true) :
    m.requestId = o.rid ∧ m.clientId = o.cid := by
  simpa [w1rOf] using h

theorem w1of_eq {o : Op} {m : Write1ProxiedM} (h : w1of o (.write1 m) = true) :
    m.requestId = o.rid ∧ m.clientId = o.cid ∧ m.replicaId = rid32 o.r := by
  simpa [w1of, and_assoc] using h

/-- Client writes. -/
theorem winv_write {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState} {o : List Out}
    {rid cid : w32} {k v : w64} {d : Dep} (hs : StepAt l c i (.write rid cid k v d) c' s' o)
    (hi : WInv l c) : WInv (l ++ [(i, .write rid cid k v d)]) c' := by
  obtain ⟨hu0, hcid, hu, hid, ⟨w0, hw0n, hw0t, hwops⟩, m0, hm1, hm2, hm3, rfl⟩ :=
    stepClientWrite_spec hs.ok
  have hops := ops_snoc_req (l := l) (i := i) (e := .write rid cid k v d) rfl
  have hmono := hs.used_of_cons hu
  have hrecv : Ev.recv (.write rid cid k v d) = none := rfl
  have hinf := hs.inf_none hrecv
  simp only [sentR_three] at hinf
  obtain ⟨ho, hw⟩ := hi
  have hid' : m0.replicaId = rid32 i := by rw [hm3]; exact ho.id i
  have hsti : stR c' i = s' := by rw [hs.st i, if_pos rfl]
  have hstj : ∀ j, j ≠ i → stR c' j = stR c j := fun j hj => by rw [hs.st j, if_neg hj]
  have hnew : (cid, rid) ∈ (stR c' i).used := by rw [hsti, hu]; exact List.mem_cons_self
  refine ⟨⟨fun R => ?_, fun q m hm => ?_, fun R m hm => ?_, fun o' h' => ?_⟩,
    fun o' h' v' hv => ?_⟩
  · by_cases hR : R = i
    · subst hR; rw [hsti, hid]; exact ho.id R
    · rw [hstj R hR]; exact ho.id R
  · rw [hinf, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · obtain ⟨R, a, b, d⟩ := ho.w1 q m hm
      exact ⟨R, a, hmono R b, d⟩
    · cases hm; exact ⟨i, hid', hm2 ▸ hm1 ▸ hnew, hm2 ▸ hcid⟩
  · rw [hinf, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · obtain ⟨b, d⟩ := ho.w1r R m hm
      exact ⟨hmono R b, d⟩
    · cases hm
  · rw [hops, List.mem_append, List.mem_singleton] at h'
    rcases h' with h' | rfl
    · obtain ⟨a, b⟩ := ho.ops o' h'; exact ⟨hmono _ a, b⟩
    · exact ⟨hnew, hcid⟩
  · rw [hops, List.mem_append, List.mem_singleton] at h'
    rcases h' with h' | rfl
    · -- an older write
      have hfalse : w1of o' (.write1 m0) = false := by
        cases h : w1of o' (.write1 m0)
        · rfl
        · obtain ⟨a, b, d⟩ := w1of_eq h
          rw [hid'] at d
          have := rid32_inj d
          have hu1 := (ho.ops o' h').1
          rw [← this, ← a, ← b, hm1, hm2] at hu1
          exact absurd hu1 hu0
      refine wrec1_frame (ops_g_le h') (hw o' h' v' hv) ?_ ?_ ?_
      · rw [hinf, List.filter_append]; simp [w1rOf]
      · intro q; rw [hinf, List.countP_append]; simp [hfalse]
      · intro C hC w' hw'
        by_cases hr : o'.r = i
        · rw [hr, hsti, hwops, AMap.get?_put] at hw'
          split at hw'
          · rename_i hk
            obtain ⟨a, b⟩ := shiftInts_inj (ho.ops o' h').2 hcid hk
            have hu1 := (ho.ops o' h').1
            rw [hr, a, b] at hu1
            exact absurd hu1 hu0
          · exact hC w' (hr ▸ hw')
        · rw [hstj _ hr] at hw'; exact hC w' hw'
    · -- the new write
      refine ⟨[], [], List.nodup_nil, fun p hp => by simp at hp, ?_, fun q => ?_, ?_⟩
      · show ((infR c' i).filter _).Perm []
        rw [hinf, List.filter_append]
        have : (infR c i).filter (w1rOf { g := l.length, r := i, j := (projR l i).length, cid, rid, inp := .write v }) = [] := by
          rw [List.filter_eq_nil_iff]
          intro m hm hf
          cases m with
          | write1Reply m =>
            obtain ⟨a, b⟩ := w1rOf_eq hf
            have := (ho.w1r i m hm).1
            rw [a, b] at this
            exact hu0 this
          | _ => simp [w1rOf] at hf
        rw [this]; simp [w1rOf]
      · have h0 : (infR c q).countP (w1of { g := l.length, r := i, j := (projR l i).length, cid, rid, inp := .write v }) = 0 := by
          rw [List.countP_eq_zero]
          intro m hm hf
          cases m with
          | write1 m =>
            obtain ⟨a, b, d⟩ := w1of_eq hf
            obtain ⟨R, hR, hRu, -⟩ := ho.w1 q m hm
            rw [hR] at d
            have := rid32_inj d
            rw [this, b, a] at hRu
            exact hu0 hRu
          | _ => simp [w1of] at hf
        rw [hinf, List.countP_append, h0]
        refine ⟨by simp; split <;> omega, fun hq => by simp at hq⟩
      · intro w hw
        show RecOk [] w
        have : (stR c' i).wops.get? (shiftInts rid cid) = some w := hw
        rw [hsti, hwops, AMap.get?_put, if_pos rfl] at this
        cases this
        refine ⟨by rw [hw0n]; rfl, fun p hp => by simp at hp, fun t ht => ?_⟩
        rw [hw0t] at ht; cases ht

theorem tagLe_ts {a b : model.Tag} (h : tagLe a.toP b.toP) : sint.Z a.ts ≤ sint.Z b.ts := by
  unfold tagLe tagLt model.Tag.toP at h
  rcases h with h | h
  · rcases h with h | ⟨h, _⟩ <;> simp only at h <;> omega
  · simp only [Prod.mk.injEq] at h; omega

theorem cutSt_len {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3) :
    cutSt l l.length r = stR c r := by
  unfold cutSt; rw [List.take_length]
  obtain ⟨o, ho⟩ := kahn.grun_state h r
  exact stOf_of_runP ho

theorem sendTo_rid32 {R : Fin 3} {m : Msg} {x : Out} (h : sendTo (rid32 R) m = some x) :
    x = .send R m := by
  unfold sendTo at h; rw [dstOf_rid32] at h; cases h; rfl

theorem sentR_single (R j : Fin 3) (w : Msg) :
    sentR j [.send R w] = if R = j then [w] else [] := by
  by_cases h : R = j <;> simp [sentR, h]

/-- `Write1`s. -/
theorem winv_write1 {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState} {o : List Out}
    {m : Write1ProxiedM} (hs : StepAt l c i (.msg (.write1 m)) c' s' o)
    (hi : WInv l c) : WInv (l ++ [(i, .msg (.write1 m))]) c' := by
  obtain ⟨⟨hfw1, hfw2, hfw3⟩, hout⟩ := stepWrite1_spec hs.ok
  have htag := step_tag_mono hs.ok
  have hops : ops (l ++ [(i, .msg (.write1 m))]) = ops l := by
    rw [ops_snoc, opAt_snoc_new]; simp [Ev.clientReq]
  obtain ⟨ho, hw⟩ := hi
  have hm : Msg.write1 m ∈ infR c i := hs.recv _ rfl
  obtain ⟨R, hR, hRu, hRc⟩ := ho.w1 i m hm
  obtain ⟨r0, hr0⟩ : ∃ r0 : Write1ReplyM, r0 = ⟨m.requestId, m.clientId, ⟨-1, s'.tag⟩⟩ :=
    ⟨_, rfl⟩
  rw [← hr0] at hout
  -- the outputs: nothing, or the reply to `R`
  obtain ⟨snt, hsnt⟩ : ∃ snt : Bool, o = if snt then [.send R (.write1Reply r0)] else [] := by
    rcases hout with rfl | ⟨x, hx, rfl⟩
    · exact ⟨false, rfl⟩
    · rw [hR] at hx; rw [sendTo_rid32 hx]; exact ⟨true, rfl⟩
  have hsent : ∀ j, sentR j o = if snt ∧ R = j then [.write1Reply r0] else [] := by
    intro j; rw [hsnt]; cases snt
    · rfl
    · simp only [if_true, sentR_single, true_and]
  have hinf : ∀ j, infR c' j = (if j = i then (infR c j).erase (.write1 m) else infR c j) ++
      (if snt ∧ R = j then [.write1Reply r0] else []) := by
    intro j; rw [hs.inf j, hsent j]; rfl
  have hstj : ∀ j, (stR c' j).wops = (stR c j).wops ∧ (stR c' j).id = (stR c j).id ∧
      (stR c' j).used = (stR c j).used := by
    intro j; rw [hs.st j]; split
    · subst_vars; exact ⟨hfw1, hfw2, hfw3⟩
    · exact ⟨rfl, rfl, rfl⟩
  have hmem : ∀ {j : Fin 3} {x : Msg}, x ∈ infR c' j → x ∈ infR c j ∨
      (snt ∧ R = j ∧ x = .write1Reply r0) := by
    intro j x hx
    rw [hinf j, List.mem_append] at hx
    rcases hx with hx | hx
    · left; split at hx
      · exact List.mem_of_mem_erase hx
      · exact hx
    · right; split at hx
      · rename_i hc; exact ⟨hc.1, hc.2, List.mem_singleton.1 hx⟩
      · cases hx
  refine ⟨⟨fun R' => (hstj R').2.1 ▸ ho.id R', fun q x hx => ?_, fun R' x hx => ?_,
    fun o' h' => ?_⟩, fun o' h' v hv => ?_⟩
  · rcases hmem hx with hx | ⟨-, -, hx⟩
    · obtain ⟨R'', a, b, d⟩ := ho.w1 q x hx
      exact ⟨R'', a, (hstj R'').2.2 ▸ b, d⟩
    · cases hx
  · rcases hmem hx with hx | ⟨-, hRR, hx⟩
    · obtain ⟨b, d⟩ := ho.w1r R' x hx
      exact ⟨(hstj R').2.2 ▸ b, d⟩
    · cases hx; subst hRR
      exact ⟨(hstj R).2.2 ▸ (by rw [hr0]; exact hRu), by rw [hr0]; exact hRc⟩
  · rw [hops] at h'; rw [(hstj o'.r).2.2]; exact ho.ops o' h'
  · rw [hops] at h'
    have hg := ops_g_le h'
    by_cases hwo : w1of o' (.write1 m) = true
    · -- `o'`'s `Write1` to `i`: the reply joins `I`
      obtain ⟨a, b, d⟩ := w1of_eq hwo
      rw [hR] at d
      have hRo := rid32_inj d
      subst hRo
      obtain ⟨C, I, h1, h2, h3, h4, h5⟩ := hw o' h' v hv
      have hpos : 0 < (infR c i).countP (w1of o') := List.countP_pos_iff.2 ⟨_, hm, hwo⟩
      have hiC : i ∉ (C ++ I).map Prod.fst := fun hc => by
        have := (h4 i).2 hc; omega
      have hcnt : (infR c' i).countP (w1of o') = 0 := by
        rw [hinf i, if_pos rfl, List.countP_append]
        have e1 := countP_erase_true (w1of o') hm hwo
        have e2 : ([] ++ (if snt ∧ o'.r = i then [Msg.write1Reply r0] else [])).countP (w1of o') = 0 := by
          split <;> simp [w1of]
        have := (h4 i).1
        simp only [List.nil_append] at e2
        omega
      have hr0 : Msg.write1Reply r0 = w1rep o' s'.tag := by
        rw [hr0]; unfold w1rep; rw [a, b]
      refine ⟨C, if snt then I ++ [(i, s'.tag)] else I, ?_, ?_, ?_, fun q => ?_, ?_⟩
      · cases snt
        · exact h1
        · simp only [↓reduceIte]
          rw [← List.append_assoc, List.map_append, List.nodup_append]
          refine ⟨h1, by simp, ?_⟩
          intro a ha b hb; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
          rw [hb]; rintro rfl
          exact hiC ha
      · intro p hp
        rw [cutSt_snoc hg]
        have hp' : p ∈ C ++ I ∨ p = (i, s'.tag) := by
          cases snt
          · exact Or.inl hp
          · simp only [↓reduceIte] at hp
            rw [← List.append_assoc, List.mem_append, List.mem_singleton] at hp
            exact hp
        rcases hp' with hp' | rfl
        · exact h2 p hp'
        · have e1 := cut_tag_mono hs.run i hg
          rw [cutSt_len hs.run] at e1
          exact tagLe_ts (tagLe_trans e1 htag)
      · rw [hinf o'.r, List.filter_append]
        have ef : (if o'.r = i then (infR c o'.r).erase (.write1 m) else infR c o'.r).filter (w1rOf o') =
            (infR c o'.r).filter (w1rOf o') := by
          split
          · exact filter_erase_of_false _ _ _ rfl
          · rfl
        rw [ef]
        cases snt
        · simpa using h3
        · simp only [true_and, if_true, List.filter_cons, List.filter_nil, List.map_append,
            List.map_cons, List.map_nil]
          rw [show w1rOf o' (.write1Reply r0) = true by rw [hr0]; simp [w1rOf, w1rep]]
          simp only [if_true, hr0]
          exact h3.append_right _
      · by_cases hq : q = i
        · subst hq; exact ⟨by omega, fun _ => hcnt⟩
        · have e : (infR c' q).countP (w1of o') = (infR c q).countP (w1of o') := by
            rw [hinf q, if_neg hq, List.countP_append]
            have : (if snt ∧ o'.r = q then [Msg.write1Reply r0] else []).countP (w1of o') = 0 := by
              split <;> simp [w1of]
            omega
          rw [e]
          refine ⟨(h4 q).1, fun hq' => (h4 q).2 ?_⟩
          cases snt
          · exact hq'
          · simp only [↓reduceIte] at hq'
            rw [← List.append_assoc, List.map_append, List.mem_append] at hq'
            rcases hq' with hq' | hq'
            · exact hq'
            · simp at hq'; exact absurd hq' hq
      · intro w hw'; rw [(hstj o'.r).1] at hw'; exact h5 w hw'
    · -- another write's `Write1`
      simp only [Bool.not_eq_true] at hwo
      refine wrec1_frame hg (hw o' h' v hv) ?_ ?_ ?_
      · refine hs.filter_eq _ _ (fun x hx => by cases hx; rfl) ?_
        rw [hsent]
        split
        · rename_i hc
          simp only [List.filter_cons, List.filter_nil]
          have : w1rOf o' (.write1Reply r0) = false := by
            cases h : w1rOf o' (.write1Reply r0)
            · rfl
            · obtain ⟨a, b⟩ := w1rOf_eq h
              simp only [hr0] at a b
              have : w1of o' (.write1 m) = true := by simp [w1of, a, b, hR, hc.2]
              rw [this] at hwo; cases hwo
          rw [this]; rfl
        · rfl
      · exact fun q => hs.countP_le q _ (by rw [hsent]; split <;> simp [w1of])
      · intro C hC w' hw'; rw [(hstj o'.r).1] at hw'; exact hC w' hw'

theorem gt_max_ts (T M : model.Tag) :
    sint.Z M.ts ≤ sint.Z (if T.gt M = true then T else M).ts ∧
      sint.Z T.ts ≤ sint.Z (if T.gt M = true then T else M).ts := by
  split
  · rename_i h
    exact ⟨tagLe_ts (Or.inl ((Tag.gt_iff _ _).1 h)), Int.le_refl _⟩
  · rename_i h
    refine ⟨Int.le_refl _, tagLe_ts ?_⟩
    rw [← not_tagLt_iff]; intro h'; exact h ((Tag.gt_iff _ _).2 h')

theorem sge_two {x : w64} (h : sge x (NHALF + 1) = true) : 2 ≤ sint.Z x := by
  simp only [sge, sle, decide_eq_true_eq] at h
  have : sint.Z (NHALF + 1 : w64) = 2 := by decide
  omega

theorem two_distinct {L : List (Fin 3 × model.Tag)} (hn : (L.map Prod.fst).Nodup)
    (hl : 2 ≤ L.length) : ∃ p1 ∈ L, ∃ p2 ∈ L, p1.1 ≠ p2.1 := by
  match L, hl with
  | p1 :: p2 :: rest, _ =>
    refine ⟨p1, by simp, p2, by simp, ?_⟩
    intro h
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hn
    exact hn.1 (Or.inl h)

/-- The record after one more reply `a` (`Write1Reply`'s handler). -/
theorem recOk_step {C : List (Fin 3 × model.Tag)} {a : Fin 3 × model.Tag} {w w' : WriteOp}
    (hn : ((C ++ [a]).map Prod.fst).Nodup) (hr : RecOk C w)
    (h1 : w'.numWrite1Replies = w.numWrite1Replies + 1)
    (h2 : w'.maxValTag.t = (if a.2.gt w.maxValTag.t = true then a.2 else w.maxValTag.t))
    (h3 : w'.writeTag = w.writeTag ∨ (sge w'.numWrite1Replies (NHALF + 1) = true ∧
      ∃ c, w'.writeTag = some ⟨w'.maxValTag.t.ts + 1, c, 0⟩)) : RecOk (C ++ [a]) w' := by
  obtain ⟨r1, r2, r3⟩ := hr
  have hlen : (C ++ [a]).length ≤ 3 := by
    have := nodup_fin3_len hn; simpa using this
  have hmv := gt_max_ts a.2 w.maxValTag.t
  rw [← h2] at hmv
  have r2' : ∀ p ∈ C ++ [a], sint.Z p.2.ts ≤ sint.Z w'.maxValTag.t.ts := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact Int.le_trans (r2 p hp) hmv.1
    · rw [List.mem_singleton.1 hp]; exact hmv.2
  have hnum : sint.Z w'.numWrite1Replies = (C ++ [a]).length := by
    rw [h1, Z_succ64 r1 (by omega) (by simp at hlen; omega)]; simp
  refine ⟨hnum, r2', fun t ht => ?_⟩
  rcases h3 with h3 | ⟨h3, cc, h4⟩
  · rw [h3] at ht
    obtain ⟨mv, e1, e2, p1, hp1, p2, hp2, hne, b1, b2⟩ := r3 t ht
    exact ⟨mv, e1, Int.le_trans e2 hmv.1, p1, List.mem_append_left _ hp1, p2,
      List.mem_append_left _ hp2, hne, b1, b2⟩
  · rw [h4] at ht; cases ht
    have h2l := sge_two h3
    rw [hnum] at h2l
    have hn' : ((C ++ [a]).map Prod.fst).Nodup := hn
    obtain ⟨p1, hp1, p2, hp2, hne⟩ := two_distinct hn' (by omega)
    exact ⟨_, rfl, Int.le_refl _, p1, hp1, p2, hp2, hne, r2' p1 hp1, r2' p2 hp2⟩

theorem perm_map_erase {α β : Type} [BEq α] [LawfulBEq α] {f : α → β} {I : List α}
    {a : α} (ha : a ∈ I) : (I.map f).Perm (f a :: (I.erase a).map f) := by
  have := (List.perm_cons_erase ha).map f
  simpa using this

/-- `Write1Reply`s. -/
theorem winv_write1Reply {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState}
    {o : List Out} {m : Write1ReplyM} (hs : StepAt l c i (.msg (.write1Reply m)) c' s' o)
    (hi : WInv l c) : WInv (l ++ [(i, .msg (.write1Reply m))]) c' := by
  obtain ⟨hid, hused, hnow, hW1, hW2, hW3⟩ := stepWrite1Reply_spec hs.ok
  have hops : ops (l ++ [(i, .msg (.write1Reply m))]) = ops l := by
    rw [ops_snoc, opAt_snoc_new]; simp [Ev.clientReq]
  obtain ⟨ho, hw⟩ := hi
  have hm : Msg.write1Reply m ∈ infR c i := hs.recv _ rfl
  obtain ⟨hmu, hmc⟩ := ho.w1r i m hm
  have hsti : stR c' i = s' := by rw [hs.st i, if_pos rfl]
  have hstj : ∀ j, j ≠ i → stR c' j = stR c j := fun j hj => by rw [hs.st j, if_neg hj]
  have hstu : ∀ j, (stR c' j).used = (stR c j).used ∧ (stR c' j).id = (stR c j).id := by
    intro j; by_cases hj : j = i
    · subst hj; rw [hsti]; exact ⟨hused, hid⟩
    · rw [hstj j hj]; exact ⟨rfl, rfl⟩
  refine ⟨⟨fun R => (hstu R).2 ▸ ho.id R, fun q x hx => ?_, fun R x hx => ?_, fun o' h' => ?_⟩,
    fun o' h' v hv => ?_⟩
  · rcases hs.mem hx with hx | hx
    · obtain ⟨R, a, b, d⟩ := ho.w1 q x hx
      exact ⟨R, a, (hstu R).1 ▸ b, d⟩
    · cases noW_sentTo hnow q _ hx
  · rcases hs.mem hx with hx | hx
    · obtain ⟨b, d⟩ := ho.w1r R x hx
      exact ⟨(hstu R).1 ▸ b, d⟩
    · cases noW_sentTo hnow R _ hx
  · rw [hops] at h'; rw [(hstu o'.r).1]; exact ho.ops o' h'
  · rw [hops] at h'
    have hg := ops_g_le h'
    by_cases hA : o'.r = i ∧ w1rOf o' (.write1Reply m) = true
    · obtain ⟨hr, hwr⟩ := hA
      obtain ⟨ea, eb⟩ := w1rOf_eq hwr
      obtain ⟨C, I, h1, h2, h3, h4, h5⟩ := hw o' h' v hv
      have hmf : Msg.write1Reply m ∈ (infR c o'.r).filter (w1rOf o') :=
        List.mem_filter.2 ⟨hr ▸ hm, hwr⟩
      obtain ⟨a, haI, hag⟩ := List.mem_map.1 (h3.mem_iff.1 hmf)
      have hmv : m.vt.t = a.2 := by
        unfold w1rep at hag; cases hag; rfl
      have hperm : (C ++ [a] ++ I.erase a).Perm (C ++ I) := by
        rw [List.append_assoc]
        exact List.Perm.append_left C (List.perm_cons_erase haI).symm
      refine ⟨C ++ [a], I.erase a, (hperm.map Prod.fst).nodup_iff.2 h1,
        fun p hp => by rw [cutSt_snoc hg]; exact h2 p (hperm.subset hp), ?_, fun q => ?_, ?_⟩
      · -- the reply leaves `I`
        rw [hs.inf o'.r, if_pos hr, List.filter_append,
          filter_sentTo_nil hnow _ _ (fun _ => w1rOf_isW), List.append_nil]
        show ((infR c o'.r).erase (.write1Reply m)).filter (w1rOf o') |>.Perm _
        have p1 : ((infR c o'.r).filter (w1rOf o')).Perm (.write1Reply m ::
            ((infR c o'.r).erase (.write1Reply m)).filter (w1rOf o')) := by
          have := (List.perm_cons_erase (hr ▸ hm)).filter (w1rOf o')
          rwa [List.filter_cons_of_pos hwr] at this
        have p2 := h3.trans (perm_map_erase (f := fun p => w1rep o' p.2) haI)
        rw [hag] at p2
        exact (p1.symm.trans p2).cons_inv
      · have hle := hs.countP_le q (w1of o') (countP_sentTo_zero hnow q _ (fun _ => w1of_isW))
        exact ⟨Nat.le_trans hle (h4 q).1,
          fun hq => Nat.le_zero.1 (((h4 q).2 ((hperm.map Prod.fst).subset hq)) ▸ hle)⟩
      · intro w' hw'
        have hK : o'.key = shiftInts m.requestId m.clientId := by unfold Op.key; rw [ea, eb]
        have hw'' : s'.wops.get? (shiftInts m.requestId m.clientId) = some w' := by
          rw [← hK, ← hsti, ← hr]; exact hw'
        obtain ⟨w, hw0, e1, e2, e3⟩ := hW3 w' hw''
        have hw0' : (stR c o'.r).wops.get? o'.key = some w := by rw [hr, hK]; exact hw0
        have hn3 : ((C ++ [a] ++ I.erase a).map Prod.fst).Nodup := (hperm.map Prod.fst).nodup_iff.2 h1
        rw [List.map_append] at hn3
        exact recOk_step (hn3.sublist (List.sublist_append_left _ _)) (h5 w hw0') e1 (hmv ▸ e2) e3
    · have hKne : o'.r = i → o'.key ≠ shiftInts m.requestId m.clientId := by
        intro hr hk
        obtain ⟨a, b⟩ := shiftInts_inj (ho.ops o' h').2 hmc hk
        exact hA ⟨hr, by simp [w1rOf, a, b]⟩
      refine wrec1_frame hg (hw o' h' v hv) ?_ ?_ ?_
      · rw [hs.inf o'.r, List.filter_append, filter_sentTo_nil hnow _ _ (fun _ => w1rOf_isW),
          List.append_nil]
        split
        · rename_i hr
          show ((infR c o'.r).erase (.write1Reply m)).filter (w1rOf o') = _
          apply filter_erase_of_false
          cases h : w1rOf o' (.write1Reply m)
          · rfl
          · exact absurd ⟨hr, h⟩ hA
        · rfl
      · exact fun q => hs.countP_le q _ (countP_sentTo_zero hnow q _ (fun _ => w1of_isW))
      · intro C hC w' hw'
        by_cases hr : o'.r = i
        · have e := hW1 o'.key (hKne hr)
          have : (stR c' o'.r).wops.get? o'.key = s'.wops.get? o'.key := by rw [hr, hsti]
          rw [this, e] at hw'
          exact hC w' (by rw [hr]; exact hw')
        · rw [hstj _ hr] at hw'; exact hC w' hw'

/-- `Write2Reply`s. -/
theorem winv_write2Reply {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState}
    {o : List Out} {m : Write2ReplyM} (hs : StepAt l c i (.msg (.write2Reply m)) c' s' o)
    (hi : WInv l c) : WInv (l ++ [(i, .msg (.write2Reply m))]) c' := by
  obtain ⟨hid, hused, hnow, hW1, hW2, hW3⟩ := stepWrite2Reply_spec hs.ok
  have hops : ops (l ++ [(i, .msg (.write2Reply m))]) = ops l := by
    rw [ops_snoc, opAt_snoc_new]; simp [Ev.clientReq]
  obtain ⟨ho, hw⟩ := hi
  have hsti : stR c' i = s' := by rw [hs.st i, if_pos rfl]
  have hstj : ∀ j, j ≠ i → stR c' j = stR c j := fun j hj => by rw [hs.st j, if_neg hj]
  have hstu : ∀ j, (stR c' j).used = (stR c j).used ∧ (stR c' j).id = (stR c j).id := by
    intro j; by_cases hj : j = i
    · subst hj; rw [hsti]; exact ⟨hused, hid⟩
    · rw [hstj j hj]; exact ⟨rfl, rfl⟩
  refine ⟨⟨fun R => (hstu R).2 ▸ ho.id R, fun q x hx => ?_, fun R x hx => ?_, fun o' h' => ?_⟩,
    fun o' h' v hv => ?_⟩
  · rcases hs.mem hx with hx | hx
    · obtain ⟨R, a, b, d⟩ := ho.w1 q x hx
      exact ⟨R, a, (hstu R).1 ▸ b, d⟩
    · cases noW_sentTo hnow q _ hx
  · rcases hs.mem hx with hx | hx
    · obtain ⟨b, d⟩ := ho.w1r R x hx
      exact ⟨(hstu R).1 ▸ b, d⟩
    · cases noW_sentTo hnow R _ hx
  · rw [hops] at h'; rw [(hstu o'.r).1]; exact ho.ops o' h'
  · rw [hops] at h'
    refine wrec1_frame (ops_g_le h') (hw o' h' v hv) ?_ ?_ ?_
    · exact hs.filter_eq _ _ (fun x hx => by cases hx; rfl)
        (filter_sentTo_nil hnow _ _ (fun _ => w1rOf_isW))
    · exact fun q => hs.countP_le q _ (countP_sentTo_zero hnow q _ (fun _ => w1of_isW))
    · intro C hC w' hw'
      by_cases hr : o'.r = i
      · have : (stR c' o'.r).wops.get? o'.key = s'.wops.get? o'.key := by rw [hr, hsti]
        rw [this] at hw'
        by_cases hk : o'.key = shiftInts m.requestId m.clientId
        · rw [hk] at hw'
          obtain ⟨w, hw0, e1, e2, e3⟩ := hW3 w' hw'
          obtain ⟨r1, r2, r3⟩ := hC w (by rw [hr, hk]; exact hw0)
          exact ⟨e1 ▸ r1, e2 ▸ r2, e2 ▸ e3 ▸ r3⟩
        · rw [hW1 _ hk] at hw'
          exact hC w' (by rw [hr]; exact hw')
      · rw [hstj _ hr] at hw'; exact hC w' hw'

/-- **`WInv` is kept by every step.** -/
theorem winv_step {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {x : List Ext}
    (h : GRun (Cfg.init gNet) l c) (hi : WInv l c) (hs : GStep c i e c' x) :
    WInv (l ++ [(i, e)]) c' := by
  obtain ⟨s', o, hst⟩ := StepAt.of h hs
  cases e with
  | read rid cid k d =>
    exact winv_cr hst rfl (fun _ h => by cases h) rfl (stepClientRead_spec hst.ok) hi
  | rmw rid cid k d a b =>
    exact winv_cr hst rfl (fun _ h => by cases h) rfl (stepClientRMW_spec hst.ok) hi
  | write => exact winv_write hst hi
  | msg m =>
    cases m with
    | write1 => exact winv_write1 hst hi
    | write1Reply => exact winv_write1Reply hst hi
    | write2Reply => exact winv_write2Reply hst hi
    | _ => exact winv_other hst rfl hi
  | _ => exact winv_other hst rfl hi

theorem winv_init : WInv [] (Cfg.init gNet) := by
  refine ⟨⟨fun R => ?_, fun q m hm => ?_, fun R m hm => ?_, fun o ho => ?_⟩, fun o ho => ?_⟩
  rotate_left
  · cases hm
  · cases hm
  · simp [ops_eq] at ho
  · simp [ops_eq] at ho
  show (RState.init R.val).id = rid32 R
  rfl

theorem winv {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) : WInv l c :=
  grun_inv WInv winv_init (fun _ _ _ _ _ _ h hi hs => winv_step h hi hs) l c h

/-- **The tag bound for write records**: a record's `maxValTag` has `ts < 2^31 - 1` (so the
`WriteTag`'s `ts + 1` does not wrap): every tag carried in a reachable configuration has `ts` at
most the potential `La.Tc c ≤ 72` (client requests minus write records that have not chosen their
`WriteTag`), the tag-bound invariant `La.tinv` (unit L-a, `PureLa/Inv.lean`). -/
theorem wops_ts_bound {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3)
    {K : w64} {w : WriteOp} (hw : (stR c r).wops.get? K = some w) :
    sint.Z w.maxValTag.t.ts < 2 ^ 31 - 1 :=
  La.wops_ts h r hw

/-- **L1 for writes** from the write-record invariant. -/
theorem l1_write_of_inv {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {v : w64} (hi : o.inp = .write v) {t : model.Tag}
    (ht : place l o = some t) : tagLt (front l o.g) t.toP := by
  have ht' : writePlace l o = some t := by unfold place at ht; rw [hi] at ht; exact ht
  unfold writePlace firstFrom at ht'
  obtain ⟨j', hj1, hj2⟩ := List.exists_of_findSome?_eq_some ht'
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj1
  obtain ⟨hjl, hjo⟩ := hj1
  obtain ⟨e, he⟩ : ∃ e, (projR l o.r)[j']? = some e := ⟨_, List.getElem?_eq_getElem hjl⟩
  obtain ⟨n, hn, hpn⟩ := proj_index l o.r he
  have hp1 : projR (l.take (n + 1)) o.r = (projR l o.r).take (j' + 1) := by
    rw [List.take_add_one, hn]
    show projR (l.take n ++ [(o.r, e)]) o.r = _
    rw [proj_snoc, if_pos rfl, hpn, List.take_add_one, he]; rfl
  -- o is created at or before label n
  obtain ⟨hog, hopAt⟩ := mem_ops.1 ho
  have hoj : o.j = (projR (l.take o.g) o.r).length := by
    unfold opAt at hopAt; split at hopAt
    · obtain ⟨_, _, ho'⟩ := Option.map_eq_some_iff.1 hopAt
      have h1 := congrArg Op.j ho'; have h2 := congrArg Op.r ho'
      simp only at h1 h2
      rw [← h1, ← h2]
    · cases hopAt
  have hgn : o.g ≤ n := by
    apply Nat.le_of_not_lt; intro hc
    have := proj_take_len_mono l o.r (show n + 1 ≤ o.g by omega)
    rw [hp1, ← hoj, List.length_take] at this
    omega
  -- the invariant at cut n + 1
  obtain ⟨cn, hrun, -, hst⟩ := grun_cut h (n + 1)
  have hcut : ∀ r : Fin 3, cutSt l (n + 1) r = cn.st r := fun r => by
    obtain ⟨o', h'⟩ := hst r; exact stOf_of_runP h'
  have ho' : o ∈ ops (l.take (n + 1)) := by
    rw [← ops_take, List.mem_filter]; exact ⟨ho, by simp; omega⟩
  obtain ⟨C, I, -, hCI, -, -, hrec⟩ := (winv hrun).2 o ho' v hi
  have hw : (stR cn o.r).wops.get? o.key >>= WriteOp.writeTag = some t := by
    show (cn.st o.r).wops.get? o.key >>= WriteOp.writeTag = some t
    rw [← hcut]; unfold cutSt; rw [hp1]; exact hj2
  obtain ⟨w, hw1, hw2⟩ := Option.bind_eq_some_iff.1 hw
  obtain ⟨-, -, htag⟩ := hrec w hw1
  obtain ⟨mv, hmv, hmvw, p1, hp1C, p2, hp2C, hne, hle1, hle2⟩ := htag t hw2
  have hb := wops_ts_bound hrun o.r hw1
  have hts : sint.Z t.ts = sint.Z mv + 1 := by rw [hmv]; exact Z_succ32 (by omega)
  have hlt1 : sint.Z p1.2.ts < sint.Z t.ts := by omega
  have hlt2 : sint.Z p2.2.ts < sint.Z t.ts := by omega
  have hb1 := hCI p1 (List.mem_append_left _ hp1C)
  have hb2 := hCI p2 (List.mem_append_left _ hp2C)
  have ec : ∀ r, cutSt (l.take (n + 1)) o.g r = cutSt l o.g r := fun r => cutSt_take (by omega) r
  replace hb1 : sint.Z (cutSt l o.g p1.1).tag.ts ≤ sint.Z p1.2.ts := by rw [← ec]; exact hb1
  replace hb2 : sint.Z (cutSt l o.g p2.1).tag.ts ≤ sint.Z p2.2.ts := by rw [← ec]; exact hb2
  have k1 : tagLt (cutSt l o.g p1.1).tag.toP t.toP := Or.inl (by simp only [model.Tag.toP]; omega)
  have k2 : tagLt (cutSt l o.g p2.1).tag.toP t.toP := Or.inl (by simp only [model.Tag.toP]; omega)
  have hm := median3_le_of_pair (l := l) (k := o.g) (t := tagMax (cutSt l o.g p1.1).tag.toP
    (cutSt l o.g p2.1).tag.toP) hne (le_tagMax_l _ _) (le_tagMax_r _ _)
  refine tagLt_of_le_of_lt hm ?_
  unfold tagMax; split <;> assumption


end Perennial.gryff.pure
