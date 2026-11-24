/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Inv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: **the read-record invariant** `RInv` (in `WInv`'s style, `PureL/WRec.lean`), from which
L1 for reads follows (`PureLb/L1Read.lean`).

* `MOk`: every message in flight is accounted for: a `Read1` of a read `o` carries a tag at least
  `o`'s coordinator's store at `o`'s creation and goes to another replica; a `Read1Reply` to `o`'s
  coordinator carries a tag at least two distinct stores at `o`'s creation (the replier's and the
  coordinator's); no `Read2`/`Read2Reply` exists (the first `Read1Reply` completes a read);
  every `Write1Reply` has value `-1` (so a write never short-circuits through `Write1Reply`s);
  keys used at the coordinator, client ids ≥ 0.
* `RRec`: the coordinators' records: read records are as created (`Fresh`), each owned by a read
  operation, with its `OngoingReqs` entry; write records owned by a write, with their entry,
  `maxValTag.v = -1`, `numWrite1Applies = 0`; the write map sorted; entries' numbers and short
  reads at most `maxN` (so a new number is fresh), `maxN ≤ nReqs ≤ 24`.
* `W2Rec l c ow` for each write `ow`: its `Write2`s and `Write2Reply`s (as `WRec1` does for
  `Write1Reply`s): `sent = some (g2, wt)` once the `Write2`s with tag `wt` were sent at cut `g2`;
  consumed / in-flight replies `C`/`I` from distinct replicas, each applier's store at `g2` below
  `wt`; the record counts the consumed appliers; every read short-circuited by `ow` was created
  before `g2`.
-/
module

public import Dsverify.Proof.gryff.PureLb.Specs
public import Dsverify.Proof.gryff.PureL.WRec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-! ## Sorted maps -/

def KSorted {n : Nat} {V : Type} (m : model.AMap n V) : Prop :=
  m.Pairwise (fun a b => a.1.toNat < b.1.toNat)

theorem AMap.get?_of_mem {n : Nat} {V : Type} {m : model.AMap n V} (hs : KSorted m) {K : BitVec n}
    {v : V} (h : (K, v) ∈ m) : m.get? K = some v := by
  induction m with
  | nil => cases h
  | cons a t ih =>
    obtain ⟨k0, v0⟩ := a
    unfold KSorted at hs
    rw [List.pairwise_cons] at hs
    simp only [model.AMap.get?, List.lookup] at ih ⊢
    rcases List.mem_cons.1 h with h | h
    · cases h; simp
    · have hlt := hs.1 _ h
      have hne : K ≠ k0 := by intro e; subst e; simp at hlt
      have : (K == k0) = false := by simp [hne]
      simp only [this]; exact ih hs.2 h

theorem AMap.mem_put {n : Nat} {V : Type} {m : model.AMap n V} {k : BitVec n} {v : V}
    {a : BitVec n × V} (h : a ∈ m.put k v) : a = (k, v) ∨ a ∈ m := by
  induction m with
  | nil => simp [model.AMap.put] at h; exact Or.inl h
  | cons b t ih =>
    obtain ⟨k0, v0⟩ := b
    unfold model.AMap.put at h
    split at h
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · split at h
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inr (h ▸ List.mem_cons_self)
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem AMap.sorted_put {n : Nat} {V : Type} {m : model.AMap n V} (hs : KSorted m) (k : BitVec n)
    (v : V) : KSorted (m.put k v) := by
  induction m with
  | nil => simp [model.AMap.put, KSorted]
  | cons b t ih =>
    obtain ⟨k0, v0⟩ := b
    unfold KSorted at hs ih ⊢
    rw [List.pairwise_cons] at hs
    unfold model.AMap.put
    split
    · rename_i hk; subst hk
      rw [List.pairwise_cons]; exact ⟨fun a ha => hs.1 a ha, hs.2⟩
    · split
      · rename_i hk hlt
        rw [List.pairwise_cons, List.pairwise_cons]
        refine ⟨fun a ha => ?_, hs.1, hs.2⟩
        rcases List.mem_cons.1 ha with ha | ha
        · subst ha; exact hlt
        · exact Nat.lt_trans hlt (hs.1 a ha)
      · rename_i hk hlt
        rw [List.pairwise_cons]
        refine ⟨fun a ha => ?_, ih hs.2⟩
        rcases AMap.mem_put ha with ha | ha
        · subst ha
          have : k.toNat ≠ k0.toNat := fun e => hk (BitVec.eq_of_toNat_eq e)
          simp only; omega
        · exact hs.1 a ha

theorem AMap.sorted_del {n : Nat} {V : Type} {m : model.AMap n V} (hs : KSorted m) (k : BitVec n) :
    KSorted (m.del k) := List.Pairwise.sublist List.filter_sublist hs

/-! ## Messages -/

/-- A `Write2` of write `o`. -/
def w2of (o : Op) : Msg → Bool
  | .write2 m => m.requestId == o.rid && m.clientId == o.cid && m.replicaId == rid32 o.r
  | _ => false

/-- A `Write2Reply` with write `o`'s key. -/
def w2rOf (o : Op) : Msg → Bool
  | .write2Reply m => m.requestId == o.rid && m.clientId == o.cid
  | _ => false

/-- The `Write2Reply` for `o` with `applied` (`true`: 1). -/
def w2rep (o : Op) (b : Bool) : Msg := .write2Reply ⟨o.rid, o.cid, if b then 1 else 0⟩

/-- A message in flight to `j` is accounted for. -/
def MOk (l : List Label) (c : Cfg gNet) (j : Fin 3) : Msg → Prop
  | .read1 m => ∃ R : Fin 3, m.replicaId = rid32 R ∧ j ≠ R ∧
      (m.clientId, m.requestId) ∈ (stR c R).used ∧ 0 ≤ sint.Z m.clientId ∧
      ∀ o ∈ ops l, o.r = R → o.cid = m.clientId → o.rid = m.requestId →
        tagLe (cutSt l o.g R).tag.toP m.vt.t.toP
  | .read1Reply m => (m.clientId, m.requestId) ∈ (stR c j).used ∧ 0 ≤ sint.Z m.clientId ∧
      (∀ o ∈ ops l, o.r = j → o.cid = m.clientId → o.rid = m.requestId →
        ∃ q, q ≠ j ∧ tagLe (cutSt l o.g q).tag.toP m.vt.t.toP ∧
          tagLe (cutSt l o.g j).tag.toP m.vt.t.toP) ∧
      ∃ q, q ≠ j ∧ tagLe m.vt.t.toP (stR c q).tag.toP
  | .read2 _ => False
  | .read2Reply _ => False
  | .write1Reply m => m.vt.v = -1
  | .write2 m => ∃ R : Fin 3, m.replicaId = rid32 R ∧
      (m.clientId, m.requestId) ∈ (stR c R).used ∧ 0 ≤ sint.Z m.clientId
  | .write2Reply m => (m.clientId, m.requestId) ∈ (stR c j).used ∧ 0 ≤ sint.Z m.clientId
  | _ => True

/-- The coordinators' records. -/
structure RRec (l : List Label) (c : Cfg gNet) : Prop where
  rops : ∀ R K rd, (stR c R).rops.get? K = some rd → Fresh rd ∧
    K = shiftInts rd.requestId rd.clientId ∧
    (∃ o ∈ ops l, o.r = R ∧ o.inp = .read ∧ o.cid = rd.clientId ∧ o.rid = rd.requestId) ∧
    ∃ e, (stR c R).ongoingReqs.get? rd.n = some e ∧ e.requestId = rd.requestId ∧
      e.clientId = rd.clientId
  wops : ∀ R K w, (K, w) ∈ (stR c R).wops → K = shiftInts w.requestId w.clientId ∧
    (∃ o ∈ ops l, o.r = R ∧ (∃ v, o.inp = .write v) ∧ o.cid = w.clientId ∧ o.rid = w.requestId) ∧
    (∃ e, (stR c R).ongoingReqs.get? w.n = some e ∧ e.requestId = w.requestId ∧
      e.clientId = w.clientId) ∧
    w.maxValTag.v = -1 ∧ w.numWrite1Applies = 0
  sorted : ∀ R, KSorted (stR c R).wops
  ongoing : ∀ R k e, (stR c R).ongoingReqs.get? k = some e → 0 < sint.Z k ∧
    sint.Z k ≤ sint.Z (stR c R).maxN ∧ (∀ x ∈ e.shortReads, sint.Z x ≤ sint.Z (stR c R).maxN) ∧
    (e.clientId, e.requestId) ∈ (stR c R).used ∧ 0 ≤ sint.Z e.clientId
  maxN : ∀ R, 0 ≤ sint.Z (stR c R).maxN ∧ sint.Z (stR c R).maxN ≤ (stR c R).nReqs ∧
    (stR c R).nReqs ≤ 24
  uniq : ∀ o ∈ ops l, ∀ o' ∈ ops l, o.r = o'.r → o.cid = o'.cid → o.rid = o'.rid → o = o'

/-- Every read short-circuited by the write whose entry number is `n` was created before `g2`. -/
def ShortOk (l : List Label) (R : Fin 3) (sent : Option (Nat × model.Tag)) (s : RState)
    (n : w32) : Prop :=
  ∀ e, s.ongoingReqs.get? n = some e → ∀ k ∈ e.shortReads, ∀ e',
    s.ongoingReqs.get? k = some e' → (s.rops.get? (shiftInts e'.requestId e'.clientId)).isSome →
    ∀ o ∈ ops l, o.r = R → o.cid = e'.clientId → o.rid = e'.requestId →
    ∀ g2 wt, sent = some (g2, wt) → o.g < g2

/-- Write `ow`'s record in state `s` (its coordinator's). -/
def W2St (l : List Label) (ow : Op) (sent : Option (Nat × model.Tag)) (C : List (Fin 3 × Bool))
    (s : RState) : Prop :=
  ∀ w, s.wops.get? ow.key = some w →
    (sent = none ↔ w.sentWrite2Round = false) ∧
    (∀ g2 wt, sent = some (g2, wt) → w.writeTag = some wt) ∧
    sint.Z w.numWrite2Applies = (C.filter (·.2)).length ∧
    ShortOk l ow.r sent s w.n ∧ sint.Z w.numWrite2Replies = C.length

/-- Write `ow`'s `Write2`s, `Write2Reply`s and record. -/
def W2Rec (l : List Label) (c : Cfg gNet) (ow : Op) : Prop :=
  ∃ (sent : Option (Nat × model.Tag)) (C I : List (Fin 3 × Bool)),
    ((C ++ I).map Prod.fst).Nodup ∧
    ((infR c ow.r).filter (w2rOf ow)).Perm (I.map fun p => w2rep ow p.2) ∧
    (∀ q, (infR c q).countP (w2of ow) ≤ 1 ∧
      (q ∈ (C ++ I).map Prod.fst → (infR c q).countP (w2of ow) = 0)) ∧
    (∀ q m, Msg.write2 m ∈ infR c q → w2of ow (.write2 m) = true →
      ∃ g2, sent = some (g2, m.vt.t)) ∧
    (sent = none → C = [] ∧ I = []) ∧
    (∀ g2 wt, sent = some (g2, wt) → g2 ≤ l.length ∧
      ∀ p ∈ C ++ I, (p.2 = true → tagLt (cutSt l g2 p.1).tag.toP wt.toP) ∧
        tagLe wt.toP (stR c p.1).tag.toP) ∧
    W2St l ow sent C (stR c ow.r)

/-- **The read-record invariant.** -/
def RInv (l : List Label) (c : Cfg gNet) : Prop :=
  (∀ j m, m ∈ infR c j → MOk l c j m) ∧ RRec l c ∧
    ∀ ow ∈ ops l, ∀ v, ow.inp = .write v → W2Rec l c ow

/-! ## Old messages stay accounted for -/

theorem mok_mono {l l' : List Label} {c c' : Cfg gNet} {j : Fin 3} {m : Msg}
    (hU : ∀ R, (stR c R).used ⊆ (stR c' R).used)
    (hops : ∀ o ∈ ops l', o ∈ ops l ∨ (o.cid, o.rid) ∉ (stR c o.r).used)
    (hcut : ∀ o ∈ ops l, ∀ q, cutSt l' o.g q = cutSt l o.g q)
    (hT : ∀ q, tagLe (stR c q).tag.toP (stR c' q).tag.toP)
    (h : MOk l c j m) : MOk l' c' j m := by
  cases m with
  | read1 m =>
    obtain ⟨R, h1, h2, h3, h4, h5⟩ := h
    refine ⟨R, h1, h2, hU R h3, h4, fun o ho hr hc hq => ?_⟩
    rcases hops o ho with ho | ho
    · rw [hcut o ho]; exact h5 o ho hr hc hq
    · exact absurd (by rw [hr, hc, hq]; exact h3) ho
  | read1Reply m =>
    obtain ⟨h3, h4, h5, q, hq, h6⟩ := h
    refine ⟨hU j h3, h4, fun o ho hr hc hq => ?_, q, hq, tagLe_trans h6 (hT q)⟩
    rcases hops o ho with ho | ho
    · simp only [hcut o ho]; exact h5 o ho hr hc hq
    · exact absurd (by rw [hr, hc, hq]; exact h3) ho
  | write2 m =>
    obtain ⟨R, h1, h3, h4⟩ := h
    exact ⟨R, h1, hU R h3, h4⟩
  | write2Reply m =>
    obtain ⟨h3, h4⟩ := h
    exact ⟨hU j h3, h4⟩
  | _ => exact h

theorem rinv_init : RInv [] (Cfg.init gNet) := by
  refine ⟨?_, ⟨fun R K rd h => ?_, fun R K w h => ?_, fun R => ?_,
    fun R k e h => ?_, fun R => ?_, fun o ho => by simp [ops_eq] at ho⟩, ?_⟩
  · intro j m hm; change m ∈ ([] : List Msg) at hm; cases hm
  · change (RState.init R.val).rops.get? K = some rd at h; cases h
  · change (K, w) ∈ (RState.init R.val).wops at h; cases h
  · change KSorted (RState.init R.val).wops; exact List.Pairwise.nil
  · change (RState.init R.val).ongoingReqs.get? k = some e at h; cases h
  · change 0 ≤ sint.Z (RState.init R.val).maxN ∧
      sint.Z (RState.init R.val).maxN ≤ (RState.init R.val).nReqs ∧ (RState.init R.val).nReqs ≤ 24
    simp [RState.init, sint.Z]
  · intro ow ho; simp [ops_eq] at ho

end Perennial.gryff.pure
