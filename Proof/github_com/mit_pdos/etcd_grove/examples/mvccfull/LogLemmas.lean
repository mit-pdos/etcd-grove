/-
mvccfull's writer: the operation log's model facts (pure). Lean-first (no Rocq counterpart).

`Writer.lean` states them (`logOk_once`, `logOk_hist`, `runM_mono`, `logOk_leases`,
`logOk_recover`); this module proves them (`*_holds`, the same statements) from one invariant of the
model along a valid log (`MInv`, `runM_inv`): each revision of the history is the tester's model
(`pendOf`) of its own changes from the revision before, and the store's state at it; the store's
log is well formed, changes each key once per revision, and is reachable; the live leases are a
sublist of the granted ids, which increase; every key of the last state is on no lease or a live
one. One operation's revision (`opPend`) keeps it (`PGood`: its changes rebuild it, and, over keys
without repeats, are distinct, delete only keys present and leave the deleted keys absent; for a
write transaction, `subsOk`'s order: `txn_good`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterShares

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-! ## One revision's pending model -/

theorem toChange_key (c : change) : (toChange c).key = c.key' := by
  unfold toChange; split <;> rfl

theorem putRec_val (M : GMap GoString kvRec) (rev : w64) (k v : GoString) (l : w64) :
    (putRec M rev k v l).val' = v := by
  unfold putRec; split <;> rfl

theorem putRec_lease (M : GMap GoString kvRec) (rev : w64) (k v : GoString) (l : w64) :
    (putRec M rev k v l).lease' = l := by
  unfold putRec; split <;> rfl

theorem toChange_put (M : GMap GoString kvRec) (rev : w64) (k v : GoString) (l : w64) :
    toChange { del' := false, key' := k, kv' := putRec M rev k v l } = .put k v l := by
  simp [toChange, putRec_val, putRec_lease]

theorem toChange_delChange (k : GoString) : toChange (delChange k) = .del k := by
  simp [toChange, delChange]

/-- The keys of the last state are on no lease or a live one. -/
def LeaseSt (L : List w64) (M : GMap GoString kvRec) : Prop :=
  ∀ k e, M !! k = some e → e.lease' = W64 0 ∨ e.lease' ∈ L

/-- **A pending model built from `M` at `rev`** (over the keys `ks`): its changes rebuild it, their
keys are the tester's, and, the keys without repeats, they change each key once, delete only keys
present, and leave the deleted keys absent. -/
def PGood (ks : List GoString) (M : GMap GoString kvRec) (rev : w64) (P : PendM) : Prop :=
  pendOf M rev (P.chs.map toChange) = P ∧ (∀ c ∈ P.chs, c.key' ∈ ks) ∧
  (ks.Nodup →
    (P.chs.map change.key').Nodup ∧
    (∀ i k, (P.chs.map toChange)[i]? = some (.del k) →
      ((pendOf M rev ((P.chs.map toChange).take i)).st !! k).isSome) ∧
    (∀ c ∈ P.chs, c.del' = true → P.st !! c.key' = none))

theorem PGood.start (ks : List GoString) (M : GMap GoString kvRec) (rev : w64) :
    PGood ks M rev ⟨rev, M, []⟩ := by
  refine ⟨rfl, by simp, fun _ => ⟨by simp, fun i k h => by simp at h, by simp⟩⟩

theorem PGood.put {ks : List GoString} {M : GMap GoString kvRec} {rev : w64} {P : PendM}
    (h : PGood ks M rev P) (k v : GoString) (l : w64) (hk : k ∈ ks)
    (hn : ks.Nodup → k ∉ P.chs.map change.key') : PGood ks M rev (P.put k v l) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hch : ((P.put k v l).chs.map toChange) = P.chs.map toChange ++ [.put k v l] := by
    simp only [PendM.put, List.map_append, List.map_cons, List.map_nil, toChange_put]
  refine ⟨?_, ?_, fun hks => ?_⟩
  · rw [hch, pendOf_put, h1]
  · intro c hc
    simp only [PendM.put, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc
    · exact h2 c hc
    · subst hc; exact hk
  · obtain ⟨g1, g2, g3⟩ := h3 hks
    have hnk := hn hks
    refine ⟨?_, ?_, ?_⟩
    · simp only [PendM.put, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨g1, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      intro he; subst he; exact hnk ha
    · intro i k' hi
      rw [hch] at hi ⊢
      rcases Nat.lt_or_ge i (P.chs.map toChange).length with hlt | hge
      · rw [List.getElem?_append_left hlt] at hi
        rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
        exact g2 i k' hi
      · rw [List.getElem?_append_right hge] at hi
        rcases hj : i - (P.chs.map toChange).length with _ | j
        · rw [hj] at hi; simp at hi
        · rw [hj] at hi; simp at hi
    · intro c hc hd
      simp only [PendM.put, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc
      · have hne : k ≠ c.key' := by
          intro he; apply hnk; rw [he]; exact List.mem_map_of_mem hc
        simp only [PendM.put]
        rw [GMap.lookup_insert_ne _ _ hne]
        exact g3 c hc hd
      · subst hc; simp at hd

theorem PGood.delOne {ks : List GoString} {M : GMap GoString kvRec} {rev : w64} {P : PendM}
    (h : PGood ks M rev P) (k : GoString) (hk : k ∈ ks)
    (hn : ks.Nodup → (P.st !! k).isSome ∧ k ∉ P.chs.map change.key') :
    PGood ks M rev (P.delOne k) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hch : ((P.delOne k).chs.map toChange) = P.chs.map toChange ++ [.del k] := by
    simp only [PendM.delOne, List.map_append, List.map_cons, List.map_nil, toChange_delChange]
  refine ⟨?_, ?_, fun hks => ?_⟩
  · rw [hch, pendOf_append, h1]; rfl
  · intro c hc
    simp only [PendM.delOne, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc
    · exact h2 c hc
    · subst hc; exact hk
  · obtain ⟨g1, g2, g3⟩ := h3 hks
    obtain ⟨hp, hnk⟩ := hn hks
    refine ⟨?_, ?_, ?_⟩
    · simp only [PendM.delOne, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨g1, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      intro he; apply hnk; rw [← he]; simpa [delChange] using ha
    · intro i k' hi
      rw [hch] at hi ⊢
      rcases Nat.lt_or_ge i (P.chs.map toChange).length with hlt | hge
      · rw [List.getElem?_append_left hlt] at hi
        rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
        exact g2 i k' hi
      · rw [List.getElem?_append_right hge] at hi
        rcases hj : i - (P.chs.map toChange).length with _ | j
        · rw [hj] at hi
          simp only [List.getElem?_cons_zero, Option.some.injEq, Change.del.injEq] at hi
          subst hi
          have hi' : i = (P.chs.map toChange).length := by omega
          rw [hi', List.take_append_of_le_length (Nat.le_refl _), List.take_length, h1]
          exact hp
        · rw [hj] at hi; simp at hi
    · intro c hc hd
      simp only [PendM.delOne, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc
      · simp only [PendM.delOne]
        by_cases he : k = c.key'
        · rw [← he]; exact GMap.lookup_delete _ _
        · rw [GMap.lookup_delete_ne _ he]
          exact g3 c hc hd
      · subst hc; simp only [PendM.delOne, delChange]; exact GMap.lookup_delete _ _

theorem foldl_delOne_eq (l : List GoString) : ∀ P : PendM,
    l.foldl PendM.delOne P = { P with st := delAll l P.st, chs := P.chs ++ l.map delChange } := by
  induction l with
  | nil => intro P; simp [delAll]
  | cons k l ih =>
    intro P
    rw [List.foldl_cons, ih]
    simp [PendM.delOne, delAll, List.append_assoc]

theorem PendM.del_eq_foldl_delOne (P : PendM) (keys : List GoString) (endNil : Bool)
    (kk e : GoString) : P.del keys endNil kk e = (P.delKeys keys endNil kk e).foldl PendM.delOne P := by
  rw [foldl_delOne_eq]; rfl

theorem PGood.foldl_delOne {ks : List GoString} {M : GMap GoString kvRec} {rev : w64}
    (l : List GoString) : ∀ P : PendM, PGood ks M rev P → (∀ k ∈ l, k ∈ ks) →
    (ks.Nodup → l.Nodup ∧ ∀ k ∈ l, (P.st !! k).isSome ∧ k ∉ P.chs.map change.key') →
    PGood ks M rev (l.foldl PendM.delOne P) := by
  induction l with
  | nil => intro P h _ _; exact h
  | cons k l ih =>
    intro P h hk hn
    rw [List.foldl_cons]
    refine ih _ (h.delOne k (hk k (List.mem_cons_self ..)) fun hks =>
      (hn hks).2 k (List.mem_cons_self ..)) (fun x hx => hk x (List.mem_cons_of_mem _ hx)) ?_
    intro hks
    obtain ⟨hnd, hp⟩ := hn hks
    rw [List.nodup_cons] at hnd
    refine ⟨hnd.2, fun x hx => ?_⟩
    have hxk : k ≠ x := fun he => hnd.1 (he ▸ hx)
    obtain ⟨hx1, hx2⟩ := hp x (List.mem_cons_of_mem _ hx)
    refine ⟨?_, ?_⟩
    · simp only [PendM.delOne]; rw [GMap.lookup_delete_ne _ hxk]; exact hx1
    · simp only [PendM.delOne, List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hx2, fun he => hxk (by simpa [delChange] using he.symm)⟩

theorem LeaseSt.delAll {L : List w64} {M : GMap GoString kvRec} (h : LeaseSt L M)
    (l : List GoString) : LeaseSt L (delAll l M) := by
  intro k e he
  rw [delAll_lookup] at he
  split at he
  · cases he
  · exact h k e he

theorem LeaseSt.mono {L L' : List w64} {M : GMap GoString kvRec} (h : LeaseSt L M)
    (hL : ∀ x ∈ L, x ∈ L') : LeaseSt L' M := by
  intro k e he
  rcases h k e he with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (hL _ h1)

theorem LeaseSt.put {L : List w64} {P : PendM} (h : LeaseSt L P.st) (k v : GoString) (l : w64)
    (hl : l = W64 0 ∨ l ∈ L) : LeaseSt L (P.put k v l).st := by
  intro x e he
  simp only [PendM.put] at he
  by_cases hx : k = x
  · subst hx
    rw [GMap.lookup_insert] at he
    cases he
    rw [putRec_lease]; exact hl
  · rw [GMap.lookup_insert_ne _ _ hx] at he
    exact h x e he

/-! ## A write transaction's sub-operations -/

/-- Each change of `P` is from a sub-operation before the `j`-th: a put of its key, or a delete
of a range holding it. -/
def Prov (subs : List SubM) (j : Nat) (P : PendM) : Prop :=
  ∀ c ∈ P.chs, ∃ i < j, ∃ a, subs[i]? = some a ∧
    ((c.del' = false ∧ a.kind = W64 0 ∧ a.key = c.key') ∨
     (c.del' = true ∧ a.kind = W64 1 ∧ inRangeM a.endNil a.key a.e c.key' = true))

theorem Prov.mono {subs : List SubM} {j j' : Nat} {P : PendM} (h : Prov subs j P) (hj : j ≤ j') :
    Prov subs j' P := by
  intro c hc
  obtain ⟨i, hi, a, ha, h'⟩ := h c hc
  exact ⟨i, by omega, a, ha, h'⟩

theorem PendM.del_st (P : PendM) (keys : List GoString) (endNil : Bool) (kk e : GoString) :
    (P.del keys endNil kk e).st = delAll (P.delKeys keys endNil kk e) P.st := rfl

theorem PendM.del_chs (P : PendM) (keys : List GoString) (endNil : Bool) (kk e : GoString) :
    (P.del keys endNil kk e).chs = P.chs ++ (P.delKeys keys endNil kk e).map delChange := rfl

theorem mem_delKeys {P : PendM} {keys : List GoString} {endNil : Bool} {kk e x : GoString}
    (hx : x ∈ P.delKeys keys endNil kk e) :
    x ∈ keys ∧ (P.st !! x).isSome ∧ inRangeM endNil kk e x = true := by
  simp only [PendM.delKeys, matchKeys, List.mem_filter, Bool.and_eq_true] at hx
  exact ⟨hx.1, hx.2.1, hx.2.2⟩

/-- **A write transaction's sub-operations, as `genSubs` makes them, make a good revision.** -/
theorem txn_good (ks : List GoString) (M : GMap GoString kvRec) (rev : w64) (L : List w64)
    (subs : List SubM) (hs : subsOk ks L subs) (hl : LeaseSt L M) : ∀ j : Nat,
    PGood ks M rev ((subs.take j).foldl (subStep ks) ⟨rev, M, []⟩) ∧
    LeaseSt L ((subs.take j).foldl (subStep ks) ⟨rev, M, []⟩).st ∧
    Prov subs j ((subs.take j).foldl (subStep ks) ⟨rev, M, []⟩) := by
  intro j
  induction j with
  | zero => exact ⟨PGood.start ks M rev, hl, fun c hc => by simp at hc⟩
  | succ j ih =>
    obtain ⟨hg, hls, hpv⟩ := ih
    rw [List.take_add_one]
    cases hb : subs[j]? with
    | none => simp only [Option.toList_none, List.append_nil]; exact ⟨hg, hls, hpv.mono (by omega)⟩
    | some b =>
      simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize hP : (subs.take j).foldl (subStep ks) ⟨rev, M, []⟩ = P at hg hls hpv
      have hbm : b ∈ subs := List.mem_of_getElem? hb
      unfold subStep
      by_cases h0 : b.kind = W64 0
      · simp only [h0, ↓reduceIte]
        have hb1 := (hs.1 b hbm h0)
        refine ⟨hg.put _ _ _ hb1.1 ?_, hls.put _ _ _ hb1.2, ?_⟩
        · intro _ hin
          obtain ⟨c, hc, hck⟩ := List.mem_map.1 hin
          obtain ⟨i, hi, a, ha, hor⟩ := hpv c hc
          have hab := hs.2 i j a b hi ha hb
          rcases hor with ⟨-, ha0, hak⟩ | ⟨-, ha1, har⟩
          · exact (hab.1 ha0 h0) (hak.trans hck)
          · rw [hck] at har; rw [(hab.2.1 ha1 h0)] at har; cases har
        · intro c hc
          simp only [PendM.put, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with hc | hc
          · exact (hpv c hc).imp fun i ⟨hi, h⟩ => ⟨by omega, h⟩
          · subst hc; exact ⟨j, by omega, b, hb, Or.inl ⟨rfl, h0, rfl⟩⟩
      · simp only [h0, ↓reduceIte]
        by_cases h1 : b.kind = W64 1
        · simp only [h1, ↓reduceIte]
          rw [PendM.del_eq_foldl_delOne]
          refine ⟨?_, ?_, ?_⟩
          · refine hg.foldl_delOne _ _ (fun x hx => (mem_delKeys hx).1) fun hks => ⟨?_, ?_⟩
            · exact hks.filter _
            · intro x hx
              obtain ⟨-, hx2, hx3⟩ := mem_delKeys hx
              refine ⟨hx2, fun hin => ?_⟩
              obtain ⟨c, hc, hck⟩ := List.mem_map.1 hin
              obtain ⟨i, hi, a, ha, hor⟩ := hpv c hc
              have hab := hs.2 i j a b hi ha hb
              rcases hor with ⟨-, ha0, hak⟩ | ⟨hd, -, -⟩
              · have := hab.2.2 ha0 h1
                rw [hak, hck, hx3] at this; cases this
              · have := (hg.2.2 hks).2.2 c hc hd
                rw [hck] at this; rw [this] at hx2; cases hx2
          · rw [← PendM.del_eq_foldl_delOne, PendM.del_st]; exact hls.delAll _
          · rw [← PendM.del_eq_foldl_delOne]
            intro c hc
            rw [PendM.del_chs, List.mem_append] at hc
            rcases hc with hc | hc
            · exact (hpv c hc).imp fun i ⟨hi, h⟩ => ⟨by omega, h⟩
            · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
              exact ⟨j, by omega, b, hb, Or.inr ⟨rfl, h1, (mem_delKeys hx).2.2⟩⟩
        · simp only [h1, ↓reduceIte]; exact ⟨hg, hls, hpv.mono (by omega)⟩

/-! ## One operation's revision -/

/-- The live leases after an operation. -/
theorem opStep_leases (ks : List GoString) (s : MSt) (o : OpM) :
    (opStep ks s o).leases = if o.kind = kGrant then s.leases ++ [o.id]
      else if o.kind = kRevoke then s.leases.filter (· != o.id) else s.leases := rfl

/-- **An operation valid at `s` makes a good revision**, and the keys of its state are on no lease
or one live after it. -/
theorem opPend_good (ks : List GoString) (s : MSt) (o : OpM) (hv : opValid ks s o)
    (hdom : ∀ k, (lastSt s.hs !! k).isSome → k ∈ ks) (hl : LeaseSt s.leases (lastSt s.hs)) :
    PGood ks (lastSt s.hs) (W64 (s.hs.length : Int)) (opPend ks s o) ∧
    LeaseSt (opStep ks s o).leases (opPend ks s o).st := by
  have hP0 := PGood.start ks (lastSt s.hs) (W64 (s.hs.length : Int))
  obtain ⟨-, -, hvp, hvt, -, hvr, -⟩ := hv
  rw [opStep_leases]
  unfold opPend
  by_cases h0 : o.kind = kPut
  · have hg : ¬ o.kind = kGrant := by rw [h0]; decide
    have hr : ¬ o.kind = kRevoke := by rw [h0]; decide
    simp only [eq_true h0, hg, hr, ↓reduceIte]
    obtain ⟨hk, hle⟩ := hvp h0
    exact ⟨hP0.put _ _ _ hk (fun _ => by simp), LeaseSt.put hl _ _ _ hle⟩
  by_cases h1 : o.kind = kDelete
  · have hg : ¬ o.kind = kGrant := by rw [h1]; decide
    have hr : ¬ o.kind = kRevoke := by rw [h1]; decide
    simp only [h0, eq_true h1, hg, hr, ↓reduceIte]
    rw [PendM.del_eq_foldl_delOne]
    refine ⟨hP0.foldl_delOne _ _ (fun x hx => (mem_delKeys hx).1) fun hks =>
      ⟨hks.filter _, fun x hx => ⟨(mem_delKeys hx).2.1, by simp⟩⟩, ?_⟩
    rw [← PendM.del_eq_foldl_delOne, PendM.del_st]; exact hl.delAll _
  by_cases h2 : o.kind = kTxn
  · have hg : ¬ o.kind = kGrant := by rw [h2]; decide
    have hr : ¬ o.kind = kRevoke := by rw [h2]; decide
    simp only [h0, h1, eq_true h2, hg, hr, ↓reduceIte]
    cases hw : o.write
    · exact ⟨hP0, hl⟩
    · have := txn_good ks (lastSt s.hs) (W64 (s.hs.length : Int)) s.leases o.subs
        (hvt h2 hw) hl o.subs.length
      rw [List.take_length] at this
      exact ⟨this.1, this.2.1⟩
  by_cases h4 : o.kind = kRevoke
  · have hg : ¬ o.kind = kGrant := by rw [h4]; decide
    simp only [h0, h1, h2, eq_true h4, hg, ↓reduceIte]
    refine ⟨hP0.foldl_delOne _ _ (fun x hx => (List.mem_filter.1 hx).1) fun hks =>
      ⟨hks.filter _, fun x hx => ⟨?_, by simp⟩⟩, ?_⟩
    · have := (List.mem_filter.1 hx).2
      unfold onLease at this
      simp only at this ⊢
      revert this; cases lastSt s.hs !! x <;> simp
    · rw [foldl_delOne_eq]
      intro k e he
      simp only at he
      rw [delAll_lookup] at he
      split at he
      · cases he
      · rename_i hnk
        have hkks : k ∈ ks := hdom k (by rw [he]; rfl)
        have hon : onLease (lastSt s.hs) o.id k = false := by
          cases hb : onLease (lastSt s.hs) o.id k
          · rfl
          · exact absurd (List.mem_filter.2 ⟨hkks, hb⟩) hnk
        unfold onLease at hon
        rw [he] at hon
        simp only [decide_eq_false_iff_not] at hon
        rcases hl k e he with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_filter.2 ⟨h, by simp [hon]⟩)
  · simp only [h0, h1, h2, h4, ↓reduceIte]
    refine ⟨hP0, ?_⟩
    split
    · exact hl.mono fun x hx => List.mem_append_left _ hx
    · exact hl

/-! ## The model's invariant along a valid log -/

theorem stMatch_foldl (ks : List GoString) (cs : List Change) (hcs : ∀ c ∈ cs, c.key ∈ ks) :
    ∀ (P : PendM) (s : List EtcdKv), s.Pairwise etcdKvLess → stMatch ks P.st s →
      stMatch ks (cs.foldl PendM.step P).st (cs.foldl (applyChange P.rev) s) := by
  induction cs with
  | nil => intro P s _ h; exact h
  | cons c cs ih =>
    intro P s hs hM
    simp only [List.foldl_cons]
    have hrev : (P.step c).rev = P.rev := by cases c <;> rfl
    have hstep : stMatch ks (P.step c).st (applyChange P.rev s c) := by
      cases c with
      | put k v l => exact stMatch_put ks P.st s hs P.rev k v l hM (hcs _ (List.mem_cons_self ..))
      | del k => exact stMatch_del ks P.st s P.rev k hM
    have := ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (P.step c) (applyChange P.rev s c)
      (applyChange_sorted hs P.rev c) hstep
    rw [hrev] at this
    exact this

theorem stMatch_pendOf (ks : List GoString) (M : GMap GoString kvRec) (rev : w64) (s : List EtcdKv)
    (hs : s.Pairwise etcdKvLess) (hM : stMatch ks M s) (cs : List Change)
    (hcs : ∀ c ∈ cs, c.key ∈ ks) : stMatch ks (pendOf M rev cs).st (applyChanges rev s cs) :=
  stMatch_foldl ks cs hcs ⟨rev, M, []⟩ s hs hM

theorem logOfHist_length (Hs : List HRev) : (logOfHist Hs).length = Hs.length := by
  simp [logOfHist]

theorem logOfHist_append (Hs : List HRev) (x : HRev) :
    logOfHist (Hs ++ [x]) = logOfHist Hs ++ [x.2.map toChange] := by
  simp [logOfHist]

theorem logOfHist_getElem? (Hs : List HRev) (r : Nat) :
    (logOfHist Hs)[r]? = Hs[r]?.map fun e => e.2.map toChange := by
  simp [logOfHist]

/-- The leases' part of the invariant. -/
def LeasesOk (s : MSt) : Prop :=
  s.leases.Sublist s.granted ∧ s.granted.Pairwise (fun a b => sint.Z a < sint.Z b) ∧
  (∀ g ∈ s.granted, 0 < sint.Z g) ∧ LeaseSt s.leases (lastSt s.hs)

/-- **The model's invariant**: the history starts with the two empty revisions; each revision is
the tester's model of its changes from the one before, and matches the store's state there; the
leases' part; over keys without repeats, the store's log changes each key once per revision, is
well formed, and (with the compaction revision) reachable. -/
def MInv (ks : List GoString) (s : MSt) : Prop :=
  hist0 <+: s.hs ∧
  (∀ (r : Nat) (e : HRev), 1 ≤ r → s.hs[r]? = some e → ∃ e', s.hs[r - 1]? = some e' ∧
    e = ((pendOf e'.1 (W64 (r : Int)) (e.2.map toChange)).st,
      (pendOf e'.1 (W64 (r : Int)) (e.2.map toChange)).chs)) ∧
  (∀ (r : Nat) (e : HRev), s.hs[r]? = some e → stMatch ks e.1 (stateAt (logOfHist s.hs) r)) ∧
  LeasesOk s ∧
  (ks.Nodup → onceUpToAll (logOfHist s.hs) ∧ LogWf (logOfHist s.hs) ∧
    MvccReachable ⟨logOfHist s.hs, s.crev, none⟩)

theorem mInv_start (ks : List GoString) : MInv ks mStart := by
  have hL : logOfHist mStart.hs = [[], []] := rfl
  have hst : ∀ r, stateAt [[], []] r = [] := by
    intro r; rcases r with _ | _ | r <;> rfl
  refine ⟨List.prefix_refl _, ?_, ?_, ?_, fun _ => ⟨?_, ?_, ?_⟩⟩
  · intro r e hr he
    rcases r with _ | _ | r
    · omega
    · simp only [mStart, hist0] at he ⊢
      simp at he; subst he
      exact ⟨(∅, []), rfl, rfl⟩
    · simp [mStart, hist0] at he
  · intro r e he
    rw [hL, hst]
    have he1 : e.1 = ∅ := by
      rcases r with _ | _ | r <;> simp [mStart, hist0] at he <;> subst he <;> rfl
    rw [he1]
    exact ⟨fun k => by simp [findKey], by simp⟩
  · refine ⟨List.Sublist.slnil, List.Pairwise.nil, by simp [mStart], ?_⟩
    intro k e he
    simp [mStart, lastSt, hist0] at he
  · rw [hL]; intro r
    rcases r with _ | _ | r <;> simp
  · rw [hL]
    refine ⟨rfl, fun r cs i k hr hi => ?_⟩
    rcases r with _ | _ | r
    · simp at hr; subst hr; simp at hi
    · simp at hr; subst hr; simp at hi
    · simp at hr
  · exact MvccReachable.start

theorem opStep_granted (ks : List GoString) (s : MSt) (o : OpM) :
    (opStep ks s o).granted = if o.kind = kGrant then s.granted ++ [o.id] else s.granted := rfl

theorem leasesOk_step (ks : List GoString) (s : MSt) (o : OpM) (hL : LeasesOk s)
    (hv : opValid ks s o) (hls : LeaseSt (opStep ks s o).leases (lastSt (opStep ks s o).hs)) :
    LeasesOk (opStep ks s o) := by
  obtain ⟨h1, h2, h3, -⟩ := hL
  obtain ⟨-, -, -, -, hvg, -, -⟩ := hv
  refine ⟨?_, ?_, ?_, hls⟩
  · rw [opStep_leases, opStep_granted]
    by_cases hg : o.kind = kGrant
    · simp only [hg, ↓reduceIte]; exact h1.append (List.Sublist.refl _)
    · simp only [hg, ↓reduceIte]
      split
      · exact (List.filter_sublist).trans h1
      · exact h1
  · rw [opStep_granted]
    by_cases hg : o.kind = kGrant
    · simp only [hg, ↓reduceIte]
      rw [List.pairwise_append]
      refine ⟨h2, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb; exact (hvg hg).2 a ha
    · simp only [hg, ↓reduceIte]; exact h2
  · rw [opStep_granted]
    by_cases hg : o.kind = kGrant
    · simp only [hg, ↓reduceIte]
      intro g hg'
      rcases List.mem_append.1 hg' with h | h
      · exact h3 g h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; exact (hvg hg).1
    · simp only [hg, ↓reduceIte]; exact h3

theorem lastSt_of {Hs : List HRev} {e : HRev} (he : Hs[Hs.length - 1]? = some e) :
    lastSt Hs = e.1 := by
  unfold lastSt; rw [he]; rfl

theorem stateAt_last (L : Log) (hL : 1 ≤ L.length) : stateAt L (L.length - 1) = stateAfter L := by
  unfold stateAt; rw [List.take_of_length_le (by omega)]

/-- **One valid operation keeps the invariant.** -/
theorem mInv_step (ks : List GoString) (s : MSt) (o : OpM) (hI : MInv ks s)
    (hv : opValid ks s o) : MInv ks (opStep ks s o) := by
  obtain ⟨hpre, hrev, hmatch, hlo, hnd⟩ := hI
  have hlen : 2 ≤ s.hs.length := by
    have := hpre.length_le; simp [hist0] at this; omega
  obtain ⟨eL, heL⟩ : ∃ e, s.hs[s.hs.length - 1]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hM := hmatch _ _ heL
  rw [← lastSt_of heL] at hM
  have hdom : ∀ k, (lastSt s.hs !! k).isSome → k ∈ ks := by
    intro k hk
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
    have hf := hM.1 k
    rw [hx] at hf
    have hm := List.mem_of_find?_eq_some hf
    have hkk : (kvOfRec k x).key = k := rfl
    have := hM.2 _ hm
    rwa [hkk] at this
  obtain ⟨hg, hls⟩ := opPend_good ks s o hv hdom hlo.2.2.2
  have hlast : lastSt (opStep ks s o).hs = (opPend ks s o).st := by
    simp only [opStep, histAfter]
    split
    · rename_i hc
      have h1 := hg.1
      rw [hc, List.map_nil, pendOf_nil] at h1
      rw [← h1]
    · simp [lastSt]
  have hlo' := leasesOk_step ks s o hlo hv (hlast ▸ hls)
  by_cases hc : (opPend ks s o).chs = []
  · -- no revision: the history unchanged
    have hhs : (opStep ks s o).hs = s.hs := by simp only [opStep, histAfter, hc, ↓reduceIte]
    unfold MInv
    rw [hhs]
    refine ⟨hpre, hrev, hmatch, hlo', fun hks => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hnd hks
    refine ⟨h1, h2, ?_⟩
    have hcr : (opStep ks s o).crev = if (o.kind = kCompact ∧ s.crev < sint.Z o.rev ∧
        sint.Z o.rev ≤ (s.rev : Int)) then sint.Z o.rev else s.crev := by
      simp only [opStep, decide_eq_true_eq]
    rw [hcr]
    split
    · rename_i hcok
      obtain ⟨hk, hlt, hle⟩ := hcok
      have h1r := hv.2.2.2.2.2.2 hk
      have hrv : (⟨logOfHist s.hs, s.crev, none⟩ : MvccState).rev = s.rev := by
        simp [MvccState.rev, MSt.rev, logOfHist_length]
      exact MvccReachable.compact _ _ h3 rfl h1r hlt (by rw [hrv]; exact hle)
    · exact h3
  · -- a new revision
    have hhs : (opStep ks s o).hs = s.hs ++ [((opPend ks s o).st, (opPend ks s o).chs)] := by
      simp only [opStep, histAfter, hc, ↓reduceIte]
    have hk5 : ¬ o.kind = kCompact := by
      intro hk
      apply hc
      unfold opPend
      have hp : ¬ o.kind = kPut := by rw [hk]; decide
      have hd : ¬ o.kind = kDelete := by rw [hk]; decide
      have ht : ¬ o.kind = kTxn := by rw [hk]; decide
      have hr : ¬ o.kind = kRevoke := by rw [hk]; decide
      simp only [hp, hd, ht, hr, ↓reduceIte]
    have hcr : (opStep ks s o).crev = s.crev := by
      simp only [opStep, hk5, false_and, decide_false, Bool.false_eq_true, ↓reduceIte]
    generalize hP : opPend ks s o = P at hg hc hhs
    have hPe := hg.1
    have hLn : (logOfHist s.hs).length = s.hs.length := logOfHist_length _
    have hL' : logOfHist (opStep ks s o).hs = (logOfHist s.hs) ++ [(P.chs.map toChange)] := by
      rw [hhs, logOfHist_append]
    have hMe : eL.1 = (lastSt s.hs) := (lastSt_of heL).symm
    have hsM : stMatch ks (lastSt s.hs) (stateAfter (logOfHist s.hs)) := by
      have := hM; rw [← stateAt_last (logOfHist s.hs) (by omega), hLn]; exact this
    have hkeys : ∀ c ∈ (P.chs.map toChange), c.key ∈ ks := by
      intro c hc1
      obtain ⟨c', hc2, rfl⟩ := List.mem_map.1 hc1
      rw [toChange_key]; exact hg.2.1 c' hc2
    unfold MInv
    rw [hL', hhs, hcr]
    refine ⟨hpre.trans (List.prefix_append _ _), ?_, ?_, hlo', fun hks => ?_⟩
    · intro r e hr he
      rcases Nat.lt_or_ge r s.hs.length with hlt | hge
      · rw [List.getElem?_append_left hlt] at he
        rw [List.getElem?_append_left (by omega)]
        exact hrev r e hr he
      · rw [List.getElem?_append_right hge] at he
        rcases hj : r - s.hs.length with _ | j
        · rw [hj] at he
          simp only [List.getElem?_cons_zero, Option.some.injEq] at he
          subst he
          have hrn : r = s.hs.length := by omega
          subst hrn
          refine ⟨eL, by rw [List.getElem?_append_left (by omega)]; exact heL, ?_⟩
          simp only
          rw [hMe, hPe]
        · rw [hj] at he; simp at he
    · intro r e he
      rcases Nat.lt_or_ge r s.hs.length with hlt | hge
      · rw [List.getElem?_append_left hlt] at he
        rw [stateAt_append_lt _ _ (by omega)]
        exact hmatch r e he
      · rw [List.getElem?_append_right hge] at he
        rcases hj : r - s.hs.length with _ | j
        · rw [hj] at he
          simp only [List.getElem?_cons_zero, Option.some.injEq] at he
          subst he
          rw [stateAt_append_ge _ _ (by omega), hLn]
          have := stMatch_pendOf ks (lastSt s.hs) (W64 (s.hs.length : Int)) (stateAfter (logOfHist s.hs)) (stateAfter_sorted (logOfHist s.hs)) hsM
            (P.chs.map toChange) hkeys
          rw [hPe] at this
          exact this
        · rw [hj] at he; simp at he
    · obtain ⟨h1, h2, h3⟩ := hnd hks
      obtain ⟨g1, g2, g3⟩ := hg.2.2 hks
      have hwf : LogWf ((logOfHist s.hs) ++ [(P.chs.map toChange)]) := by
        refine ⟨by rw [List.getElem?_append_left (by omega)]; exact h2.1, ?_⟩
        intro r cs i k hr hi
        rcases Nat.lt_or_ge r s.hs.length with hlt | hge
        · rw [List.getElem?_append_left (by omega)] at hr
          rw [stateAt_append_lt _ _ (by omega)]
          exact h2.2 r cs i k hr hi
        · rw [List.getElem?_append_right (by omega)] at hr
          rcases hj : r - (logOfHist s.hs).length with _ | j
          · rw [hj] at hr
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
            subst hr
            have hrn : r = s.hs.length := by omega
            subst hrn
            rw [stateAt_append_lt _ _ (by omega)]
            have hsa : stateAt (logOfHist s.hs) (s.hs.length - 1) = stateAfter (logOfHist s.hs) := by
              rw [← hLn]; exact stateAt_last _ (by omega)
            rw [hsa]
            have hf := fkMatch_pendOf (lastSt s.hs) (W64 (s.hs.length : Int))
              (stateAfter (logOfHist s.hs)) (stateAfter_sorted (logOfHist s.hs))
              hsM.1 ((P.chs.map toChange).take i) k
            unfold applyChanges at hf ⊢
            rw [hf]
            have := g2 i k hi
            revert this
            cases (pendOf (lastSt s.hs) (W64 (s.hs.length : Int)) ((P.chs.map toChange).take i)).st !! k <;> simp
          · rw [hj] at hr; simp at hr
      refine ⟨?_, hwf, ?_⟩
      · intro r
        rcases Nat.lt_or_ge r s.hs.length with hlt | hge
        · have := h1 r
          rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
            ← List.getD_eq_getElem?_getD]
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
          rcases hj : r - (logOfHist s.hs).length with _ | j
          · simp only [List.getElem?_cons_zero, Option.getD_some, List.map_map]
            have : (Change.key ∘ toChange) = change.key' := funext toChange_key
            rw [this]; exact g1
          · simp
      · have hpne : (P.chs.map toChange) ≠ [] := by
          intro h; exact hc (List.map_eq_nil_iff.1 h)
        have heq : (⟨(logOfHist s.hs) ++ [(P.chs.map toChange)], s.crev, none⟩ : MvccState) =
            ((⟨(logOfHist s.hs), s.crev, none⟩ : MvccState).notify (P.chs.map toChange)).commitPending := by
          simp [MvccState.notify, MvccState.commitPending, commitLog, hpne]
        rw [heq]
        exact MvccReachable.commit _ (MvccReachable.notify _ _ h3 rfl hwf)

/-- **The invariant along a valid log.** -/
theorem runM_inv (ks : List GoString) (ops : List OpM) (h : logOk ks ops) :
    ∀ n, MInv ks (runM ks ops n) := by
  intro n
  induction n with
  | zero => rw [runM_zero]; exact mInv_start ks
  | succ n ih =>
    cases hn : ops[n]? with
    | none =>
      have : runM ks ops (n + 1) = runM ks ops n := by
        unfold runM; rw [List.take_add_one, hn]; simp
      rw [this]; exact ih
    | some o =>
      rw [runM_succ ks ops n o hn]
      exact mInv_step ks _ o ih (h n o hn)

theorem nodup_of_sorted {ks : List GoString} (hks : ks.Pairwise go.GoStringLt) : ks.Nodup :=
  hks.imp fun {a b} h (e : a = b) => go.goStringLt_irrefl a (by rw [e] at h ⊢; exact h)

/-! ## The statements of `Writer.lean` -/

theorem logOk_once_holds (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (ops : List OpM)
    (h : logOk ks ops) (n : Nat) : onceUpToAll (σOf ks ops n).notifiedLog :=
  ((runM_inv ks ops h n).2.2.2.2 (nodup_of_sorted hks)).1

theorem logOk_hist_holds (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (ops : List OpM)
    (h : logOk ks ops) (n n' : Nat) (hn : n ≤ n') (_hn' : n' ≤ ops.length) :
    histAt ks ops n <+: histAt ks ops n' ∧ histOkM ks (σOf ks ops n) (histAt ks ops n') ∧
      MvccReachable (σOf ks ops n) := by
  have hI := runM_inv ks ops h n
  have hpre := runM_hs_prefix ks ops n n' hn
  refine ⟨hpre, ⟨?_, fun r hr => ?_⟩, (hI.2.2.2.2 (nodup_of_sorted hks)).2.2⟩
  · rw [σOf_notified]
    simp only [σOf, logOfHist_length]
    exact hpre.length_le
  · rw [σOf_notified] at hr ⊢
    simp only [σOf, logOfHist_length] at hr ⊢
    obtain ⟨t, ht⟩ := hpre
    have hget : ∀ i, i < (histAt ks ops n).length →
        (histAt ks ops n')[i]? = (histAt ks ops n)[i]? := by
      intro i hi; rw [← ht, List.getElem?_append_left hi]
    obtain ⟨e, he⟩ : ∃ e, (histAt ks ops n)[r]? = some e := ⟨_, List.getElem?_eq_getElem hr⟩
    refine ⟨e, by rw [hget r hr]; exact he, hI.2.2.1 r e he, fun h1 => ?_⟩
    obtain ⟨e', he', hee⟩ := hI.2.1 r e h1 he
    refine ⟨e', by rw [hget (r - 1) (by omega)]; exact he', ?_⟩
    have hgd : (logOfHist (histAt ks ops n)).getD r [] = e.2.map toChange := by
      rw [List.getD_eq_getElem?_getD, logOfHist_getElem?, he]; rfl
    rw [hgd]; exact hee

theorem runM_mono_holds (ks : List GoString) (ops : List OpM) (n n' : Nat) (hn : n ≤ n') :
    revAfter ks ops n ≤ revAfter ks ops n' ∧ cmpAfter ks ops n ≤ cmpAfter ks ops n' ∧
      (σOf ks ops n).log <+: (σOf ks ops n').log :=
  ⟨revAfter_mono ks ops n n' hn, cmpAfter_mono ks ops n n' hn,
    (runM_hs_prefix ks ops n n' hn).map _⟩

theorem logOk_leases_holds (ks : List GoString) (hks : ∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1)
    (ops : List OpM) (h : logOk ks ops) (n : Nat) :
    (leasesAfter ks ops n).Pairwise (fun a b => sint.Z a < sint.Z b) ∧
    (∀ id ∈ leasesAfter ks ops n, 0 < sint.Z id ∧ id ∈ grantedAfter ks ops n) ∧
    ∀ it lid, (pendItems (σOf ks ops n).log []).lookup it = some lid →
      lid ∈ leasesAfter ks ops n ∧ (it.Key'.length : Int) < 2 ^ 63 - 1 := by
  obtain ⟨hpre, -, hmatch, ⟨h1, h2, h3, h4⟩, -⟩ := runM_inv ks ops h n
  refine ⟨h2.sublist h1, fun id hid => ⟨h3 id (h1.subset hid), h1.subset hid⟩, ?_⟩
  intro it lid hit
  have hlen : 2 ≤ (runM ks ops n).hs.length := by
    have := hpre.length_le; simp [hist0] at this; omega
  obtain ⟨eL, heL⟩ : ∃ e, (runM ks ops n).hs[(runM ks ops n).hs.length - 1]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hM := hmatch _ _ heL
  rw [← lastSt_of heL, ← logOfHist_length (runM ks ops n).hs, stateAt_last _ (by rw [logOfHist_length]; omega)]
    at hM
  have hit' : (leaseItemsOf (stateAfter (logOfHist (runM ks ops n).hs))).lookup it = some lid := hit
  rw [leaseItemsOf_lookup] at hit'
  cases hf : findKey it.Key' (stateAfter (logOfHist (runM ks ops n).hs)) with
  | none => rw [hf] at hit'; cases hit'
  | some kv =>
    rw [hf] at hit'
    simp only [Option.bind_some, kvLease] at hit'
    have hkv := hM.1 it.Key'
    rw [hf] at hkv
    cases hl : lastSt (runM ks ops n).hs !! it.Key' with
    | none => rw [hl] at hkv; cases hkv
    | some e =>
      rw [hl] at hkv
      simp only [Option.map_some, Option.some.injEq] at hkv
      subst hkv
      have hm := List.mem_of_find?_eq_some hf
      refine ⟨?_, hks _ (hM.2 _ hm)⟩
      simp only [kvOfRec] at hit'
      by_cases hz : e.lease' = W64 0
      · simp only [hz, ↓reduceIte] at hit'; cases hit'
      · simp only [hz, ↓reduceIte, Option.some.injEq] at hit'
        subst hit'
        rcases h4 it.Key' e hl with h | h
        · exact absurd h hz
        · exact h

theorem logOk_recover_holds (ks : List GoString) (ops : List OpM) (h : logOk ks ops) (n n' : Nat)
    (hn : n ≤ n') :
    ∀ id ∈ leasesAfter ks ops n', id ∈ grantedAfter ks ops n → id ∈ leasesAfter ks ops n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => intro id hid _; exact hid
  | succ k ih =>
    have hnm : n ≤ n + k := Nat.le_add_right n k
    have ih := ih hnm
    intro id hid hg
    have hk : n + (k + 1) = n + k + 1 := by omega
    rw [hk] at hid
    cases hm : ops[n + k]? with
    | none =>
      have : runM ks ops (n + k + 1) = runM ks ops (n + k) := by
        unfold runM; rw [List.take_add_one, hm]; simp
      unfold leasesAfter at hid; rw [this] at hid
      exact ih id hid hg
    | some o =>
      unfold leasesAfter at hid
      rw [runM_succ ks ops (n + k) o hm, opStep_leases] at hid
      by_cases hgk : o.kind = kGrant
      · simp only [hgk, ↓reduceIte] at hid
        rcases List.mem_append.1 hid with hid | hid
        · exact ih id hid hg
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hid
          subst hid
          have hlt := ((h (n + k) o hm).2.2.2.2.1 hgk).2 o.id
            (grantedAfter_mono ks ops n (n + k) hnm o.id hg)
          omega
      · simp only [hgk, ↓reduceIte] at hid
        split at hid
        · exact ih id (List.mem_filter.1 hid).1 hg
        · exact ih id hid hg

end model

end mvccfull
end EtcdGrove
end Perennial
