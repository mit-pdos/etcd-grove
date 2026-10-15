/-
**What `checkIntervals` is for**, proved (unit 1 of the request path): a branch `ops` of a
transaction that passes the gRPC layer's checks — `checkRequestOp` (`opsCheck n ops = none`: every
put and delete has a non-empty key, at any depth) and `checkIntervals` (`intervalsOk`) — with no
from-key delete (`ReqOp.noFromKeyDelL`) and no nested put that a later sibling nested
transaction deletes (`ReqOp.siblingSafeL`), run by the server at any state (`txn.srvOps`, whatever
its comparisons choose), puts distinct keys none of which it deletes: the condition of the txn
package's `keys_nodup_iff_check`, hence `NoDupKeysPerRev` of the transaction's revision
(`check_gives_nodup`). Lean-first (no Rocq counterpart).

**The two exclusions are findings of the code**, not of the proof; without either the statement
is false: `checkIntervals` reads a from-key delete's range `[k, "\x00")` as the empty interval,
so a later put of a key it deletes passes (`issues/etcd-txn-delete-then-ignore-put.md`); and it
checks a nested transaction's puts against the deletes of its level and of the siblings *before*
it, not after (`issues/etcd-txn-check-intervals-sibling.md`).

**The keys' check is needed too**: unit 0's statement without it (`intervalsOkNoKeysStmt`) is
false (`intervalsOkNoKeysStmt_false`): `checkIntervals`' affine order reads the
empty key as +∞, so a put of `""` and a delete of `""` pass it. `kvServer.Txn` runs
`checkTxnRequest` (hence `checkRequestOp` of every operation) first, so the premise is the
handler's.

The proof: a run of the operations (`RunL`: one branch per nested transaction) is what the
server's run puts and deletes (`runL_of`: its put keys, and every deleted key in the range of one
of its deletes); a passing check makes every run `Good` (`goodAll`, by the nesting size, over one
level at a time, `level`: the nested transactions' loop `nestStep`, then the level's puts
`putStep`); a key in a delete's range is one the delete's interval hits (`hits_of_inRange`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

/-! ## Strings and intervals -/

theorem goEmpty : (go!"" : GoString) = [] := rfl

theorem strLt_append_zero (k : GoString) (hk : k ≠ []) : go.GoStringLt k (k ++ [W8 0]) := by
  induction k with
  | nil => exact absurd rfl hk
  | cons x xs ih =>
    show List.Lex _ (x :: xs) (x :: (xs ++ [W8 0]))
    cases xs with
    | nil => exact List.Lex.cons List.Lex.nil
    | cons y ys => exact List.Lex.cons (ih (by simp))

theorem zero_lt_of (e : GoString) (h1 : e ≠ []) (h2 : e ≠ [W8 0]) : go.GoStringLt [W8 0] e := by
  match e, h1, h2 with
  | c :: t, _, h2 =>
    by_cases hc : c = W8 0
    · subst hc
      cases t with
      | nil => exact absurd rfl h2
      | cons _ _ => exact List.Lex.cons List.Lex.nil
    · apply List.Lex.rel
      have h0 : c.toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
      show uint.Z (W8 0) < uint.Z c
      simp only [uint.Z]; simp; omega

theorem affCmp_lt (a b : GoString) (ha : a ≠ []) (hb : b ≠ []) (h : go.GoStringLt a b) :
    adt.affCmp a b = -1 := by
  unfold adt.affCmp; simp [ha, hb, h]

theorem affCmp_nonempty_left (a : GoString) (ha : a ≠ []) : adt.affCmp [] a = 1 := by
  unfold adt.affCmp; simp [ha]

/-- A delete the check sees as the code does: a non-empty key, not a from-key range end. -/
def goodDel (o : OpFull) : Prop := o.key ≠ [] ∧ o.base.rangeEnd ≠ [W8 0]

theorem hits_sub {a b : List adt.IvlS} {k : GoString} (hab : ∀ x ∈ a, x ∈ b)
    (h : hits b k = false) : hits a k = false := by
  unfold hits at *
  rw [List.any_eq_false] at *
  exact fun x hx => h x (hab x hx)

theorem hits_single {d : adt.IvlS} {ds : List adt.IvlS} {k : GoString} (hd : d ∈ ds)
    (h : hits ds k = false) : hits [d] k = false :=
  hits_sub (fun x hx => by simp at hx; exact hx ▸ hd) h

/-- A deleted key (in the delete's range) is one `checkIntervals` sees the delete hit. -/
theorem hits_of_inRange (o : OpFull) (k : GoString) (hk : k ≠ []) (ho : goodDel o)
    (h : inRange o.key o.base.rangeEnd k = true) : hits [delIvl o] k = true := by
  obtain ⟨hkey, hfk⟩ := ho
  unfold inRange at h
  unfold hits delIvl pointIvl
  simp only [List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq]
  by_cases he : o.base.rangeEnd = []
  · simp only [he, ↓reduceIte, decide_eq_true_eq] at h ⊢
    subst h
    unfold adt.ivlCmp
    have hne : o.key ++ [W8 0] ≠ [] := by simp
    rw [affCmp_lt _ _ hkey hne (strLt_append_zero _ hkey)]
    simp
  · simp only [he, hfk, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at h ⊢
    obtain ⟨h1, h2⟩ := h
    unfold adt.ivlCmp
    rw [affCmp_lt _ _ hk he h2]
    have : ¬ adt.affCmp k o.key < 0 := by
      rw [adt.affCmp_neg_iff]; rintro ⟨-, h | h⟩
      · exact hkey h
      · exact h1 h
    simp [this]

/-- `Union`'s filter keeps a good delete's interval. -/
theorem unionSel_mem (o : OpFull) (ds : List adt.IvlS) (ho : goodDel o) (h : delIvl o ∈ ds) :
    delIvl o ∈ unionSel ds := by
  obtain ⟨hkey, hfk⟩ := ho
  unfold unionSel
  rw [List.mem_filter]
  refine ⟨h, ?_⟩
  have hb : (delIvl o).1 ≠ [] := by unfold delIvl; split <;> simpa
  have he1 : (delIvl o).2 ≠ [] := by unfold delIvl pointIvl; split <;> simp_all
  have he2 : (delIvl o).2 ≠ [W8 0] := by
    unfold delIvl pointIvl; split
    · intro h; have := congrArg List.length h; simp at this; exact hkey this
    · assumption
  simp only [decide_eq_true_eq]
  unfold adt.ivlCmp unionIvl
  have : ¬ adt.affCmp [W8 0] (delIvl o).1 < 0 ∨ ¬ adt.affCmp [] (delIvl o).1 ≤ 0 := by
    right; rw [affCmp_nonempty_left _ hb]; omega
  rw [affCmp_lt _ _ (by simp) he1 (zero_lt_of _ he1 he2)]
  simp only [show ¬ ((-1 : Int) ≥ 0) by omega, ↓reduceIte, ite_eq_right_iff]
  intro h'; rcases this with h1 | h1
  · exact absurd h'.1 h1
  · exact absurd h'.2 h1

/-! ## The runs: which puts and deletes a run of the operations does -/

mutual
/-- A run of the operation `u` (one branch of each nested transaction) puts the keys `P` and
runs the deletes `D`, in order. -/
def RunOp : ReqOp → List GoString → List OpFull → Prop
  | .range _, P, D => P = [] ∧ D = []
  | .put o, P, D => P = [o.key] ∧ D = []
  | .delete o, P, D => P = [] ∧ D = [o]
  | .txn _ ts es, P, D => RunL ts P D ∨ RunL es P D
  | .empty, _, _ => False

/-- A run of the operations `us`, in order. -/
def RunL : List ReqOp → List GoString → List OpFull → Prop
  | [], P, D => P = [] ∧ D = []
  | u :: us, P, D => ∃ P1 D1 P2 D2, P = P1 ++ P2 ∧ D = D1 ++ D2 ∧ RunOp u P1 D1 ∧ RunL us P2 D2
end

mutual
/-- Every put and delete has a non-empty key, at any depth (what `checkRequestOp` checks). -/
def ReqOp.keysNE : ReqOp → Prop
  | .put o => o.key ≠ []
  | .delete o => o.key ≠ []
  | .txn _ ts es => ReqOp.keysNEL ts ∧ ReqOp.keysNEL es
  | _ => True

def ReqOp.keysNEL : List ReqOp → Prop
  | [] => True
  | u :: us => ReqOp.keysNE u ∧ ReqOp.keysNEL us
end

mutual
theorem keysNE_of_check : ∀ (u : ReqOp) (n : Int), opCheck n u = none → u.keysNE
  | .range _, _, _ => by simp [ReqOp.keysNE]
  | .put o, n, h => by
    simp only [ReqOp.keysNE]; intro hk; simp [opCheck, putCheck, hk] at h
  | .delete o, n, h => by
    simp only [ReqOp.keysNE]; intro hk; simp [opCheck, deleteCheck, hk] at h
  | .txn cs ts es, n, h => by
    simp only [ReqOp.keysNE]
    simp only [opCheck] at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    · rename_i h1
      exact ⟨keysNEL_of_check ts _ h1, keysNEL_of_check es _ h⟩
  | .empty, _, h => by simp [opCheck] at h

theorem keysNEL_of_check : ∀ (us : List ReqOp) (n : Int), opsCheck n us = none → ReqOp.keysNEL us
  | [], _, _ => by simp [ReqOp.keysNEL]
  | u :: us, n, h => by
    simp only [ReqOp.keysNEL]
    simp only [opsCheck] at h
    split at h
    · cases h
    · rename_i h1
      exact ⟨keysNE_of_check u n h1, keysNEL_of_check us n h⟩
end

mutual
theorem RunOp.sub : ∀ (u : ReqOp) (P : List GoString) (D : List OpFull), RunOp u P D →
    (∀ k ∈ P, k ∈ u.allPuts) ∧ ∀ o ∈ D, delIvl o ∈ u.allDels
  | .range _, P, D, h => by
    simp only [RunOp] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | .put o, P, D, h => by
    simp only [RunOp] at h; obtain ⟨rfl, rfl⟩ := h; simp [ReqOp.allPuts]
  | .delete o, P, D, h => by
    simp only [RunOp] at h; obtain ⟨rfl, rfl⟩ := h; simp [ReqOp.allDels]
  | .txn cs ts es, P, D, h => by
    simp only [RunOp] at h
    simp only [ReqOp.allPuts, ReqOp.allDels, List.mem_append]
    rcases h with h | h
    · have := RunL.sub ts P D h
      exact ⟨fun k hk => Or.inl (this.1 k hk), fun o ho => Or.inl (this.2 o ho)⟩
    · have := RunL.sub es P D h
      exact ⟨fun k hk => Or.inr (this.1 k hk), fun o ho => Or.inr (this.2 o ho)⟩
  | .empty, _, _, h => by simp [RunOp] at h

theorem RunL.sub : ∀ (us : List ReqOp) (P : List GoString) (D : List OpFull), RunL us P D →
    (∀ k ∈ P, k ∈ ReqOp.allPutsL us) ∧ ∀ o ∈ D, delIvl o ∈ ReqOp.allDelsL us
  | [], P, D, h => by
    simp only [RunL] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | u :: us, P, D, h => by
    simp only [RunL] at h
    obtain ⟨P1, D1, P2, D2, rfl, rfl, h1, h2⟩ := h
    have a := RunOp.sub u P1 D1 h1
    have b := RunL.sub us P2 D2 h2
    simp only [ReqOp.allPutsL, ReqOp.allDelsL, List.mem_append]
    refine ⟨fun k hk => ?_, fun o ho => ?_⟩
    · rcases hk with hk | hk
      · exact Or.inl (a.1 k hk)
      · exact Or.inr (b.1 k hk)
    · rcases ho with ho | ho
      · exact Or.inl (a.2 o ho)
      · exact Or.inr (b.2 o ho)
end

theorem mem_allDelsL {x : adt.IvlS} : ∀ {us : List ReqOp}, x ∈ ReqOp.allDelsL us →
    ∃ v ∈ us, x ∈ v.allDels
  | [], h => by simp [ReqOp.allDelsL] at h
  | u :: us, h => by
    simp only [ReqOp.allDelsL, List.mem_append] at h
    rcases h with h | h
    · exact ⟨u, by simp, h⟩
    · obtain ⟨v, hv, hx⟩ := mem_allDelsL h
      exact ⟨v, by simp [hv], hx⟩

/-! ## A server run is a run -/

theorem putKeysOf_append (a b : List mvcc.Change) :
    txn.putKeysOf (a ++ b) = txn.putKeysOf a ++ txn.putKeysOf b := by
  simp [txn.putKeysOf, List.filterMap_append]

theorem delKeysOf_append (a b : List mvcc.Change) :
    txn.delKeysOf (a ++ b) = txn.delKeysOf a ++ txn.delKeysOf b := by
  simp [txn.delKeysOf, List.filterMap_append]

mutual
theorem runOp_of (s0 : List EtcdKv) (r : w64) : ∀ (u : ReqOp) (t : TxnOp) (s : List EtcdKv),
    ReqOp.toTxnOp u = some t →
    ∃ P D, RunOp u P D ∧ txn.putKeysOf (txn.srvOp s0 r s t).1 = P ∧
      ∀ k ∈ txn.delKeysOf (txn.srvOp s0 r s t).1, ∃ o ∈ D, inRange o.key o.base.rangeEnd k = true
  | .range o, t, s, h => by
    simp only [ReqOp.toTxnOp, Option.some.injEq] at h; subst h
    exact ⟨[], [], by simp [RunOp], by simp [txn.srvOp, txn.putKeysOf],
      by simp [txn.srvOp, txn.delKeysOf]⟩
  | .put o, t, s, h => by
    simp only [ReqOp.toTxnOp, Option.some.injEq] at h; subst h
    refine ⟨[o.key], [], by simp [RunOp], ?_, ?_⟩ <;>
      (unfold txn.putTxnOp; split <;> (try split) <;> simp [txn.srvOp, txn.putKeysOf, txn.delKeysOf])
  | .delete o, t, s, h => by
    simp only [ReqOp.toTxnOp, Option.some.injEq] at h; subst h
    refine ⟨[], [o], by simp [RunOp], ?_, ?_⟩
    · simp [txn.srvOp, txn.putKeysOf]
    · intro k hk
      simp only [txn.srvOp, txn.delKeysOf, List.mem_filterMap, List.mem_map] at hk
      obtain ⟨c, ⟨v, hv, rfl⟩, hc⟩ := hk
      simp only [Option.some.injEq] at hc; subst hc
      refine ⟨o, by simp, ?_⟩
      unfold rangeIn at hv
      exact (List.mem_filter.1 hv).2
  | .txn cs ts es, t, s, h => by
    simp only [ReqOp.toTxnOp] at h
    split at h
    · rename_i ts' es' hts hes
      simp only [Option.some.injEq] at h; subst h
      rw [txn.srvOp_txn]
      split
      · obtain ⟨P, D, hr, hp, hd⟩ := runL_of s0 r ts ts' s hts
        exact ⟨P, D, by simp only [RunOp]; exact Or.inl hr, hp, hd⟩
      · obtain ⟨P, D, hr, hp, hd⟩ := runL_of s0 r es es' s hes
        exact ⟨P, D, by simp only [RunOp]; exact Or.inr hr, hp, hd⟩
    · cases h
  | .empty, t, s, h => by simp [ReqOp.toTxnOp] at h

theorem runL_of (s0 : List EtcdKv) (r : w64) : ∀ (us : List ReqOp) (ts : List TxnOp) (s : List EtcdKv),
    ReqOp.toTxnOps us = some ts →
    ∃ P D, RunL us P D ∧ txn.putKeysOf (txn.srvOps s0 r s ts).1 = P ∧
      ∀ k ∈ txn.delKeysOf (txn.srvOps s0 r s ts).1, ∃ o ∈ D, inRange o.key o.base.rangeEnd k = true
  | [], ts, s, h => by
    simp only [ReqOp.toTxnOps, Option.some.injEq] at h; subst h
    exact ⟨[], [], by simp [RunL], by simp [txn.srvOps_nil, txn.putKeysOf],
      by simp [txn.srvOps_nil, txn.delKeysOf]⟩
  | u :: us, ts, s, h => by
    simp only [ReqOp.toTxnOps] at h
    split at h
    · rename_i t ts' ht hts
      simp only [Option.some.injEq] at h; subst h
      rw [txn.srvOps_cons]
      obtain ⟨P1, D1, h1, hp1, hd1⟩ := runOp_of s0 r u t s ht
      obtain ⟨P2, D2, h2, hp2, hd2⟩ := runL_of s0 r us ts' _ hts
      refine ⟨P1 ++ P2, D1 ++ D2, ?_, ?_, ?_⟩
      · simp only [RunL]; exact ⟨P1, D1, P2, D2, rfl, rfl, h1, h2⟩
      · rw [putKeysOf_append, hp1, hp2]
      · intro k hk
        rw [delKeysOf_append, List.mem_append] at hk
        rcases hk with hk | hk
        · obtain ⟨o, ho, hin⟩ := hd1 k hk; exact ⟨o, List.mem_append_left _ ho, hin⟩
        · obtain ⟨o, ho, hin⟩ := hd2 k hk; exact ⟨o, List.mem_append_right _ ho, hin⟩
    · cases h
end

/-! ## `checkIntervals`' loops -/

theorem nestFold_none : ∀ (nest : List NestRes), nest.foldl nestStep none = none
  | [] => rfl
  | _ :: nest => by simp only [List.foldl_cons, nestStep]; exact nestFold_none nest

theorem putFold_none : ∀ (L : List GoString), L.foldl putStep none = none
  | [] => rfl
  | _ :: L => by simp only [List.foldl_cons, putStep]; exact putFold_none L

/-- One nested transaction's step, when it passes. -/
theorem nestStep_spec {p p' : List GoString} {d d' : List adt.IvlS} {r : NestRes}
    (h : nestStep (some (p, d)) r = some (p', d')) :
    (∀ k ∈ p, k ∈ p') ∧ (∀ x ∈ d, x ∈ d') ∧
    (∀ k ∈ r.putsThen, k ∈ p') ∧ (∀ k ∈ r.putsElse, k ∈ p') ∧
    (∀ x ∈ unionSel r.delsThen, x ∈ d') ∧ (∀ x ∈ unionSel r.delsElse, x ∈ d') ∧
    (∀ k ∈ r.putsThen, k ∉ p ∧ hits d k = false) ∧
    (∀ k ∈ r.putsElse, (k ∈ p → k ∈ r.putsThen) ∧ hits d k = false) := by
  simp only [nestStep] at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.any_eq_true, not_exists, not_and, Bool.or_eq_true, decide_eq_true_eq, not_or,
    List.mem_append, Bool.not_eq_true] at h1 h2
  refine ⟨fun k hk => by simp [hk], fun x hx => by simp [hx], fun k hk => by simp [hk], ?_,
    fun x hx => by simp [hx], fun x hx => by simp [hx], fun k hk => ⟨(h1 k hk).1, (h1 k hk).2⟩,
    fun k hk => ⟨fun hp => Classical.not_not.1 ((h2 k hk).1 (Or.inl hp)), (h2 k hk).2⟩⟩
  intro k hk
  by_cases hin : k ∈ p ∨ k ∈ r.putsThen
  · rcases hin with hin | hin <;> simp [hin]
  · simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
    right; exact ⟨hk, by simpa using hin⟩

theorem nestFold_mono : ∀ (nest : List NestRes) (p0 pend : List GoString) (d0 dend : List adt.IvlS),
    nest.foldl nestStep (some (p0, d0)) = some (pend, dend) →
    (∀ k ∈ p0, k ∈ pend) ∧ (∀ x ∈ d0, x ∈ dend)
  | [], p0, pend, d0, dend, h => by
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨fun _ h => h, fun _ h => h⟩
  | r :: nest, p0, pend, d0, dend, h => by
    simp only [List.foldl_cons] at h
    cases hs : nestStep (some (p0, d0)) r with
    | none => rw [hs, nestFold_none] at h; cases h
    | some pd =>
      obtain ⟨p1, d1⟩ := pd
      rw [hs] at h
      have a := nestStep_spec hs
      have b := nestFold_mono nest p1 pend d1 dend h
      exact ⟨fun k hk => b.1 k (a.1 k hk), fun x hx => b.2 x (a.2.1 x hx)⟩

/-- The level's puts' loop, when it passes. -/
theorem putFold_spec : ∀ (L : List GoString) (p puts : List GoString) (d ds : List adt.IvlS),
    L.foldl putStep (some (p, d)) = some (puts, ds) →
    ds = d ∧ (∀ k, k ∈ puts ↔ k ∈ p ∨ k ∈ L) ∧ L.Nodup ∧ ∀ k ∈ L, k ∉ p ∧ hits d k = false
  | [], p, puts, d, ds, h => by
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  | k :: L, p, puts, d, ds, h => by
    simp only [List.foldl_cons, putStep] at h
    split at h
    · rw [putFold_none] at h; cases h
    rename_i hk
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hk
    obtain ⟨rfl, hmem, hnd, hall⟩ := putFold_spec L (p ++ [k]) puts d ds h
    refine ⟨rfl, fun k' => ?_, ?_, ?_⟩
    · rw [hmem]; simp [or_assoc]
    · refine List.nodup_cons.2 ⟨fun hkL => (hall k hkL).1 (by simp), hnd⟩
    · intro k' hk'
      rcases List.mem_cons.1 hk' with rfl | hk'
      · exact ⟨hk.1, hk.2⟩
      · exact ⟨fun hp => (hall k' hk').1 (by simp [hp]), (hall k' hk').2⟩

/-! ## What a passing check says of every run -/

/-- What a passing `checkIntervals` (`some (puts, ds)`) says of a run putting `P` and deleting
`D`: the puts are distinct, among `puts`, none in a delete's interval, every delete's interval
in `ds`, the keys non-empty and the deletes good. -/
def Good (P : List GoString) (D : List OpFull) (puts : List GoString) (ds : List adt.IvlS) :
    Prop :=
  P.Nodup ∧ (∀ k ∈ P, k ∈ puts) ∧ (∀ o ∈ D, delIvl o ∈ ds) ∧
    (∀ k ∈ P, ∀ o ∈ D, hits [delIvl o] k = false) ∧ (∀ k ∈ P, k ≠ []) ∧ (∀ o ∈ D, goodDel o)

/-- Every run of the operations `ops` passing the check is `Good`. -/
def GoodAll (ops : List ReqOp) : Prop :=
  ∀ puts ds, ivCheck ops = some (puts, ds) → ReqOp.noFromKeyDelL ops →
    ReqOp.siblingSafeL ops → ReqOp.keysNEL ops → ∀ P D, RunL ops P D → Good P D puts ds

set_option linter.unusedVariables false in
/-- **One level** of `checkIntervals`, from the operation `ops` on (a suffix of the level): the
nested transactions' loop from `(p0, d0)` to `(pend, dend)`, the level's puts checked against
the latter, the level's deletes in `d0`; the nested transactions' branches `GoodAll`. -/
theorem level : ∀ (ops : List ReqOp)
    (hnest : ∀ u ∈ ops, ∀ cs ts es, u = .txn cs ts es → GoodAll ts ∧ GoodAll es)
    (hfk : ReqOp.noFromKeyDelL ops) (hsib : ReqOp.siblingSafeL ops) (hkn : ReqOp.keysNEL ops)
    (p0 pend : List GoString) (d0 dend : List adt.IvlS) (nest : List NestRes)
    (hn : ivNest ops = some nest) (hfold : nest.foldl nestStep (some (p0, d0)) = some (pend, dend))
    (hLP : ∀ k ∈ levelPuts ops, k ∉ pend ∧ hits dend k = false) (hLPnd : (levelPuts ops).Nodup)
    (hLD : ∀ x ∈ levelDels ops, x ∈ d0) (P : List GoString) (D : List OpFull),
    RunL ops P D →
    P.Nodup ∧ (∀ k ∈ P, k ∈ pend ∨ k ∈ levelPuts ops) ∧ (∀ k ∈ P, k ∉ p0) ∧
      (∀ k ∈ P, hits d0 k = false) ∧ (∀ o ∈ D, delIvl o ∈ dend) ∧
      (∀ k ∈ P, ∀ o ∈ D, hits [delIvl o] k = false) ∧ (∀ k ∈ P, k ≠ []) ∧ (∀ o ∈ D, goodDel o)
  | [], _, _, _, _, p0, pend, d0, dend, nest, hn, hfold, _, _, _, P, D, hrun => by
    simp only [ivNest, Option.some.injEq] at hn; subst hn
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at hfold
    obtain ⟨rfl, rfl⟩ := hfold
    simp only [RunL] at hrun; obtain ⟨rfl, rfl⟩ := hrun
    simp
  | u :: rest, hnest, hfk, hsib, hkn, p0, pend, d0, dend, nest, hn, hfold, hLP, hLPnd, hLD,
      P, D, hrun => by
    simp only [RunL] at hrun
    obtain ⟨P1, D1, P2, D2, rfl, rfl, h1, h2⟩ := hrun
    simp only [ReqOp.noFromKeyDelL] at hfk
    simp only [ReqOp.siblingSafeL] at hsib
    simp only [ReqOp.keysNEL] at hkn
    have hnest' : ∀ v ∈ rest, ∀ cs ts es, v = .txn cs ts es → GoodAll ts ∧ GoodAll es :=
      fun v hv => hnest v (by simp [hv])
    have hmono := nestFold_mono nest p0 pend d0 dend hfold
    cases u with
    | range o =>
      simp only [RunOp] at h1; obtain ⟨rfl, rfl⟩ := h1
      simp only [ivNest] at hn
      have ih := level rest hnest' hfk.2 hsib.2.2 hkn.2 p0 pend d0 dend nest hn hfold
        (by simpa [levelPuts] using hLP) (by simpa [levelPuts] using hLPnd)
        (by simpa [levelDels] using hLD) P2 D2 h2
      simpa [levelPuts] using ih
    | empty => simp [RunOp] at h1
    | put o =>
      simp only [RunOp] at h1; obtain ⟨rfl, rfl⟩ := h1
      simp only [ivNest] at hn
      simp only [levelPuts, List.mem_cons, List.nodup_cons, forall_eq_or_imp] at hLP hLPnd
      have ih := level rest hnest' hfk.2 hsib.2.2 hkn.2 p0 pend d0 dend nest hn hfold
        hLP.2 hLPnd.2 (by simpa [levelDels] using hLD) P2 D2 h2
      obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ih
      have hko : o.key ∉ P2 := fun hk => by
        rcases i2 _ hk with h | h
        · exact hLP.1.1 h
        · exact hLPnd.1 h
      simp only [List.singleton_append, List.nil_append, List.nodup_cons, List.mem_cons,
        forall_eq_or_imp, levelPuts]
      refine ⟨⟨hko, i1⟩, ⟨by simp, fun k hk => ?_⟩,
        ⟨fun h => hLP.1.1 (hmono.1 _ h), i3⟩, ⟨hits_sub hmono.2 hLP.1.2, i4⟩, i5,
        ⟨fun o' ho' => hits_single (i5 o' ho') hLP.1.2, i6⟩, ⟨hkn.1, i7⟩, i8⟩
      rcases i2 k hk with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    | delete o =>
      simp only [RunOp] at h1; obtain ⟨rfl, rfl⟩ := h1
      simp only [ivNest] at hn
      simp only [levelDels, List.mem_cons, forall_eq_or_imp] at hLD
      have ih := level rest hnest' hfk.2 hsib.2.2 hkn.2 p0 pend d0 dend nest hn hfold
        (by simpa [levelPuts] using hLP) (by simpa [levelPuts] using hLPnd) hLD.2 P2 D2 h2
      obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ih
      simp only [List.nil_append, List.singleton_append, List.mem_cons, forall_eq_or_imp,
        levelPuts]
      refine ⟨i1, i2, i3, i4, ⟨hmono.2 _ hLD.1, i5⟩,
        fun k hk => ⟨hits_single hLD.1 (i4 k hk), i6 k hk⟩, i7,
        ⟨⟨hkn.1, by simpa [ReqOp.noFromKeyDel] using hfk.1⟩, i8⟩⟩
    | txn cs ts es =>
      simp only [ivNest] at hn
      split at hn
      · rename_i pT dT pE dE nr hT hE hr
        simp only [Option.some.injEq] at hn; subst hn
        simp only [List.foldl_cons] at hfold
        cases hs : nestStep (some (p0, d0)) ⟨pT, dT, pE, dE⟩ with
        | none => rw [hs, nestFold_none] at hfold; cases hfold
        | some pd =>
        obtain ⟨p1, d1⟩ := pd
        rw [hs] at hfold
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := nestStep_spec hs
        have hmono' := nestFold_mono nr p1 pend d1 dend hfold
        have ih := level rest hnest' hfk.2 hsib.2.2 hkn.2 p1 pend d1 dend nr hr hfold
          (by simpa [levelPuts] using hLP) (by simpa [levelPuts] using hLPnd)
          (fun x hx => a2 x (hLD x (by simpa [levelDels] using hx))) P2 D2 h2
        obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ih
        obtain ⟨gT, gE⟩ := hnest _ (by simp) cs ts es rfl
        simp only [ReqOp.noFromKeyDel] at hfk
        simp only [ReqOp.siblingSafe] at hsib
        simp only [ReqOp.keysNE] at hkn
        -- the branch run: `Good` against its own check, and its puts/deletes in the txn's
        have hsub := RunOp.sub (.txn cs ts es) P1 D1 h1
        obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ : P1.Nodup ∧ (∀ k ∈ P1, k ∈ p1) ∧
            (∀ k ∈ P1, k ∉ p0 ∧ hits d0 k = false) ∧ (∀ o ∈ D1, delIvl o ∈ d1) ∧
            (∀ k ∈ P1, ∀ o ∈ D1, hits [delIvl o] k = false) ∧ (∀ k ∈ P1, k ≠ []) ∧
            (∀ o ∈ D1, goodDel o) := by
          simp only [RunOp] at h1
          rcases h1 with h1 | h1
          · obtain ⟨g1, g2, g3, g4, g5, g6⟩ :=
              gT pT dT hT hfk.1.1 hsib.2.1.1 hkn.1.1 P1 D1 h1
            exact ⟨g1, fun k hk => a3 k (g2 k hk), fun k hk => a7 k (g2 k hk),
              fun o ho => a5 _ (unionSel_mem o _ (g6 o ho) (g3 o ho)), g4, g5, g6⟩
          · obtain ⟨g1, g2, g3, g4, g5, g6⟩ :=
              gE pE dE hE hfk.1.2 hsib.2.1.2 hkn.1.2 P1 D1 h1
            refine ⟨g1, fun k hk => a4 k (g2 k hk), fun k hk => ⟨fun hp => ?_, (a8 k (g2 k hk)).2⟩,
              fun o ho => a6 _ (unionSel_mem o _ (g6 o ho) (g3 o ho)), g4, g5, g6⟩
            exact (a7 k ((a8 k (g2 k hk)).1 hp)).1 hp
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact List.nodup_append.2 ⟨b1, i1, fun k hk k' hk' he => i3 k' hk' (he ▸ b2 k hk)⟩
        · intro k hk
          rcases List.mem_append.1 hk with hk | hk
          · exact Or.inl (hmono'.1 k (b2 k hk))
          · simpa [levelPuts] using i2 k hk
        · intro k hk
          rcases List.mem_append.1 hk with hk | hk
          · exact (b3 k hk).1
          · exact fun h => i3 k hk (a1 k h)
        · intro k hk
          rcases List.mem_append.1 hk with hk | hk
          · exact (b3 k hk).2
          · exact hits_sub a2 (i4 k hk)
        · intro o ho
          rcases List.mem_append.1 ho with ho | ho
          · exact hmono'.2 _ (b4 o ho)
          · exact i5 o ho
        · intro k hk o ho
          rcases List.mem_append.1 hk with hk | hk <;> rcases List.mem_append.1 ho with ho | ho
          · exact b5 k hk o ho
          · -- a later sibling's delete: `siblingSafe`
            obtain ⟨v, hv, hx⟩ := mem_allDelsL ((RunL.sub rest P2 D2 h2).2 o ho)
            have hs := hsib.1 v hv
            simp only [sibOk] at hs
            exact hits_single hx (hs k (hsub.1 k hk))
          · exact hits_single (b4 o ho) (i4 k hk)
          · exact i6 k hk o ho
        · intro k hk
          rcases List.mem_append.1 hk with hk | hk
          · exact b6 k hk
          · exact i7 k hk
        · intro o ho
          rcases List.mem_append.1 ho with ho | ho
          · exact b7 o ho
          · exact i8 o ho
      · cases hn

/-- A level whose nested transactions' branches are `GoodAll` is `GoodAll`. -/
theorem goodAll_of_nest (ops : List ReqOp)
    (hnest : ∀ u ∈ ops, ∀ cs ts es, u = .txn cs ts es → GoodAll ts ∧ GoodAll es) :
    GoodAll ops := by
  intro puts ds hiv hfk hsib hkn P D hrun
  unfold ivCheck at hiv
  cases hn : ivNest ops with
  | none => rw [hn] at hiv; cases hiv
  | some nest =>
  rw [hn] at hiv
  simp only [Option.bind_some, ivFinish] at hiv
  cases hf : nest.foldl nestStep (some ([], levelDels ops)) with
  | none => rw [hf, putFold_none] at hiv; cases hiv
  | some pd =>
  obtain ⟨pend, dend⟩ := pd
  rw [hf] at hiv
  obtain ⟨hds, hmem, hnd, hall⟩ := putFold_spec _ _ _ _ _ hiv
  subst hds
  obtain ⟨i1, i2, -, -, i5, i6, i7, i8⟩ :=
    level ops hnest hfk hsib hkn [] pend (levelDels ops) ds nest hn hf hall hnd
      (fun _ h => h) P D hrun
  exact ⟨i1, fun k hk => (hmem k).2 (i2 k hk), i5, i6, i7, i8⟩

mutual
/-- The nesting size of an operation. -/
def ReqOp.sz : ReqOp → Nat
  | .txn _ ts es => 1 + ReqOp.szL ts + ReqOp.szL es
  | _ => 1

def ReqOp.szL : List ReqOp → Nat
  | [] => 0
  | u :: us => ReqOp.sz u + ReqOp.szL us
end

theorem sz_le_szL : ∀ {us : List ReqOp} {u : ReqOp}, u ∈ us → u.sz ≤ ReqOp.szL us
  | [], _, h => by simp at h
  | v :: us, u, h => by
    simp only [ReqOp.szL]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := sz_le_szL h; omega

/-- **Every run of operations passing `checkIntervals` is `Good`** (by the nesting size). -/
theorem goodAll : ∀ (n : Nat) (ops : List ReqOp), ReqOp.szL ops ≤ n → GoodAll ops
  | 0, ops, h => goodAll_of_nest ops (fun u hu cs ts es he => by
      have := sz_le_szL hu; subst he; simp only [ReqOp.sz] at this; omega)
  | n + 1, ops, h => goodAll_of_nest ops (fun u hu cs ts es he => by
      have := sz_le_szL hu; subst he; simp only [ReqOp.sz] at this
      exact ⟨goodAll n ts (by omega), goodAll n es (by omega)⟩)

/-- **`check_gives_nodup`** (`intervalsOkCheckStmt`): see the file header. The two exclusions
(`noFromKeyDelL`, `siblingSafeL`) are findings of the code
(`issues/etcd-txn-delete-then-ignore-put.md`, `issues/etcd-txn-check-intervals-sibling.md`):
without either the statement is false. -/
theorem check_gives_nodup (n : Int) (ops : List ReqOp) (tops : List TxnOp) (s0 s : List EtcdKv)
    (r : w64) (htx : ReqOp.toTxnOps ops = some tops) (hck : opsCheck n ops = none)
    (hfk : ReqOp.noFromKeyDelL ops) (hsib : ReqOp.siblingSafeL ops) (hiv : intervalsOk ops) :
    (txn.putKeysOf (txn.srvOps s0 r s tops).1).Nodup ∧
      ∀ k ∈ txn.putKeysOf (txn.srvOps s0 r s tops).1, k ∉ txn.delKeysOf (txn.srvOps s0 r s tops).1 := by
  obtain ⟨P, D, hrun, hp, hd⟩ := runL_of s0 r ops tops s htx
  unfold intervalsOk at hiv
  obtain ⟨⟨puts, ds⟩, hc⟩ := Option.isSome_iff_exists.1 hiv
  obtain ⟨g1, -, -, g4, g5, g6⟩ :=
    goodAll _ ops (Nat.le_refl _) puts ds hc hfk hsib (keysNEL_of_check ops n hck) P D hrun
  rw [hp]
  refine ⟨g1, fun k hk hdel => ?_⟩
  obtain ⟨o, ho, hin⟩ := hd k hdel
  have := hits_of_inRange o k (g5 k hk) (g6 o ho) hin
  rw [g4 k hk o ho] at this
  cases this

/-- **`intervalsOkCheckStmt` holds.** -/
theorem intervalsOkCheckStmt_holds : intervalsOkCheckStmt :=
  fun n ops tops s0 s r htx hck hfk hsib hiv => check_gives_nodup n ops tops s0 s r htx hck hfk hsib hiv

/-- **Unit 0's statement, without the keys checked, is false**: without the keys checked (`checkRequestOp`,
which runs before `checkIntervals` in `kvServer.Txn`), a put of the empty key and a delete of the
empty key pass `checkIntervals` (the affine order reads `""` as +∞, so the point `["", "\x00")`
overlaps nothing) and the run puts and deletes `""` in one revision. -/
theorem intervalsOkNoKeysStmt_false : ¬ intervalsOkNoKeysStmt := by
  intro h
  have := h [.put (txn.putOpOf [] [] (W64 0) false false false),
      .delete (txn.deleteOpOf [] [] false)]
    [txn.putTxnOp (txn.putOpOf [] [] (W64 0) false false false),
      .delete (txn.deleteOpOf [] [] false)] [] [] (W64 1) rfl
    (by simp [ReqOp.noFromKeyDelL, ReqOp.noFromKeyDel, txn.deleteOpOf])
    (by simp [ReqOp.siblingSafeL, ReqOp.siblingSafe, sibOk])
    (by
      simp only [intervalsOk, ivCheck, ivNest, Option.bind_some, ivFinish, levelPuts, levelDels,
        List.foldl_nil, List.foldl_cons, putStep, txn.putOpOf, txn.deleteOpOf, delIvl, pointIvl,
        hits, List.any_cons, List.any_nil, adt.ivlCmp, adt.affCmp]
      decide)
  obtain ⟨-, h2⟩ := this
  apply h2 []
  · simp [txn.srvOps, txn.srvOp, txn.putTxnOp, txn.putOpOf, txn.putKeysOf]
  · simp [txn.srvOps, txn.srvOp, txn.putTxnOp, txn.putOpOf, txn.deleteOpOf, txn.delKeysOf,
      rangeIn, inRange, mvcc.applyChanges, mvcc.applyChange, putKv, btInsert]

end v3rpc
end EtcdGrove
end Perennial

