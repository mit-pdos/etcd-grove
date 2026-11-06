/-
U7e's (`notes/bbolt-proof-plan.md`) `Bucket.free`, its pure part: the records after the walk
freed the positions `ps` (`freedAt`: each node reached at page id `0`), and the freelist facts
(`canFreeAll` of a list split in two; an extent freed twice is not `canFreeAll`, so a node the
walk reaches twice does not happen).
-/
module

public import Proof.go_etcd_io.bbolt.Write.Walk
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Model

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- A node of `B` reached by one of the positions `ps`. -/
def reachedBy (B : BRec) (ps : List w64) (l : Loc) : Prop := ∃ pid ∈ ps, resolve B pid = some l

/-- **`Y` is `X` with the nodes of bucket `bl` the positions `ps` reach at page id `0`.** -/
def freedAt (X Y : WX) (bl : Loc) (B : BRec) (ps : List w64) : Prop :=
  ∃ ns', Y = X.setBkt bl { B with ns := ns' } ∧ ∀ l, ns' !! l = (B.ns !! l).map fun r =>
    open Classical in
    if reachedBy B ps l then { r with nv := { r.nv with pgid' := W64 0 } } else r

theorem setBkt_lookup (X : WX) (bl : Loc) (B' : BRec) : (X.setBkt bl B').t.bs !! bl = some B' := by
  unfold WX.setBkt; simp

theorem setBkt_setBkt (X : WX) (bl : Loc) (B1 B2 : BRec) :
    (X.setBkt bl B1).setBkt bl B2 = X.setBkt bl B2 := by
  unfold WX.setBkt; simp only [GMap.insert_insert]

theorem freedAt_nil (X : WX) (bl : Loc) (B : BRec) (hB : X.t.bs !! bl = some B) :
    freedAt X X bl B [] := by
  refine ⟨B.ns, ?_, fun l => ?_⟩
  · unfold WX.setBkt
    rw [show ({ B with ns := B.ns } : BRec) = B from rfl, GMap.insert_id _ _ _ hB]
  · cases h : B.ns !! l with
    | none => rfl
    | some r => simp [reachedBy]

theorem freedAt_walkSame (X Y : WX) (bl : Loc) (B : BRec) (ps : List w64)
    (hB : X.t.bs !! bl = some B) (hl : bl ∈ X.liveB) (hlive : ∀ l r, B.ns !! l = some r → l ∈ X.live)
    (h : freedAt X Y bl B ps) : walkSame X Y bl B := by
  obtain ⟨ns', rfl, hns⟩ := h
  refine ⟨rfl, rfl, hl, _, setBkt_lookup X bl _, rfl, rfl, rfl, rfl, fun l r hr => ⟨hlive l r hr, ?_⟩⟩
  rw [hns l, hr]
  simp only [Option.map_some]
  split <;> exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- A page position adds no reached node. -/
theorem freedAt_page (X Y : WX) (bl : Loc) (B : BRec) (ps : List w64) (pid : w64)
    (hr : resolve B pid = none) (h : freedAt X Y bl B ps) : freedAt X Y bl B (ps ++ [pid]) := by
  obtain ⟨ns', rfl, hns⟩ := h
  refine ⟨ns', rfl, fun l => ?_⟩
  rw [hns l]
  have : reachedBy B (ps ++ [pid]) l ↔ reachedBy B ps l := by
    unfold reachedBy
    constructor
    · rintro ⟨q, hq, hql⟩
      rcases List.mem_append.1 hq with hq | hq
      · exact ⟨q, hq, hql⟩
      · simp at hq; subst hq; rw [hr] at hql; cases hql
    · rintro ⟨q, hq, hql⟩; exact ⟨q, List.mem_append_left _ hq, hql⟩
  open Classical in
  simp only [this]

/-- A node position `pid` (its node `l`, not reached before): the node at page id `0`. -/
theorem freedAt_node (X Y : WX) (bl : Loc) (B : BRec) (ps : List w64) (pid : w64) (l : Loc)
    (rn : NRec) (hr : resolve B pid = some l) (hrn : B.ns !! l = some rn)
    (hnot : ¬ reachedBy B ps l) (h : freedAt X Y bl B ps) :
    Y.node bl l = some rn ∧
    freedAt X (Y.setNode bl l { rn with nv := { rn.nv with pgid' := W64 0 } }) bl B (ps ++ [pid]) := by
  obtain ⟨ns', rfl, hns⟩ := h
  have hl : ns' !! l = some rn := by
    rw [hns l, hrn]; simp [hnot]
  refine ⟨by simp [WX.node, setBkt_lookup, hl], ?_⟩
  refine ⟨ns'.insert l { rn with nv := { rn.nv with pgid' := W64 0 } }, ?_, fun l' => ?_⟩
  · simp only [WX.setNode, setBkt_lookup, setBkt_setBkt]
  · have hreach : ∀ l', reachedBy B (ps ++ [pid]) l' ↔ reachedBy B ps l' ∨ l' = l := by
      intro l'
      unfold reachedBy
      constructor
      · rintro ⟨q, hq, hql⟩
        rcases List.mem_append.1 hq with hq | hq
        · exact Or.inl ⟨q, hq, hql⟩
        · simp at hq; subst hq; rw [hr] at hql; cases hql; exact Or.inr rfl
      · rintro (⟨q, hq, hql⟩ | rfl)
        · exact ⟨q, List.mem_append_left _ hq, hql⟩
        · exact ⟨pid, by simp, hr⟩
    by_cases he : l' = l
    · subst he
      simp [hrn, hreach]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm he), hns l']
      have h1 : reachedBy B (ps ++ [pid]) l' ↔ reachedBy B ps l' := by rw [hreach]; simp [he]
      by_cases hr' : reachedBy B ps l'
      · have h2 := h1.2 hr'; simp [hr', h2]
      · have h2 : ¬ reachedBy B (ps ++ [pid]) l' := fun h => hr' (h1.1 h); simp [hr', h2]

/-- `freedAt`'s records are `bktFreed`'s. -/
theorem freedAt_ns (B : BRec) (ps : List w64) (ns' : GMap Loc NRec)
    (hns : ∀ l, ns' !! l = (B.ns !! l).map fun r =>
      open Classical in
      if reachedBy B ps l then { r with nv := { r.nv with pgid' := W64 0 } } else r) :
    ∀ l, ns' !! l = (B.ns !! l).map fun r =>
      if ∃ pid ∈ ps, resolve B pid = some l
      then { r with nv := { r.nv with pgid' := W64 0 } } else r := by
  intro l
  rw [hns l]
  refine congrArg (fun f => Option.map f (B.ns !! l)) (funext fun r => ?_)
  by_cases h : reachedBy B ps l
  · have h' : ∃ pid ∈ ps, resolve B pid = some l := h
    rw [if_pos h, if_pos h']
  · have h' : ¬ ∃ pid ∈ ps, resolve B pid = some l := h
    rw [if_neg h, if_neg h']

/-! ## The freelist -/

theorem freeAll_cons (fl : FLPg) (txid : w64) (e : w64 × Nat) (es : List (w64 × Nat)) :
    fl.freeAll txid (e :: es) = (fl.freePages txid e.1 e.2).freeAll txid es := rfl

theorem freeAll_append (fl : FLPg) (txid : w64) (a b : List (w64 × Nat)) :
    fl.freeAll txid (a ++ b) = (fl.freeAll txid a).freeAll txid b := by
  unfold FLPg.freeAll; rw [List.foldl_append]

theorem canFreeAll_append (txid : w64) : ∀ (a b : List (w64 × Nat)) (fl : FLPg),
    fl.canFreeAll txid (a ++ b) ↔ fl.canFreeAll txid a ∧ (fl.freeAll txid a).canFreeAll txid b
  | [], b, fl => by simp [FLPg.canFreeAll, FLPg.freeAll]
  | e :: a, b, fl => by
    simp only [List.cons_append, FLPg.canFreeAll, freeAll_cons]
    rw [canFreeAll_append txid a b]
    exact and_assoc.symm

theorem allIds_freePages (fl : FLPg) (txid id : w64) (n : Nat) (x : w64) :
    x ∈ (fl.freePages txid id n).allIds ↔ x ∈ fl.allIds ∨ x ∈ runIds id n := by
  unfold FLPg.allIds
  have hp := (pendingIds_freePages fl txid id n).mem_iff (a := x)
  have hf : (fl.freePages txid id n).free = fl.free := rfl
  rw [List.mem_append, List.mem_append, hf, hp, List.mem_append]
  exact or_assoc.symm

theorem allIds_freeAll (txid : w64) (x : w64) : ∀ (es : List (w64 × Nat)) (fl : FLPg),
    x ∈ fl.allIds → x ∈ (fl.freeAll txid es).allIds
  | [], _, h => h
  | e :: es, fl, h => by
    rw [freeAll_cons]
    exact allIds_freeAll txid x es _ ((allIds_freePages fl txid e.1 e.2 x).2 (Or.inl h))

theorem allIds_freeAll_mem (txid : w64) (e : w64 × Nat) (he : 1 ≤ e.2) :
    ∀ (es : List (w64 × Nat)) (fl : FLPg), e ∈ es → e.1 ∈ (fl.freeAll txid es).allIds
  | [], _, h => by simp at h
  | e' :: es, fl, h => by
    rw [freeAll_cons]
    rcases List.mem_cons.1 h with rfl | h
    · apply allIds_freeAll
      refine (allIds_freePages fl txid e.1 e.2 e.1).2 (Or.inr ?_)
      simp only [runIds, List.mem_map, List.mem_range]
      exact ⟨0, he, by simp⟩
    · exact allIds_freeAll_mem txid e he es _ h

/-- **An extent freed twice is not `canFree`.** -/
theorem not_canFree_again (fl : FLPg) (txid : w64) (es : List (w64 × Nat)) (e : w64 × Nat)
    (he : 1 ≤ e.2) (hm : e ∈ es) : ¬ (fl.freeAll txid es).canFree txid e.1 e.2 := by
  intro h
  have hmem := allIds_freeAll_mem txid e he es fl hm
  apply h.2.2.1 e.1 _ hmem
  simp only [runIds, List.mem_map, List.mem_range]
  exact ⟨0, he, by simp⟩

/-! ## The extents -/

theorem posExtent_node (X : WX) (bl : Loc) (B : BRec) (pid : w64) (l : Loc) (rn : NRec)
    (pg : List w8) (hB : X.t.bs !! bl = some B) (hr : resolve B pid = some l)
    (hrn : B.ns !! l = some rn) (hpid : rn.nv.pgid' = pid) (hp0 : pid ≠ W64 0)
    (hpg : X.v.pages !! pid.toNat = some pg) :
    X.posExtent bl pid = some (pid, 1 + pageOverflow pg) := by
  unfold WX.posExtent
  simp only [hB, hr, hrn, Option.map_some, Option.getD_some, hpid, if_neg hp0, hpg]

theorem posExtent_page (X : WX) (bl : Loc) (B : BRec) (pid : w64) (pg : List w8)
    (hB : X.t.bs !! bl = some B) (hr : resolve B pid = none) (hp0 : pid ≠ W64 0)
    (hpg : X.v.pages !! pid.toNat = some pg) :
    X.posExtent bl pid = some (pid, 1 + pageOverflow pg) := by
  unfold WX.posExtent
  simp only [hB, hr, if_neg hp0, hpg, Option.map_some]

theorem posExtent_same (X : WX) (bl : Loc) (B : BRec) (p1 p2 : w64) (l : Loc)
    (hB : X.t.bs !! bl = some B) (h1 : resolve B p1 = some l) (h2 : resolve B p2 = some l) :
    X.posExtent bl p1 = X.posExtent bl p2 := by
  unfold WX.posExtent
  simp only [hB, h1, h2]

/-- The extent at the walk's next position can be freed after the earlier ones. -/
theorem canFree_at (fl : FLPg) (txid : w64) (f : w64 → Option (w64 × Nat)) (P ps : List w64)
    (pid : w64) (e : w64 × Nat) (hpre : (ps ++ [pid]) <+: P) (he : f pid = some e)
    (h : fl.canFreeAll txid (P.filterMap f)) :
    (fl.freeAll txid (ps.filterMap f)).canFree txid e.1 e.2 := by
  obtain ⟨u, rfl⟩ := hpre
  simp only [List.filterMap_append, List.filterMap_cons, he,
    List.append_assoc, List.singleton_append] at h
  exact ((canFreeAll_append txid _ _ fl).1 h).2.1

/-- A node reached twice: its extent would be freed twice. -/
theorem node_once (fl : FLPg) (txid : w64) (X : WX) (bl : Loc) (B : BRec) (P ps : List w64)
    (pid : w64) (l : Loc) (e : w64 × Nat) (hB : X.t.bs !! bl = some B) (he1 : 1 ≤ e.2)
    (hpre : (ps ++ [pid]) <+: P) (hr : resolve B pid = some l)
    (he : X.posExtent bl pid = some e)
    (h : fl.canFreeAll txid (P.filterMap (X.posExtent bl))) : ¬ reachedBy B ps l := by
  rintro ⟨q, hq, hql⟩
  have hc := canFree_at fl txid _ P ps pid e hpre he h
  refine not_canFree_again fl txid _ e he1 ?_ hc
  rw [List.mem_filterMap]
  exact ⟨q, hq, by rw [posExtent_same X bl B q pid l hB hql hr]; exact he⟩

end pure

end Write

end bbolt
end EtcdGrove
end Perennial
