/-
The freelist interface (`freelist.Interface`) as its users (the `bbolt` package) see it: the
spec of each of its methods, called through the interface value of an implementation `I`, on
the whole freelist `ownFL I s σ`, and `FLImpl.IfaceContract`, the record of them that
`array` (and `hashMap`) meet.

The specs are functional on `FLState`, up to `FLState.equiv` where the Go code keeps only what
its users observe: the order of the free ids before they are sorted again, of the read-only
transactions, and of the (id, allocating transaction) pairs of a pending entry
(`ReleasePendingPages` swaps them around).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Read
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Write

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

/-- A pending entry's (id, allocating transaction) pairs. -/
def Pending.pairs (pd : Pending) : List (w64 × w64) := pd.ids.zip pd.alloctx

/-- Two pending entries agree up to the order of their pairs. -/
def Pending.equiv (p q : Pending) : Prop :=
  p.pairs.Perm q.pairs ∧ p.lastReleaseBegin = q.lastReleaseBegin

/-- Two states agree up to the order of the free ids, of the read-only transactions and of
each pending entry's pairs. -/
def FLState.equiv (σ τ : FLState) : Prop :=
  σ.free.Perm τ.free ∧ σ.readonly.Perm τ.readonly ∧ σ.allocs = τ.allocs ∧
  (∀ t, (σ.pending !! t).isSome ↔ (τ.pending !! t).isSome) ∧
  ∀ t p q, σ.pending !! t = some p → τ.pending !! t = some q → p.equiv q

/-- `Rollback(txid)` does not panic: no page `txid` freed was allocated by `txid`. -/
def FLState.canRollback (σ : FLState) (txid : w64) : Prop :=
  ∀ pd, σ.pending !! txid = some pd → ∀ t ∈ pd.alloctx, t ≠ W64 0 → t ≠ txid

/-- One pair of a rolled-back entry: its page is allocated again by its transaction, if known. -/
def rbStep (m : GMap w64 w64) (x : w64 × w64) : GMap w64 w64 :=
  if x.2 = W64 0 then m else <[x.1 := x.2]> m

/-- `σ` after `Rollback(txid)`: the pages `txid` freed are allocated again (by the transactions
that allocated them, when known), and `txid` allocated nothing. -/
def FLState.rollback (σ : FLState) (txid : w64) : FLState :=
  match σ.pending !! txid with
  | none => σ
  | some pd =>
    { σ with
      pending := GMap.delete txid σ.pending,
      allocs := GMap.filter (fun _ t => decide (t ≠ txid))
        (pd.pairs.foldl rbStep σ.allocs) }

/-- `t` is in the transaction range `[b, e]`. -/
def inTxRange (b e t : w64) : Bool := decide (uint.Z b ≤ uint.Z t ∧ uint.Z t ≤ uint.Z e)

/-- `σ` after `release(txid)`: the pages pending for transactions up to `txid` are free. -/
def FLState.release (σ : FLState) (txid : w64) : FLState :=
  { σ with
    free := σ.free ++ flatIds (σ.pending.filter (fun t _ => decide (uint.Z t ≤ uint.Z txid))),
    pending := σ.pending.filter (fun t _ => !decide (uint.Z t ≤ uint.Z txid)) }

/-- `releaseRange(b, e)` looks at the entry `pd` of `t`: `t` is in `[b, e]` and the entry was
not already looked at from `b`. -/
def rrTouched (b e t : w64) (pd : Pending) : Bool := inTxRange b e t && pd.lastReleaseBegin != b

/-- What `releaseRange(b, e)` keeps of an entry it looks at: its pairs allocated outside
`[b, e]`, looked at from `b`. -/
def rrKeep (b e : w64) (pd : Pending) : Pending :=
  ⟨(pd.pairs.filter (fun x => !inTxRange b e x.2)).map Prod.fst,
    (pd.pairs.filter (fun x => !inTxRange b e x.2)).map Prod.snd, b⟩

/-- What `releaseRange(b, e)` frees of an entry it looks at: its pages allocated in `[b, e]`. -/
def rrRel (b e : w64) (pd : Pending) : List w64 :=
  (pd.pairs.filter (fun x => inTxRange b e x.2)).map Prod.fst

/-- `σ` after `releaseRange(b, e)`: each entry of a transaction in `[b, e]` not already looked
at from `b` frees its pages allocated in `[b, e]` (and is dropped if none is left). -/
def FLState.releaseRange (σ : FLState) (b e : w64) : FLState :=
  if uint.Z e < uint.Z b then σ else
  { σ with
    free := σ.free ++ (σ.pending.filter (rrTouched b e)).toList.flatMap (fun kv => rrRel b e kv.2),
    pending := σ.pending.filter (fun t pd => !rrTouched b e t pd) ∪
      ((σ.pending.filter (rrTouched b e)).fmap (rrKeep b e)).filter (fun _ pd => !pd.ids.isEmpty) }

/-- The read-only transactions, sorted. -/
def sortedTxids (l : List w64) : List w64 := l.mergeSort (fun a b => decide (uint.Z a ≤ uint.Z b))

/-- `σ` after `ReleasePendingPages()`: the pages freed before the oldest read-only transaction
are free, and so are those both allocated and freed between two consecutive read-only
transactions (after the newest); the read-only transactions are sorted. -/
def FLState.releasePending (σ : FLState) : FLState :=
  let ro := sortedTxids σ.readonly
  let minid := ro.headD (W64 (2 ^ 64 - 1))
  let σ1 := if 0 < uint.Z minid then σ.release (minid - W64 1) else σ
  let acc := ro.foldl (fun (acc : FLState × w64) tid =>
    (acc.1.releaseRange acc.2 (tid - W64 1), tid + W64 1)) (σ1, minid)
  { acc.1.releaseRange acc.2 (W64 (2 ^ 64 - 1)) with readonly := ro }

theorem rollback_some {σ : FLState} {txid : w64} {pd : Pending} (h : σ.pending !! txid = some pd) :
    σ.rollback txid = { σ with
      pending := GMap.delete txid σ.pending,
      allocs := GMap.filter (fun _ t => decide (t ≠ txid))
        (pd.pairs.foldl rbStep σ.allocs) } := by
  unfold FLState.rollback; rw [h]

theorem rollback_none {σ : FLState} {txid : w64} (h : σ.pending !! txid = none) :
    σ.rollback txid = σ := by
  unfold FLState.rollback; rw [h]

/-- After a rollback, the cached ids are those before but the entry's; the state stays
well-formed. -/
theorem rollback_ok {σ : FLState} {txid : w64} {pd : Pending} (hwf : σ.WF)
    (h : σ.pending !! txid = some pd) :
    (∀ x, (σ.rollback txid).cached x ↔ σ.cached x ∧ x ∉ pd.ids) ∧ (σ.rollback txid).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  rw [rollback_some h]
  generalize (GMap.filter (fun _ t => decide (t ≠ txid)) _ : GMap w64 w64) = A
  have hp := flatIds_lookup h
  have hall : σ.allIds.Perm ((σ.free ++ flatIds (GMap.delete txid σ.pending)) ++ pd.ids) := by
    unfold FLState.allIds
    rw [pendingIds_eq, List.append_assoc]
    exact List.Perm.append_left _ (hp.trans List.perm_append_comm)
  have hnd := hall.nodup_iff.1 h1
  have hnd' := (List.nodup_append.1 hnd)
  have hall' : ({ σ with pending := GMap.delete txid σ.pending, allocs := A } : FLState).allIds =
      σ.free ++ flatIds (GMap.delete txid σ.pending) := rfl
  refine ⟨fun x => ?_, ?_, ?_, h3, ?_, ?_⟩
  · unfold FLState.cached
    rw [hall', hall.mem_iff]
    simp only [List.mem_append]
    constructor
    · intro hx
      exact ⟨Or.inl hx, fun hm => hnd'.2.2 x (List.mem_append.2 hx) x hm rfl⟩
    · rintro ⟨hx | hx, hn⟩
      · exact hx
      · exact absurd hx hn
  · rw [hall']; exact hnd'.1
  · intro id hid; rw [hall'] at hid
    exact h2 id (hall.mem_iff.2 (List.mem_append_left _ hid))
  · rw [hall']
    have := hall.length_eq
    simp only [List.length_append] at this ⊢
    omega
  · intro t q hq
    simp only [GMap.lookup_delete_iff] at hq
    split at hq
    · cases hq
    · exact h5 t q hq

theorem lookup_filter {V : Type} (m : GMap w64 V) (P : w64 → V → Bool) (k : w64) :
    (GMap.filter P m) !! k = (m !! k).filter (P k) := rfl

/-- The ids of the entries a filter keeps: those of the map's bindings it keeps. -/
theorem flatIds_filter_perm (m : GMap w64 Pending) (P : w64 → Pending → Bool) :
    (flatIds (GMap.filter P m)).Perm
      ((m.toList.filter (fun kv => P kv.1 kv.2)).flatMap (fun kv => kv.2.ids)) := by
  have h := (toList_perm_of (m := GMap.filter P m) (l := m.toList.filter (fun kv => P kv.1 kv.2))
    ((List.Sublist.map _ List.filter_sublist).nodup (GMap.toList_keys_nodup m))
    (fun k v => by
      rw [List.mem_filter, GMap.mem_toList, lookup_filter]
      cases h : m !! k with
      | none => simp [Option.filter]
      | some w =>
        by_cases hp : P k w = true
        · simp [Option.filter, hp]
          intro e; subst e; exact hp
        · simp [Option.filter, hp]
          intro e; subst e; simpa using hp)).symm
  exact h.flatMap_right _

/-- A map's ids: those of the entries a filter keeps and those it drops. -/
theorem flatIds_filter_split (m : GMap w64 Pending) (P : w64 → Pending → Bool) :
    (flatIds m).Perm (flatIds (GMap.filter P m) ++ flatIds (GMap.filter (fun k v => !P k v) m)) := by
  refine List.Perm.trans ?_ (List.Perm.append (flatIds_filter_perm m _) (flatIds_filter_perm m _)).symm
  rw [← List.flatMap_append]
  exact ((List.filter_append_perm (fun kv : w64 × Pending => P kv.1 kv.2) m.toList).flatMap_right
    _).symm.trans (by simp)

/-- A state whose free and pending ids are those of a well-formed state, up to order (and whose
free ids increase), is well-formed and caches the same ids. -/
theorem move_ok {σ τ : FLState} (hwf : σ.WF) (hperm : τ.allIds.Perm σ.allIds)
    (hincr : PgidsIncr τ.free)
    (hlen : ∀ t p, τ.pending !! t = some p → p.ids.length = p.alloctx.length) :
    τ.WF ∧ ∀ x, τ.cached x ↔ σ.cached x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  refine ⟨⟨hperm.nodup_iff.2 h1, fun id hid => h2 id (hperm.mem_iff.1 hid), hincr,
    by rw [hperm.length_eq]; exact h4, hlen⟩, fun x => ?_⟩
  unfold FLState.cached; exact hperm.mem_iff

/-- `m` without the keys of `vis` up to `txid` (`release`'s loop, having visited `vis`). -/
def dropUpTo {V : Type} (vis : List w64) (txid : w64) (m : GMap w64 V) : GMap w64 V :=
  GMap.filter (fun k _ => !(decide (k ∈ vis) && decide (uint.Z k ≤ uint.Z txid))) m

theorem dropUpTo_nil {V : Type} (txid : w64) (m : GMap w64 V) : dropUpTo [] txid m = m := by
  apply GMap.map_eq; intro k
  unfold dropUpTo; rw [lookup_filter]; cases m !! k <;> simp [Option.filter]

theorem dropUpTo_notvis {V : Type} {vis : List w64} {k : w64} (txid : w64) (m : GMap w64 V)
    (h : k ∉ vis) : (dropUpTo vis txid m) !! k = m !! k := by
  unfold dropUpTo; rw [lookup_filter]; cases m !! k <;> simp [Option.filter, h]

theorem dropUpTo_le {V : Type} {vis : List w64} {key txid : w64} (m : GMap w64 V)
    (hle : uint.Z key ≤ uint.Z txid) :
    dropUpTo (vis ++ [key]) txid m = GMap.delete key (dropUpTo vis txid m) := by
  apply GMap.map_eq; intro k
  unfold dropUpTo; rw [GMap.lookup_delete_iff, lookup_filter, lookup_filter]
  by_cases hk : key = k
  · subst hk; cases m !! key <;> simp [Option.filter, hle]
  · simp only [hk, if_false, List.mem_append, List.mem_singleton, Ne.symm hk, _root_.or_false]

theorem dropUpTo_gt {V : Type} {vis : List w64} {key txid : w64} (m : GMap w64 V)
    (hgt : ¬ uint.Z key ≤ uint.Z txid) :
    dropUpTo (vis ++ [key]) txid m = dropUpTo vis txid m := by
  apply GMap.map_eq; intro k
  unfold dropUpTo; rw [lookup_filter, lookup_filter]
  by_cases hk : key = k
  · subst hk; cases m !! key <;> simp [Option.filter, hgt]
  · simp only [List.mem_append, List.mem_singleton, Ne.symm hk, _root_.or_false]

theorem dropUpTo_all {V : Type} {vis : List w64} (txid : w64) (m : GMap w64 V)
    (h : ∀ k, (m !! k).isSome → k ∈ vis) :
    dropUpTo vis txid m = m.filter (fun t _ => !decide (uint.Z t ≤ uint.Z txid)) := by
  apply GMap.map_eq; intro k
  unfold dropUpTo; rw [lookup_filter, lookup_filter]
  cases hm : m !! k with
  | none => rfl
  | some v => simp [Option.filter, h k (by simp [hm])]

/-- The ids of the entries of a map, gathered in the order of a list of its keys. -/
theorem flatIds_keys (m : GMap w64 Pending) (keys : List w64)
    (hk : ∀ k, k ∈ keys ↔ (m !! k).isSome) (hnd : keys.Nodup) :
    (keys.flatMap (fun t => ((m !! t).getD ⟨[], [], 0⟩).ids)).Perm (flatIds m) := by
  have := pendingIds_perm_keys ⟨[], m, ∅, []⟩ keys hk hnd
  simpa [FLState.pendingOf, FLState.pendingIds, flatIds] using this

theorem Pending.equiv_refl (p : Pending) : p.equiv p := ⟨List.Perm.refl _, rfl⟩

/-- The ids `release(txid)` merges into the free ids, and the facts `mergeSpans` needs. -/
theorem release_pre {σ : FLState} {txid : w64} {L : List w64} (hwf : σ.WF)
    (hL : L.Perm (flatIds (σ.pending.filter (fun t _ => decide (uint.Z t ≤ uint.Z txid))))) :
    σ.allIds.Perm ((σ.free ++ L) ++
      flatIds (σ.pending.filter (fun t _ => !decide (uint.Z t ≤ uint.Z txid)))) ∧
    (σ.free ++ L).Nodup ∧ (∀ y ∈ L, 2 ≤ uint.Z y) ∧ σ.free.length + L.length < 2 ^ 63 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  have hall : σ.allIds.Perm ((σ.free ++ L) ++
      flatIds (σ.pending.filter (fun t _ => !decide (uint.Z t ≤ uint.Z txid)))) := by
    unfold FLState.allIds
    rw [pendingIds_eq, List.append_assoc]
    exact List.Perm.append_left _
      ((flatIds_filter_split σ.pending (fun t _ => decide (uint.Z t ≤ uint.Z txid))).trans
        (List.Perm.append_right _ hL.symm))
  refine ⟨hall, (List.nodup_append.1 (hall.nodup_iff.1 h1)).1, fun y hy => ?_, ?_⟩
  · exact h2 y (hall.mem_iff.2 (List.mem_append_left _ (List.mem_append_right _ hy)))
  · have := hall.length_eq; simp only [List.length_append] at this; omega

/-- The state after `release(txid)` merged the released ids into the free ids `free'`. -/
def FLState.releasedState (σ : FLState) (txid : w64) (free' : List w64) : FLState :=
  { σ with
    free := free'
    pending := σ.pending.filter (fun t _ => !decide (uint.Z t ≤ uint.Z txid)) }

/-- The state after `release(txid)`: well-formed, the same ids cached, `σ.release txid` up to
order. -/
theorem release_ok {σ : FLState} {txid : w64} {L free' : List w64} (hwf : σ.WF)
    (hL : L.Perm (flatIds (σ.pending.filter (fun t _ => decide (uint.Z t ≤ uint.Z txid)))))
    (hf : free'.Perm (σ.free ++ L)) (hinc : PgidsIncr free') :
    (σ.releasedState txid free').WF ∧ (∀ x, (σ.releasedState txid free').cached x ↔ σ.cached x) ∧
    (σ.releasedState txid free').equiv (σ.release txid) := by
  obtain ⟨hall, -, -, -⟩ := release_pre hwf hL
  have hperm : (σ.releasedState txid free').allIds.Perm σ.allIds :=
    List.Perm.trans (List.Perm.append_right _ hf) hall.symm
  obtain ⟨hw, hc⟩ := move_ok hwf hperm hinc (fun t p hp => by
    unfold FLState.releasedState at hp
    simp only [lookup_filter] at hp
    apply hwf.2.2.2.2 t p
    cases h : σ.pending !! t <;> simp_all [Option.filter])
  refine ⟨hw, hc, ?_, List.Perm.refl _, rfl, fun t => Iff.rfl, fun t p q hp hq => ?_⟩
  · exact hf.trans (List.Perm.append_left _ hL)
  · have : p = q := Option.some.inj (hp.symm.trans hq)
    subst this; exact Pending.equiv_refl p

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

section specs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `AddReadonlyTXID(tid)`: `tid` is a read-only transaction. -/
def FLImpl.AddReadonlySpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (tid : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"AddReadonlyTXID" I.iv)) (Val #tid))
    {{ RET #(); ownFL I s { σ with readonly := σ.readonly ++ [tid] } }}

/-- `RemoveReadonlyTXID(tid)`: one `tid` is no longer a read-only transaction (the rest in
some order: `shared`'s swaps the last one into its place). -/
def FLImpl.RemoveReadonlySpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (tid : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"RemoveReadonlyTXID" I.iv)) (Val #tid))
    {{ (ro : List w64), RET #(); ⌜ro.Perm (σ.readonly.erase tid)⌝ ∗
        ownFL I s { σ with readonly := ro } }}

/-- `ReleasePendingPages()` (`FLState.releasePending`, up to order). -/
def FLImpl.ReleasePendingSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"ReleasePendingPages" I.iv)) (Val #()))
    {{ (σ' : FLState), RET #(); ⌜σ'.equiv σ.releasePending⌝ ∗ ownFL I s σ' }}

/-- `Free(txid, p)`: the page `p` and its overflow pages are pending for `txid`. -/
def FLImpl.FreeSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (txid : w64) (p : Loc)
    (pv : go_etcd_io.bbolt.internal.common.Page) (dq : DFrac),
    σ.canFree txid pv.id' (uint.nat pv.overflow' + 1) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        p ↦{dq} pv }}
      (App (App (Val #(methods I.ity go!"Free" I.iv)) (Val #txid)) (Val #p))
    {{ RET #(); ownFL I s (σ.freePages txid pv.id' (uint.nat pv.overflow' + 1)) ∗ p ↦{dq} pv }}

/-- `Rollback(txid)` (`FLState.rollback`). -/
def FLImpl.RollbackSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (txid : w64), σ.canRollback txid →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"Rollback" I.iv)) (Val #txid))
    {{ RET #(); ownFL I s (σ.rollback txid) }}

/-- `Freed(id)`: `id` is free or pending. -/
def FLImpl.FreedSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (id : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"Freed" I.iv)) (Val #id))
    {{ RET #(decide (σ.cached id)); ownFL I s σ }}

/-- `FreeCount()`: the number of free ids. -/
def FLImpl.IfaceFreeCountSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"FreeCount" I.iv)) (Val #()))
    {{ RET #(W64 (σ.free.length : Int)); ownFL I s σ }}

/-- `PendingCount()`: the number of pending ids. -/
def FLImpl.PendingCountSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"PendingCount" I.iv)) (Val #()))
    {{ RET #(W64 (σ.pendingCount : Int)); ownFL I s σ }}

/-- `Count()`: the number of free and pending ids. -/
def FLImpl.CountSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"Count" I.iv)) (Val #()))
    {{ RET #(W64 ((σ.free.length + σ.pendingCount : Nat) : Int)); ownFL I s σ }}

/-- `Read(p)`: the free ids become the ids of the freelist page `p`, sorted. An empty page
needs no free ids before (`hashMap.Init` of no ids keeps the old cache). -/
def FLImpl.ReadSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (p : Loc) (pv : go_etcd_io.bbolt.internal.common.Page) (dq : DFrac)
    (c : w64) (xs : List w64) (dq2 : DFrac),
    p.locCar ≠ 0 → pv.flags' = W16 16 → (fpOverflow pv → 0 ≤ sint.Z c) →
    xs.Nodup → (∀ x ∈ xs, 2 ≤ uint.Z x ∧ x ∉ σ.pendingIds) → xs.length + σ.pendingCount < 2 ^ 63 →
    (xs ≠ [] ∨ σ.free = []) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}
      (App (Val #(methods I.ity go!"Read" I.iv)) (Val #p))
    {{ (free' : List w64), RET #(); ⌜PgidsIncr free' ∧ free'.Perm xs⌝ ∗
        ownFL I s { σ with free := free' } ∗
        p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}

/-- `Reload(p)`: the free ids become the ids of the freelist page `p` that are not pending,
sorted. The page may hold pending ids (bbolt writes the free and the pending ids into it;
`Commit`'s rollback reloads it while an older transaction's pending entry survives). An empty
page needs no free ids before (`hashMap.Init` of no ids keeps the old cache). -/
def FLImpl.ReloadSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (p : Loc) (pv : go_etcd_io.bbolt.internal.common.Page) (dq : DFrac)
    (c : w64) (xs : List w64) (dq2 : DFrac),
    p.locCar ≠ 0 → pv.flags' = W16 16 → (fpOverflow pv → 0 ≤ sint.Z c) →
    xs.Nodup → (∀ x ∈ xs, 2 ≤ uint.Z x) → xs.length + σ.pendingCount < 2 ^ 63 →
    (xs ≠ [] ∨ σ.free = []) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}
      (App (Val #(methods I.ity go!"Reload" I.iv)) (Val #p))
    {{ (free' : List w64), RET #();
        ⌜PgidsIncr free' ∧ free'.Perm (xs.filter (fun x => decide (x ∉ σ.pendingIds)))⌝ ∗
        ownFL I s { σ with free := free' } ∗
        p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}

/-- `NoSyncReload(pgIds)`: the free ids become the increasing ids `pgIds` but the pending ones.
If none is left, there must be no free ids before (`hashMap.Init` of no ids keeps the old
cache). -/
def FLImpl.NoSyncReloadSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (pg : GoSlice) (xs : List w64) (dq : DFrac),
    PgidsIncr xs → (∀ x ∈ xs, 2 ≤ uint.Z x) → xs.length + σ.pendingCount < 2 ^ 63 →
    (xs.filter (fun x => decide (x ∉ σ.pendingIds)) ≠ [] ∨ σ.free = []) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        pg ↦*{dq} xs }}
      (App (Val #(methods I.ity go!"NoSyncReload" I.iv)) (Val #pg))
    {{ RET #(); ownFL I s { σ with free := xs.filter (fun x => decide (x ∉ σ.pendingIds)) } ∗
        pg ↦*{dq} xs }}

/-- `EstimatedWritePageSize()`: the size of the page `Write` writes. -/
def FLImpl.EstimatedWritePageSizeSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"EstimatedWritePageSize" I.iv)) (Val #()))
    {{ RET #(W64 (16 + 8 * (flCells σ.allIds.length : Nat))); ownFL I s σ }}

/-- `Write(p)`: `p` becomes a freelist page of the free and pending ids, sorted. -/
def FLImpl.WriteSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (p : Loc) (pv : go_etcd_io.bbolt.internal.common.Page)
    (old : List w64),
    p.locCar ≠ 0 → old.length = flCells σ.allIds.length →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        p ↦ pv ∗ slice.mk (p +ₗ 16) (W64 (old.length : Int)) (W64 (old.length : Int)) ↦* old }}
      (App (Val #(methods I.ity go!"Write" I.iv)) (Val #p))
    {{ (out : List w64), RET #(); ⌜PgidsSorted out ∧ out.Perm σ.allIds⌝ ∗ ownFL I s σ ∗
        p ↦ ({ pv with flags' := W16 16, count' := flCount σ.allIds.length } :
          go_etcd_io.bbolt.internal.common.Page) ∗
        slice.mk (p +ₗ 16) (W64 (old.length : Int)) (W64 (old.length : Int)) ↦*
          (if 65535 ≤ σ.allIds.length then W64 (σ.allIds.length : Int) :: out else out) }}

/-- `Init(ids)`: the free ids become `ids` (the new state well-formed; the slice is kept). Of no
ids, there must be no free ids before (`hashMap.Init` of no ids keeps the old cache). -/
def FLImpl.IfaceInitSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (ids : GoSlice) (xs : List w64),
    ({ σ with free := xs } : FLState).WF → (xs ≠ [] ∨ σ.free = []) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        ids ↦* xs ∗ ownSliceCap w64 ids (DFrac.own 1) }}
      (App (Val #(methods I.ity go!"Init" I.iv)) (Val #ids))
    {{ RET #(); ownFL I s { σ with free := xs } }}

/-- The freelist interface's methods, as its users call them. -/
structure FLImpl.IfaceContract (I : FLImpl (GF := GF)) : Prop where
  addReadonly : I.AddReadonlySpec
  removeReadonly : I.RemoveReadonlySpec
  releasePending : I.ReleasePendingSpec
  allocate : I.AllocateSpec
  free : I.FreeSpec
  rollback : I.RollbackSpec
  freed : I.FreedSpec
  freeCount : I.IfaceFreeCountSpec
  pendingCount : I.PendingCountSpec
  count : I.CountSpec
  read : I.ReadSpec
  write : I.WriteSpec
  estimatedWritePageSize : I.EstimatedWritePageSizeSpec
  reload : I.ReloadSpec
  noSyncReload : I.NoSyncReloadSpec
  init : I.IfaceInitSpec

end specs

end bbolt
end EtcdGrove
end Perennial
