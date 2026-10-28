/-
The informers' batch path (`InOrderInformersBatchProcess`, on by default, which `Main` keeps): what
the specs of `RealFIFO.PopBatch` (gap D3), `threadSafeMap.Transaction` (gap C4), `cache.Transaction`,
`processDeltasInBatch` and the shared informer's `handleBatchDeltas` are stated with. Lean-first;
phase 4 of `notes/k8s-daemonset-plan.md` (fourth round).

* `Tx`: one write of a store transaction (`ThreadSafeStoreTransaction`: its type, key, object);
  `St.txn`: the thread-safe store after a transaction (`Transaction` applies each key's last write,
  which for writes of the three known types is the writes applied in order; the resource version
  becomes the last object's when its accessor has one).
* `FQ.batch`: the deltas `PopBatch` takes from the queue (a lone unbatchable delta, or the longest
  prefix of batchable ones, at most 1000 and, while initial items remain, at most their count);
  `FQ.popDoneN`: its deferred step (that many initial items fewer).
* `batchStep`: what `processDeltasInBatch` does to the store and the handler for a batch of object
  deltas: the store's items after each delta in order, its resource version the last object's (the
  whole batch is one transaction), then every event, in order, each `OnUpdate`'s old object the key's
  object after the deltas before it (`inBatch`, else the store's).
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section model
variable [GooseExts] [GoGlobalContext]

/-- **One write of a store transaction** (`ThreadSafeStoreTransaction`): its type, key, object. -/
structure Tx where
  t : GoString
  k : GoString
  o : GoInterface

/-- The write as the Go `Transaction` (`cache.Transaction`'s argument). -/
def Tx.txn (x : Tx) : Transaction := Transaction.mk x.o x.t

/-- The write as the Go `ThreadSafeStoreTransaction` (`threadSafeMap.Transaction`'s argument). -/
def Tx.go (x : Tx) : ThreadSafeStoreTransaction := ThreadSafeStoreTransaction.mk x.txn x.k

/-- A write's type is one `Transaction` applies (`TransactionTypeAdd`/`Update`/`Delete`). -/
def Tx.typeOk (x : Tx) : Prop := x.t = go!"Add" ∨ x.t = go!"Update" ∨ x.t = go!"Delete"

/-- One write applied to the items (`updateLocked` for `Add`/`Update`, `deleteLocked` for
`Delete`). -/
def txItems (it : Items) (x : Tx) : Items :=
  if x.t = go!"Delete" then GMap.delete x.k it else <[x.k := x.o]> it

/-- **The store after `Transaction(xs)`** at `σ`: nothing for no write; else the writes applied in
order (each key's last write wins), the resource version the last object's if its accessor has
one (`rvOf`), else kept. -/
def St.txn (rvOf : GoInterface → Option GoString) (σ : St) (xs : List Tx) : St :=
  match xs.getLast? with
  | none => σ
  | some x => { σ with items := xs.foldl txItems σ.items, rv := (rvOf x.o).getD σ.rv }

/-! ### The batch `PopBatch` takes -/

/-- A delta `PopBatch` batches (`batchable`: `Sync`, `Replaced`, `Added`, `Updated`, `Deleted`; not
a relist's `ReplacedAll` nor a `Bookmark`). -/
def FD.batchable : FD → Bool
  | .obj t _ => decide (t = go!"Sync" ∨ t = go!"Replaced" ∨ t = go!"Added" ∨ t = go!"Updated" ∨
      t = go!"Deleted")
  | _ => false

/-- **The deltas `PopBatch` takes** from a queue: the first alone if it is not batchable; else the
longest prefix of batchable deltas of at most `batchSize` (1000) and, while initial items remain
(`initCount > 0`), at most their count. -/
def FQ.batch [GooseExts] (q : FQ) : List FD :=
  match q.items with
  | [] => []
  | d :: ds =>
    if d.batchable then
      ((d :: ds).take (if 0 < q.initCount then min 1000 q.initCount else 1000)).takeWhile
        FD.batchable
    else [d]

/-- `PopBatch`'s deferred step after a batch of `n` deltas: `n` initial items fewer, synced once
none is left (`checkSynced`). -/
def FQ.popDoneN [GooseExts] (n : Nat) (q : FQ) : FQ :=
  if 0 < q.initCount then
    { q with initCount := q.initCount - n,
             synced := q.synced || (q.populated && q.initCount - n == 0) }
  else q

theorem FQ.popDoneN_one [GooseExts] (q : FQ) : q.popDoneN 1 = q.popDone := rfl

theorem FQ.batch_prefix [GooseExts] (q : FQ) : q.batch <+: q.items := by
  unfold FQ.batch
  cases q.items with
  | nil => exact List.nil_prefix
  | cons d ds =>
    simp only
    split
    · exact (List.takeWhile_prefix _).trans (List.take_prefix _ _)
    · exact ⟨ds, rfl⟩

/-! ### A batch processed (`processDeltasInBatch`) -/

/-- The items after an object delta (a deletion removes its key, any other stores the object). -/
def fdItems (KF : GoInterface → GoString) (it : Items) : FD → Items
  | .obj t o => if t = go!"Deleted" then GMap.delete (KF o) it else <[KF o := o]> it
  | _ => it

/-- The object of an object delta (`nil` for another). -/
def FD.obj? : FD → GoInterface
  | .obj _ o => o
  | _ => interface.nil

/-- An object delta's event over the current items `it`: a deletion's `OnDelete`; another's
`OnUpdate` of the key's current object if it is not `nil`, else `OnAdd` (`putEvR`). -/
def fdEv (KF : GoInterface → GoString) (b : Bool) (it : Items) (t : GoString) (o : GoInterface) : Ev :=
  if t = go!"Deleted" then Ev.delete o else putEvR it (KF o) o b

/-- **The events of a batch**, from the items `it` before it, each delta's over the items after
the deltas before it (`inBatch`, else the store's). -/
def batchEvs (KF : GoInterface → GoString) (b : Bool) : Items → List FD → List Ev
  | _, [] => []
  | it, .obj t o :: ds => fdEv KF b it t o :: batchEvs KF b (fdItems KF it (.obj t o)) ds
  | it, _ :: ds => batchEvs KF b it ds

/-- An object delta's store write over the current items `it` (`processDeltasInBatch`'s
`Transaction`): `Delete` for a deletion; else `Update` if the key's current object is not `nil`,
`Add` otherwise. -/
def fdTx (KF : GoInterface → GoString) (it : Items) (t : GoString) (o : GoInterface) : Tx :=
  if t = go!"Deleted" then ⟨go!"Delete", KF o, o⟩
  else ⟨if objAt it (KF o) ≠ interface.nil then go!"Update" else go!"Add", KF o, o⟩

/-- **The writes of a batch** (`txns`), each delta's over the items after the deltas before it. -/
def batchTxs (KF : GoInterface → GoString) : Items → List FD → List Tx
  | _, [] => []
  | it, .obj t o :: ds => fdTx KF it t o :: batchTxs KF (fdItems KF it (.obj t o)) ds
  | it, _ :: ds => batchTxs KF it ds

theorem batchEvs_snoc (KF : GoInterface → GoString) (b : Bool) (t : GoString) (o : GoInterface) :
    ∀ (ds : List FD) (it : Items), batchEvs KF b it (ds ++ [.obj t o]) =
      batchEvs KF b it ds ++ [fdEv KF b (ds.foldl (fdItems KF) it) t o]
  | [], it => rfl
  | .obj t' o' :: ds, it => by
      simp only [List.cons_append, batchEvs, List.foldl_cons, batchEvs_snoc KF b t o ds]
  | .replaced _ _ :: ds, it => by
      simp only [List.cons_append, batchEvs, List.foldl_cons, batchEvs_snoc KF b t o ds]; rfl
  | .bookmark _ :: ds, it => by
      simp only [List.cons_append, batchEvs, List.foldl_cons, batchEvs_snoc KF b t o ds]; rfl

theorem batchTxs_snoc (KF : GoInterface → GoString) (t : GoString) (o : GoInterface) :
    ∀ (ds : List FD) (it : Items), batchTxs KF it (ds ++ [.obj t o]) =
      batchTxs KF it ds ++ [fdTx KF (ds.foldl (fdItems KF) it) t o]
  | [], it => rfl
  | .obj t' o' :: ds, it => by
      simp only [List.cons_append, batchTxs, List.foldl_cons, batchTxs_snoc KF t o ds]
  | .replaced _ _ :: ds, it => by
      simp only [List.cons_append, batchTxs, List.foldl_cons, batchTxs_snoc KF t o ds]; rfl
  | .bookmark _ :: ds, it => by
      simp only [List.cons_append, batchTxs, List.foldl_cons, batchTxs_snoc KF t o ds]; rfl

/-- The writes applied in order leave the items the deltas leave. -/
theorem batchTxs_items (KF : GoInterface → GoString) :
    ∀ (ds : List FD) (it0 it : Items), (batchTxs KF it0 ds).foldl txItems it = ds.foldl (fdItems KF) it
  | [], _, _ => rfl
  | .obj t o :: ds, it0, it => by
      simp only [batchTxs, List.foldl_cons]
      rw [batchTxs_items KF ds]
      congr 1
      unfold txItems fdTx fdItems
      by_cases h : t = go!"Deleted"
      · simp [h]
      · simp only [h, ↓reduceIte]
        split <;> simp
  | .replaced _ _ :: ds, it0, it => by
      simp only [batchTxs, List.foldl_cons]; rw [batchTxs_items KF ds]; rfl
  | .bookmark _ :: ds, it0, it => by
      simp only [batchTxs, List.foldl_cons]; rw [batchTxs_items KF ds]; rfl

theorem batchTxs_typeOk (KF : GoInterface → GoString) :
    ∀ (ds : List FD) (it : Items), ∀ x ∈ batchTxs KF it ds, x.typeOk
  | [], _ => by simp [batchTxs]
  | .obj t o :: ds, it => by
      intro x hx
      simp only [batchTxs, List.mem_cons] at hx
      rcases hx with rfl | hx
      · unfold fdTx Tx.typeOk; split
        · simp
        · split <;> simp
      · exact batchTxs_typeOk KF ds _ x hx
  | .replaced _ _ :: ds, it => batchTxs_typeOk KF ds it
  | .bookmark _ :: ds, it => batchTxs_typeOk KF ds it

theorem batchTxs_keyed (KF : GoInterface → GoString) :
    ∀ (ds : List FD) (it : Items), ∀ x ∈ batchTxs KF it ds, x.k = KF x.o
  | [], _ => by simp [batchTxs]
  | .obj t o :: ds, it => by
      intro x hx
      simp only [batchTxs, List.mem_cons] at hx
      rcases hx with rfl | hx
      · unfold fdTx; split <;> rfl
      · exact batchTxs_keyed KF ds _ x hx
  | .replaced _ _ :: ds, it => batchTxs_keyed KF ds it
  | .bookmark _ :: ds, it => batchTxs_keyed KF ds it

theorem batchTxs_objs (KF : GoInterface → GoString) :
    ∀ (ds : List FD) (it : Items), ∀ x ∈ batchTxs KF it ds, x.o ∈ ds.map FD.obj?
  | [], _ => by simp [batchTxs]
  | .obj t o :: ds, it => by
      intro x hx
      simp only [batchTxs, List.mem_cons] at hx
      rcases hx with rfl | hx
      · have : (fdTx KF it t o).o = o := by unfold fdTx; split <;> rfl
        rw [this]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (batchTxs_objs KF ds _ x hx)
  | .replaced _ _ :: ds, it => fun x hx => List.mem_cons_of_mem _ (batchTxs_objs KF ds it x hx)
  | .bookmark _ :: ds, it => fun x hx => List.mem_cons_of_mem _ (batchTxs_objs KF ds it x hx)

/-- For object deltas, the last write's object is the last delta's. -/
theorem batchTxs_last (KF : GoInterface → GoString) :
    ∀ (ds : List FD) (it : Items), (∀ d ∈ ds, ∃ t o, d = .obj t o) →
      (batchTxs KF it ds).getLast?.map Tx.o = ds.getLast?.map FD.obj?
  | [], _, _ => rfl
  | .obj t o :: ds, it, h => by
      have ih := batchTxs_last KF ds (fdItems KF it (.obj t o))
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      cases ds with
      | nil => simp only [batchTxs, List.getLast?_singleton, Option.map_some]; unfold fdTx; split <;> rfl
      | cons d ds' =>
        obtain ⟨t', o', rfl⟩ := h d (by simp)
        simp only [batchTxs] at ih ⊢
        rw [List.getLast?_cons_cons, List.getLast?_cons_cons]
        exact ih
  | .replaced _ _ :: ds, it, h => by obtain ⟨_, _, h⟩ := h _ List.mem_cons_self; cases h
  | .bookmark _ :: ds, it, h => by obtain ⟨_, _, h⟩ := h _ List.mem_cons_self; cases h

/-- **The transaction of a batch's writes is the batch's store step.** -/
theorem txn_batchTxs (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString)
    (σ : St) (ds : List FD) (h : ∀ d ∈ ds, ∃ t o, d = .obj t o) :
    St.txn rvOf σ (batchTxs KF σ.items ds) = (match ds.getLast? with
      | none => σ
      | some d => { σ with items := ds.foldl (fdItems KF) σ.items,
                           rv := (rvOf d.obj?).getD σ.rv }) := by
  have hl := batchTxs_last KF ds σ.items h
  unfold St.txn
  cases hx : (batchTxs KF σ.items ds).getLast? with
  | none =>
    rw [hx] at hl
    cases hd : ds.getLast? with
    | none => rfl
    | some d => rw [hd] at hl; cases hl
  | some x =>
    rw [hx] at hl
    cases hd : ds.getLast? with
    | none => rw [hd] at hl; cases hl
    | some d =>
      rw [hd] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      simp only [batchTxs_items, hl]

/-- **A batch of object deltas processed** at the store's state `σ`: the store's next state (one
transaction: the items after each delta in order, the resource version the last object's when its
accessor has one) and the handler's events, in order. -/
def batchStep (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString) (b : Bool)
    (σ : St) (ds : List FD) (σ' : St) (evs : List Ev) : Prop :=
  σ' = (match ds.getLast? with
    | none => σ
    | some d => { σ with items := ds.foldl (fdItems KF) σ.items,
                         rv := (rvOf d.obj?).getD σ.rv }) ∧
  evs = batchEvs KF b σ.items ds

/-- **The store's next state for a batch** (`batchStep`'s store component, a function). -/
def batchStore (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString) (σ : St)
    (ds : List FD) : St :=
  match ds.getLast? with
  | none => σ
  | some d => { σ with items := ds.foldl (fdItems KF) σ.items, rv := (rvOf d.obj?).getD σ.rv }

theorem batchStep_store (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString)
    (b : Bool) (σ σ' : St) (ds : List FD) (evs : List Ev) (h : batchStep KF rvOf b σ ds σ' evs) :
    σ' = batchStore KF rvOf σ ds := h.1

/-- The last write to key `k` in a batch: `some (some o)` for a put of `o`, `some none` for a
deletion, `none` for no write. -/
def lastWr (KF : GoInterface → GoString) : List FD → GoString → Option (Option GoInterface)
  | [], _ => none
  | d :: ds, k =>
    match lastWr KF ds k with
    | some v => some v
    | none =>
      match d with
      | .obj t o => if KF o = k then some (if t = go!"Deleted" then none else some o) else none
      | _ => none

/-- The items after a batch at a key: its last write's, else as before. -/
theorem fdItems_fold_lookup (KF : GoInterface → GoString) :
    ∀ (ds : List FD) (it : Items) (k : GoString),
      (ds.foldl (fdItems KF) it) !! k = (lastWr KF ds k).getD (it !! k)
  | [], it, k => rfl
  | d :: ds, it, k => by
    simp only [List.foldl_cons, lastWr]
    rw [fdItems_fold_lookup KF ds]
    cases h : lastWr KF ds k with
    | some v => rfl
    | none =>
      simp only [Option.getD_none]
      cases d with
      | obj t o =>
        unfold fdItems
        by_cases hk : KF o = k
        · subst hk; by_cases ht : t = go!"Deleted" <;> simp [ht]
        · by_cases ht : t = go!"Deleted" <;> simp [ht, hk]
      | replaced _ _ => rfl
      | bookmark _ => rfl

/-- **Applying a batch's store step twice is applying it once.** -/
theorem batchStore_idem (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString)
    (σ : St) (ds : List FD) : batchStore KF rvOf (batchStore KF rvOf σ ds) ds = batchStore KF rvOf σ ds := by
  unfold batchStore
  cases hl : ds.getLast? with
  | none => rfl
  | some d =>
    simp only
    congr 1
    · apply GMap.ext; intro k
      rw [fdItems_fold_lookup, fdItems_fold_lookup]
      cases lastWr KF ds k <;> rfl
    · cases rvOf d.obj? <;> rfl

/-- An object delta of a kind the atomic FIFO queues. -/
def FD.isObjOk (d : FD) : Prop := (∃ t o, d = .obj t o) ∧ d.kindOk

end model

section tyOk
variable [GooseExts] [go_gctx : GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- **The method-set facts of the batch path** (`methodSet` is uninterpreted in the model, so they
are premises, as `k8setcd3.objTyOk`): `*threadSafeMap` implements `ThreadSafeStoreWithTransaction`
(its `Transaction`, `thread_safe_store.go:269`), `*cache` implements `TransactionStore` (its
`Transaction`, `store.go:220`, with `Store`'s methods), and `*RealFIFO` implements `QueueWithBatch`
(its `PopBatch`, `the_real_fifo.go:486`, with `Queue`'s). All three hold of the Go code (each type
declares the method with the interface's signature; client-go checks the third at compile time,
`var _ QueueWithBatch = &RealFIFO{}`). -/
def batchTyOk : Prop :=
  go.typeSetContains (go.GoType.PointerType threadSafeMap.ty) ThreadSafeStoreWithTransaction.ty = true ∧
  go.typeSetContains (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) TransactionStore.ty = true ∧
  go.typeSetContains (go.GoType.PointerType RealFIFO.ty) QueueWithBatch.ty = true

end tyOk

end cache
end EtcdGrove
end Perennial
