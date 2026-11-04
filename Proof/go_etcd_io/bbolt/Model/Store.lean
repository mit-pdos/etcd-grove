/-
The page store as pure state (U0a of `notes/bbolt-proof-plan.md`; design §3.6): the
classification of the file's slots, the readers and the writer's view, the lending arithmetic,
the store's invariant `storeOK`, its transitions (one per `Inv/Store.lean` lemma), and the
statements that each transition keeps `storeOK` under its side conditions (proved by U3).

Store slots are the current tree's and the pending pages'; the other data slots (free, allocated
by the live writer, the synced freelist page, at or past `hwm`, the mapping's holes) are the
writer side's `W` slots (`Inv/Locks.lean`); slots 0 and 1 are the metas.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Mvcc
public import Perennial.Proof.sync.RWMutexGuard

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris

section store
variable [GooseExts]

/-- The state of the memory map: `some (base, len)`, mapped at `base` for `len` bytes; `none`
before the first `mmap`, after a failed remap, and once closed. -/
abbrev MapSt := Option (Loc × Nat)

/-- `db.datasz` in the state `ms`. -/
def mapLen : MapSt → Nat
  | some (_, len) => len
  | none => 0

/-- **The state of the page store** (`pagesInv`): the mapping, the committed state, the
freelist, the registered readers, the writer's base view (recorded from its begin to its close),
the live writer's txid, whether it has published (between its meta write and its `close`),
whether the writer's view is lent (`wlent`: false while it is parked for a remap, U0a deviation:
the store keeps the parked view, so that re-borrowing it on the new base needs no fact the writer
cannot know), and the bytes of the store slots (stable while they are store slots). -/
structure StoreSt where
  ms : MapSt
  C : CommitSt
  fl : FLPg
  R : GMap Nat RdInfo
  wv : Option View
  wtx : Option Nat
  pub : Bool
  wlent : Bool
  bytes : Nat → List w8

/-- The writer's part of the store's state, which the store and the writer share (`ghostVar
B.wv`): its view, its txid, published, lent. -/
abbrev WSt := Option View × Option Nat × Bool × Bool

/-- The writer's part of `σ`. -/
def StoreSt.wst (σ : StoreSt) : WSt := (σ.wv, σ.wtx, σ.pub, σ.wlent)

/-- No live writer. -/
def wIdle : WSt := (none, none, false, false)

/-- The store slots: the current tree's and the pending pages'. -/
def storeSlots (σ : StoreSt) : List Nat := listDedup (treeSlots σ.C ++ pendSlots σ.fl)

/-- What a reader borrows of each slot of its view (a quarter of its `mmaplock` fraction). -/
def rq : Qp := sync.rfrac.half.half

/-- What the writer borrows of each slot of its base view. -/
def wq : Qp := (1 : Qp).half.half.half

/-- Adding fractions, `none` being none. -/
def optAdd (a : Qp) : Option Qp → Option Qp
  | none => some a
  | some b => some (a + b)

/-- `a` and the fractions `o` make up `whole`. -/
def fracSum (a : Qp) (o : Option Qp) (whole : Qp) : Prop :=
  match o with
  | none => a = whole
  | some s => a + s = whole

open Classical in
/-- What is lent of slot `s`: `rq` per reader whose view covers it, and `wq` if the writer's
view does. -/
def lent (σ : StoreSt) (s : Nat) : Option Qp :=
  let r := GMap.mapFold (fun _ (ri : RdInfo) acc =>
    if coversSlot ri.v.pages s then optAdd rq acc else acc) none σ.R
  match σ.wv, σ.wlent with
  | some v, true => if coversSlot v.pages s then optAdd wq r else r
  | _, _ => r

/-- The pages of `P` are the bytes of their slots in `bytes`. -/
def pagesFromBytes (bytes : Nat → List w8) (P : Pages) : Prop :=
  ∀ id pg, P !! id = some pg → pg = (List.range' id (1 + pageOverflow pg)).flatMap bytes

/-- The view's slots are store slots. -/
def viewInStore (σ : StoreSt) (v : View) : Prop :=
  ∀ s, coversSlot v.pages s → s ∈ storeSlots σ

/-- A registered reader's facts. -/
def StoreSt.rOK (σ : StoreSt) (r : RdInfo) : Prop :=
  r.v.txid ≤ σ.C.txid ∧ mvccView σ.fl r.v ∧ viewInStore σ r.v ∧ viewWF r.v ∧
  pagesFromBytes σ.bytes r.v.pages ∧ (∀ b l, σ.ms = some (b, l) → r.v.base = b)

/-- The writer's view's facts (F4.4): out until `close`, also across the commit point; its pages
stay store slots; before the publish, they are the current tree's. -/
def StoreSt.wOK (σ : StoreSt) (v : View) : Prop :=
  σ.wtx = some (v.txid + 1) ∧ mvccView σ.fl v ∧ viewInStore σ v ∧ viewWF v ∧
  pagesFromBytes σ.bytes v.pages ∧ (σ.pub = false → v.pages = σ.C.pages ∧ v.root = σ.C.root) ∧
  (σ.wlent = true → ∀ b l, σ.ms = some (b, l) → v.base = b)

/-- **The store's invariant** (design §3.6). -/
def storeOK (σ : StoreSt) : Prop :=
  σ.C.metaOk ∧ treeOK σ.C ∧ flBelow σ.fl σ.C σ.wtx ∧ σ.fl.WF ∧
  (∀ w, σ.wtx = some w → w = σ.C.txid + (if σ.pub then 0 else 1)) ∧
  (σ.wtx = none → σ.pub = false) ∧
  (∀ k r, σ.R !! k = some r → σ.rOK r) ∧
  (∀ v, σ.wv = some v → σ.wOK v) ∧
  pagesFromBytes σ.bytes σ.C.pages ∧
  (∀ k r, σ.R !! k = some r → pagesAgree σ.C.pages r.v.pages ∧
    ∀ v, σ.wv = some v → pagesAgree v.pages r.v.pages) ∧
  (∀ v, σ.wv = some v → pagesAgree σ.C.pages v.pages) ∧
  (∀ s ∈ storeSlots σ, 2 ≤ s ∧ (σ.bytes s).length = 4096) ∧
  (∀ b l, σ.ms = some (b, l) → ∀ s ∈ storeSlots σ, s < l / 4096) ∧
  (σ.ms = none → σ.R = ∅ ∧ σ.wlent = false) ∧ (σ.wv = none → σ.wlent = false) ∧
  (σ.wtx = none → σ.wv = none) ∧
  (∀ s, s ∈ treeSlots σ.C → s ∉ pendSlots σ.fl ∨ pendingOnlyFromWriter σ.fl σ.wtx s) ∧
  -- U3 finding 1: the current tree keeps the MVCC rule (a new view of it is safe)
  (∀ b, mvccView σ.fl (View.ofC b σ.C)) ∧
  -- U3 finding 2: every recorded allocation is by a committed transaction or the next one
  (∀ x a, σ.fl.allocs !! x = some a → a.toNat ≤ σ.C.txid + 1) ∧
  -- U3 finding 5: before the publish, a slot pending only for the writer and not in the tree
  -- (the old synced freelist page) is covered by no reader
  (σ.pub = false → ∀ s ∈ pendSlots σ.fl, s ∉ treeSlots σ.C →
    pendingOnlyFromWriter σ.fl σ.wtx s → ∀ k r, σ.R !! k = some r → ¬ coversSlot r.v.pages s) ∧
  -- the tree's pages below `2 ^ 62`, as the freelist's ids (what `Free` puts pending)
  σ.C.hwm ≤ 2 ^ 62

/-! ## Transitions (one per `Inv/Store.lean` lemma) -/

/-- A reader registers under the key `k` with the view `r.v`. -/
def StoreSt.register (σ : StoreSt) (k : Nat) (r : RdInfo) : StoreSt := { σ with R := σ.R.insert k r }
proj_simps StoreSt.register

/-- A reader deregisters. -/
def StoreSt.deregister (σ : StoreSt) (k : Nat) : StoreSt := { σ with R := σ.R.delete k }
proj_simps StoreSt.deregister

/-- The writer begins: its txid is the next one, its base view `v` borrowed. -/
def StoreSt.wbegin (σ : StoreSt) (v : View) : StoreSt :=
  { σ with wv := some v, wtx := some (σ.C.txid + 1), pub := false, wlent := true }
proj_simps StoreSt.wbegin

/-- The writer's view returned (parked) for a remap (`wtx`, `pub` kept: round 4, N6). -/
def StoreSt.wreturn (σ : StoreSt) : StoreSt := { σ with wlent := false }
proj_simps StoreSt.wreturn

/-- The writer's parked view re-borrowed after a remap, on the new base `b`. -/
def StoreSt.wborrow (σ : StoreSt) (b : Loc) : StoreSt :=
  { σ with wv := σ.wv.map (fun v => { v with base := b }), wlent := true }
proj_simps StoreSt.wborrow

/-- The writer's `close`: the view returned, no live writer (the only reset of `wtx`/`pub`). -/
def StoreSt.wclose (σ : StoreSt) : StoreSt :=
  { σ with wv := none, wtx := none, pub := false, wlent := false }
proj_simps StoreSt.wclose

/-- `Free(txid, p)` of `n` slots from `id`; when the freed page is the old synced freelist page,
its slots move `W → store` with their bytes `pg` (F4.5). -/
def StoreSt.free (σ : StoreSt) (txid id : w64) (n : Nat) (pg : Nat → List w8) : StoreSt :=
  { σ with fl := σ.fl.freePages txid id n,
           bytes := fun s => if inRun id n (W64 (s : Int)) then pg s else σ.bytes s }
proj_simps StoreSt.free

/-- `Allocate` returned the `n` ids from `r`: no longer free (they were `W` slots already). -/
def StoreSt.alloc (σ : StoreSt) (txid r : w64) (n : Nat) : StoreSt :=
  { σ with fl := σ.fl.alloc txid r n }
proj_simps StoreSt.alloc

/-- `ReleasePendingPages` with the read-only transactions `ro`: released slots `store → W`. -/
def StoreSt.release (σ : StoreSt) (ro : List w64) : StoreSt :=
  { σ with fl := σ.fl.releasePending ro }
proj_simps StoreSt.release

/-- The commit point: the committed state `C'`, whose new pages' slots move `W → store` with the
bytes `bs`; the writer has published. -/
def StoreSt.publish (σ : StoreSt) (C' : CommitSt) (bs : Nat → List w8) : StoreSt :=
  { σ with C := C', pub := true,
           bytes := fun s => if s ∈ treeSlots σ.C ∨ s ∈ pendSlots σ.fl then σ.bytes s else bs s }
proj_simps StoreSt.publish

/-- `freelist.Rollback(txid)`: `txid`'s pending pages are not pending (B3: a freed old synced
freelist page moves back `store → W`). -/
def StoreSt.rollback (σ : StoreSt) (txid : w64) : StoreSt :=
  { σ with fl := σ.fl.rollback txid }
proj_simps StoreSt.rollback

/-- The rollback of the writer's pending entry (`FLPg.rollbackEntry`), when it has one. -/
def StoreSt.rollbackE (σ : StoreSt) (txid : w64) : StoreSt :=
  { σ with fl := σ.fl.rollbackEntry txid }
proj_simps StoreSt.rollbackE

/-- `Reload`/`NoSyncReload`: the free ids rebuilt (only `W` slots become free). -/
def StoreSt.reload (σ : StoreSt) (ids : List w64) : StoreSt := { σ with fl := σ.fl.reload ids }
proj_simps StoreSt.reload

/-- `munmap`: every store cell out of the store (`store_gather`). -/
def StoreSt.gather (σ : StoreSt) : StoreSt := { σ with ms := none }
proj_simps StoreSt.gather

/-- `mmap`: the new mapping's cells in (`store_carve`). -/
def StoreSt.carve (σ : StoreSt) (base : Loc) (len : Nat) : StoreSt :=
  { σ with ms := some (base, len) }
proj_simps StoreSt.carve

/-- The loaded freelist (`Open`'s `loadFreelist`, no reader registered). -/
def StoreSt.setFl (σ : StoreSt) (fl : FLPg) : StoreSt := { σ with fl := fl }
proj_simps StoreSt.setFl

private theorem W64_toNat_eq (x : w64) : W64 (x.toNat : Int) = x := by
  simp only [W64, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem mem_pagesSlots' (P : Pages) (s : Nat) : s ∈ pagesSlots P ↔ coversSlot P s := by
  simp only [pagesSlots, List.mem_flatMap, List.mem_range', coversSlot]
  constructor
  · rintro ⟨⟨id, pg⟩, hip, j, hj, rfl⟩
    exact ⟨id, pg, (GMap.mem_toList _ _ _).1 hip, by omega, by simp only at hj; omega⟩
  · rintro ⟨id, pg, hp, h1, h2⟩
    exact ⟨(id, pg), (GMap.mem_toList _ _ _).2 hp, s - id, by simp only; omega, by omega⟩

private theorem tree_in_store' (σ : StoreSt) (s : Nat) (h : coversSlot σ.C.pages s) :
    s ∈ storeSlots σ := by
  simp only [storeSlots, mem_list_dedup, List.mem_append]
  exact Or.inl ((mem_pagesSlots' _ _).2 h)

private theorem treeSlot_lt64 (σ : StoreSt) (h : storeOK σ) (s : Nat) (hs : coversSlot σ.C.pages s) :
    s < 2 ^ 64 := by
  obtain ⟨id, pg, hp, h1, h2⟩ := hs
  have := h.2.1.2.2.2.1 id pg hp
  have hm := h.1.2.2.2.2.2.2.1.2.2.1
  have := (metaOf (σ.C.slot σ.C.txid)).pgid'.isLt
  omega

private theorem pagesAgree_refl (P : Pages) (hd : pagesDisjoint P) : pagesAgree P P := by
  intro i pi j pj s hi hj h1 h2 h3 h4
  by_cases hij : i = j
  · subst hij; rw [hi] at hj; cases hj; exact ⟨rfl, rfl⟩
  · rcases hd i pi j pj hi hj hij with h | h <;> omega

private theorem pagesAgree_symm (P Q : Pages) (h : pagesAgree P Q) : pagesAgree Q P := by
  intro i pi j pj s hi hj h1 h2 h3 h4
  obtain ⟨e1, e2⟩ := h j pj i pi s hj hi h3 h4 h1 h2
  exact ⟨e1.symm, e2.symm⟩

private theorem mem_pendSlots (fl : FLPg) (s : Nat) :
    s ∈ pendSlots fl ↔ ∃ t pd x, fl.pending !! t = some pd ∧ x ∈ pd.ids ∧ x.toNat = s := by
  simp only [pendSlots, FLPg.pendingIds, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨x, ⟨⟨t, pd⟩, hkv, hx⟩, rfl⟩
    exact ⟨t, pd, x, (GMap.mem_toList _ _ _).1 hkv, hx, rfl⟩
  · rintro ⟨t, pd, x, hp, hx, rfl⟩
    exact ⟨x, ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩, rfl⟩

private theorem not_pend_of_only_none (fl : FLPg) (s : Nat) (hs : s < 2 ^ 64)
    (h : pendingOnlyFromWriter fl none s) : s ∉ pendSlots fl := by
  intro hm
  obtain ⟨t, pd, x, hp, hx, rfl⟩ := (mem_pendSlots fl s).1 hm
  exact absurd (h t pd hp (by rw [W64_toNat_eq]; exact hx)) (by simp)

private theorem W64_toNat_of_lt' (s : Nat) (h : s < 2 ^ 64) : (W64 (s : Int)).toNat = s := by
  simp only [W64, BitVec.toNat_ofInt]; omega

private theorem run_toNat (id : w64) (n j : Nat) (hj : j < n) (hn : id.toNat + n < 2 ^ 64) :
    (id + W64 (j : Int)).toNat = id.toNat + j := by
  simp only [W64, BitVec.toNat_add, BitVec.toNat_ofInt]; omega

private theorem mem_runIds' (id : w64) (n : Nat) (x : w64) :
    x ∈ runIds id n ↔ ∃ j < n, x = id + W64 (j : Int) := by
  simp only [runIds, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

private theorem mem_runIds_toNat (id : w64) (n : Nat) (hn : id.toNat + n < 2 ^ 64) (x : w64) :
    x ∈ runIds id n ↔ id.toNat ≤ x.toNat ∧ x.toNat < id.toNat + n := by
  rw [mem_runIds']
  constructor
  · rintro ⟨j, hj, rfl⟩; rw [run_toNat id n j hj hn]; omega
  · intro ⟨h1, h2⟩
    refine ⟨x.toNat - id.toNat, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [run_toNat id n _ (by omega) hn]; omega

private theorem inRun_W64 (id : w64) (n s : Nat) (hs : s < 2 ^ 64) :
    inRun id n (W64 (s : Int)) ↔ id.toNat ≤ s ∧ s < id.toNat + n := by
  unfold inRun; rw [W64_toNat_of_lt' s hs]

private theorem freePages_lookup (fl : FLPg) (T id : w64) (n : Nat) (t : w64) (pd : Pending)
    (h : (fl.freePages T id n).pending !! t = some pd) :
    (t ≠ T ∧ fl.pending !! t = some pd) ∨
    (t = T ∧ ∃ P : Pending, (fl.pending !! T).getD ⟨[], [], 0⟩ = P ∧
      pd = ⟨P.ids ++ runIds id n, P.alloctx ++ List.replicate n ((fl.allocs !! id).getD 0),
        P.lastReleaseBegin⟩) := by
  simp only [FLPg.freePages, GMap.lookup_insert_eq_iff] at h
  split at h
  · rename_i he; cases h; exact Or.inr ⟨he.symm, _, rfl, rfl⟩
  · rename_i he; exact Or.inl ⟨fun e => he e.symm, h⟩

private theorem freePages_pending_old (fl : FLPg) (T id : w64) (n : Nat) (t : w64) (pd : Pending)
    (h : fl.pending !! t = some pd) : ∃ pd', (fl.freePages T id n).pending !! t = some pd' ∧
      ∀ x, x ∈ pd.ids → x ∈ pd'.ids := by
  by_cases ht : t = T
  · subst ht
    refine ⟨⟨pd.ids ++ runIds id n, pd.alloctx ++ List.replicate n ((fl.allocs !! id).getD 0),
      pd.lastReleaseBegin⟩, by simp [FLPg.freePages, h], fun x hx => ?_⟩
    simp only [List.mem_append]; exact Or.inl hx
  · exact ⟨pd, by simp [FLPg.freePages, Ne.symm ht, h], fun x hx => hx⟩

private theorem pendSlots_free (fl : FLPg) (T id : w64) (n : Nat) (hn : id.toNat + n < 2 ^ 64) (s : Nat) :
    s ∈ pendSlots (fl.freePages T id n) ↔
      s ∈ pendSlots fl ∨ (id.toNat ≤ s ∧ s < id.toNat + n) := by
  rw [mem_pendSlots, mem_pendSlots]
  constructor
  · rintro ⟨t, pd, x, hp, hx, rfl⟩
    rcases freePages_lookup fl T id n t pd hp with ⟨-, hp⟩ | ⟨rfl, P, hP, rfl⟩
    · exact Or.inl ⟨t, pd, x, hp, hx, rfl⟩
    · simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · left
        rcases hq : fl.pending !! t with _ | q
        · rw [hq] at hP; simp only [Option.getD_none] at hP; subst hP; simp at hx
        · rw [hq] at hP; simp only [Option.getD_some] at hP; subst hP
          exact ⟨t, q, x, hq, hx, rfl⟩
      · exact Or.inr ((mem_runIds_toNat id n hn x).1 hx)
  · rintro (⟨t, pd, x, hp, hx, rfl⟩ | ⟨h1, h2⟩)
    · obtain ⟨pd', hp', hsub⟩ := freePages_pending_old fl T id n t pd hp
      exact ⟨t, pd', x, hp', hsub x hx, rfl⟩
    · refine ⟨T, _, W64 (s : Int), GMap.lookup_insert_eq _ _ _, ?_,
        W64_toNat_of_lt' s (by omega)⟩
      simp only [List.mem_append]
      right
      rw [mem_runIds_toNat id n hn, W64_toNat_of_lt' s (by omega)]; omega

private theorem pendingIds_free_perm (fl : FLPg) (T id : w64) (n : Nat) :
    (fl.freePages T id n).pendingIds.Perm (fl.pendingIds ++ runIds id n) := by
  unfold FLPg.pendingIds
  rcases hq : fl.pending !! T with _ | q
  · have h1 := GMap.mapToList_insert fl.pending T ⟨runIds id n,
      List.replicate n ((fl.allocs !! id).getD 0), 0⟩ hq
    simp only [FLPg.freePages, hq, Option.getD_none, List.nil_append]
    refine (h1.flatMap_right _).trans ?_
    simp only [List.flatMap_cons]
    exact List.perm_append_comm
  · have h0 := GMap.mapToList_delete fl.pending T q hq
    have h1 := GMap.mapToList_insert (fl.pending.delete T) T ⟨q.ids ++ runIds id n,
      q.alloctx ++ List.replicate n ((fl.allocs !! id).getD 0), q.lastReleaseBegin⟩
      (GMap.lookup_delete _ _)
    rw [GMap.insert_delete] at h1
    simp only [FLPg.freePages, hq, Option.getD_some]
    refine (h1.flatMap_right _).trans ?_
    refine List.Perm.trans ?_ ((h0.flatMap_right _).symm.append_right _)
    simp only [List.flatMap_cons, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm

private theorem runIds_nodup (id : w64) (n : Nat) (hn : id.toNat + n < 2 ^ 64) : (runIds id n).Nodup := by
  unfold runIds List.Nodup
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := n))
  intro a b ha hb hne e
  have := congrArg BitVec.toNat e
  simp only [List.mem_range] at ha hb
  rw [run_toNat id n a ha hn, run_toNat id n b hb hn] at this; omega

private theorem flatMap_congr' {α β : Type} (l : List α) (f g : α → List β) (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

private theorem foldl_insert_lookup (L : List (w64 × w64)) :
    ∀ (m : GMap w64 w64) (k a : w64),
      (L.foldl (fun m x => m.insert x.1 x.2) m) !! k = some a →
      (∃ x ∈ L, x.1 = k ∧ x.2 = a) ∨ m !! k = some a := by
  induction L with
  | nil => intro m k a h; exact Or.inr h
  | cons x L ih =>
    intro m k a h
    simp only [List.foldl_cons] at h
    rcases ih _ k a h with ⟨y, hy, h1, h2⟩ | h'
    · exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, h1, h2⟩
    · simp only [GMap.lookup_insert_eq_iff] at h'
      split at h'
      · rename_i he; cases h'; exact Or.inl ⟨x, List.mem_cons_self, he, rfl⟩
      · exact Or.inr h'

private theorem rollback_allocs (fl : FLPg) (T k a : w64) (h : (fl.rollbackEntry T).allocs !! k = some a) :
    a ≠ T ∧ (fl.allocs !! k = some a ∨ ∃ (pd : Pending) (i : Nat), fl.pending !! T = some pd ∧
      pd.ids[i]? = some k ∧ pd.alloctx[i]? = some a) := by
  simp only [FLPg.rollbackEntry, GMap.lookup_filter, Option.filter_eq_some_iff,
    decide_eq_true_eq] at h
  obtain ⟨h, hne⟩ := h
  refine ⟨hne, ?_⟩
  rcases foldl_insert_lookup _ _ k a h with ⟨x, hx, h1, h2⟩ | h'
  · right
    simp only [List.mem_filter] at hx
    rcases hq : fl.pending !! T with _ | q
    · rw [hq] at hx; simp at hx
    · rw [hq] at hx
      obtain ⟨i, hi1, hi2⟩ := mem_zip_idx'' hx.1
      exact ⟨q, i, rfl, h1 ▸ hi1, h2 ▸ hi2⟩
  · exact Or.inl h'
where
  mem_zip_idx'' {l1 l2 : List w64} {x : w64 × w64} (h : x ∈ l1.zip l2) :
      ∃ i : Nat, l1[i]? = some x.1 ∧ l2[i]? = some x.2 := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
    rw [List.getElem?_zip_eq_some] at hi
    exact ⟨i, hi.1, hi.2⟩

private theorem rollback_pending (fl : FLPg) (T t : w64) (pd : Pending)
    (h : (fl.rollbackEntry T).pending !! t = some pd) : t ≠ T ∧ fl.pending !! t = some pd := by
  simp only [FLPg.rollbackEntry] at h
  exact ((GMap.lookup_delete_Some _ _ _ _).1 h).imp (fun h => fun e => h e.symm) id

private theorem mvccView_rollback (fl : FLPg) (v : View) (T : w64) (h : mvccView fl v) :
    mvccView (fl.rollbackEntry T) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun id pg hp a ha => ?_, fun s hs => ?_⟩
  · rcases (rollback_allocs fl T _ a ha).2 with ha | ⟨pd, i, hpd, hi1, hi2⟩
    · exact h1 id pg hp a ha
    · have := ((h2 id ⟨id, pg, hp, Nat.le_refl _, by omega⟩).2.2 T pd i hpd hi1).1
      rwa [List.getD_eq_getElem?_getD, hi2] at this
  · obtain ⟨a, b, c⟩ := h2 s hs
    exact ⟨a, b, fun t pd i hp hi => c t pd i (rollback_pending fl T t pd hp).2 hi⟩

private theorem pendSlots_rollback (fl : FLPg) (T : w64) (s : Nat) (h : s ∈ pendSlots (fl.rollbackEntry T)) :
    s ∈ pendSlots fl := by
  obtain ⟨t, pd, x, hp, hx, rfl⟩ := (mem_pendSlots _ _).1 h
  exact (mem_pendSlots _ _).2 ⟨t, pd, x, (rollback_pending fl T t pd hp).2, hx, rfl⟩

private theorem pendingIds_rollback_perm (fl : FLPg) (T : w64) :
    ∃ L, fl.pendingIds.Perm (L ++ (fl.rollbackEntry T).pendingIds) := by
  unfold FLPg.pendingIds
  rcases hq : fl.pending !! T with _ | q
  · refine ⟨[], ?_⟩
    simp only [FLPg.rollbackEntry, GMap.delete_notin _ _ hq, List.nil_append]; exact List.Perm.refl _
  · refine ⟨q.ids, ?_⟩
    have h0 := GMap.mapToList_delete fl.pending T q hq
    simp only [FLPg.rollbackEntry]
    exact (h0.flatMap_right _).trans (by simp only [List.flatMap_cons]; exact List.Perm.refl _)

private theorem cover_lt_hwm (C : CommitSt) (h2 : treeOK C) (s : Nat) (hs : coversSlot C.pages s) :
    s < C.hwm := by
  obtain ⟨id, pg, hp, h1, h2'⟩ := hs
  have := h2.2.2.2.1 id pg hp
  omega

private theorem mem_storeSlots (σ : StoreSt) (s : Nat) :
    s ∈ storeSlots σ ↔ s ∈ treeSlots σ.C ∨ s ∈ pendSlots σ.fl := by
  simp only [storeSlots, mem_list_dedup, List.mem_append]

private theorem toList_flatMap_perm {V : Type} (m : GMap w64 V) (f : V → List w64) (K : List w64)
    (hK : K.Nodup) (hdom : ∀ k, (m !! k).isSome → k ∈ K) :
    (m.toList.flatMap fun kv => f kv.2).Perm (K.flatMap fun k => ((m !! k).map f).getD []) := by
  let L := K.filterMap fun k => (m !! k).map fun v => (k, v)
  have hL : L.Perm m.toList := by
    refine (List.perm_ext_iff_of_nodup ?_ (GMap.NoDup_map_to_list m)).2 fun ⟨k, v⟩ => ?_
    · unfold List.Nodup
      rw [List.pairwise_filterMap]
      refine hK.imp fun {a a'} hne b hb b' hb' e => hne ?_
      simp only [Option.mem_def, Option.map_eq_some_iff] at hb hb'
      obtain ⟨_, -, rfl⟩ := hb; obtain ⟨_, -, rfl⟩ := hb'; exact (Prod.mk.inj e).1
    · simp only [L, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
      rw [GMap.mem_toList]
      constructor
      · rintro ⟨k', -, v', h, rfl, rfl⟩; exact h
      · intro h; exact ⟨k, hdom k (by simp [h]), v, h, rfl, rfl⟩
  refine (hL.symm.flatMap_right _).trans (List.Perm.of_eq ?_)
  simp only [L]
  clear hL hdom hK
  induction K with
  | nil => rfl
  | cons k K ih =>
    simp only [List.filterMap_cons, List.flatMap_cons]
    rcases m !! k with _ | v
    · simp only [Option.map_none, List.nil_append, Option.getD_none]; exact ih
    · simp only [Option.map_some, List.flatMap_cons, Option.getD_some]; rw [ih]

private theorem flatMap_perm_congr {α β : Type} (K : List α) (f g : α → List β)
    (h : ∀ k ∈ K, (f k).Perm (g k)) : (K.flatMap f).Perm (K.flatMap g) := by
  induction K with
  | nil => exact List.Perm.refl _
  | cons k K ih =>
    simp only [List.flatMap_cons]
    exact (h k (by simp)).append (ih fun k hk => h k (by simp [hk]))

private theorem flatMap_append_perm' {α β : Type} (K : List α) (f g : α → List β) :
    (K.flatMap fun k => f k ++ g k).Perm (K.flatMap f ++ K.flatMap g) := by
  induction K with
  | nil => exact List.Perm.refl _
  | cons k K ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine (List.Perm.append_left _ ih).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

/-! ## The release steps -/

private def relOK (Q : w64 → w64 → Prop) (fl fl' : FLPg) : Prop :=
  fl'.allocs = fl.allocs ∧
  (∀ x ∈ fl'.free, x ∈ fl.free ∨ ∃ t pd i, fl.pending !! t = some pd ∧ pd.ids[i]? = some x ∧
    Q t (pd.alloctx.getD i 0)) ∧
  (∀ t pd' i x, fl'.pending !! t = some pd' → pd'.ids[i]? = some x →
    ∃ pd j, fl.pending !! t = some pd ∧ pd.ids[j]? = some x ∧
      pd.alloctx.getD j 0 = pd'.alloctx.getD i 0) ∧
  fl'.allIds.Perm fl.allIds ∧
  (∀ t p, fl'.pending !! t = some p → p.ids.length = p.alloctx.length) ∧
  (∀ t p, fl'.pending !! t = some p → (fl.pending !! t).isSome)

private theorem relOK_refl (Q : w64 → w64 → Prop) (fl : FLPg)
    (hwf : ∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length) :
    relOK Q fl fl :=
  ⟨rfl, fun x hx => Or.inl hx, fun t pd' i x hp hi => ⟨pd', i, hp, hi, rfl⟩,
    List.Perm.refl _, hwf, fun t p hp => by simp [hp]⟩

private theorem relOK_trans (Q : w64 → w64 → Prop) (fl fl1 fl2 : FLPg) (h1 : relOK Q fl fl1)
    (h2 : relOK Q fl1 fl2) : relOK Q fl fl2 := by
  obtain ⟨a1, b1, c1, d1, -, f1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2⟩ := h2
  refine ⟨a2.trans a1, fun x hx => ?_, fun t pd' i x hp hi => ?_, d2.trans d1, e2,
    fun t p hp => ?_⟩
  · rcases b2 x hx with hx | ⟨t, pd, i, hp, hi, hq⟩
    · exact b1 x hx
    · obtain ⟨pd0, j, hp0, hj, he⟩ := c1 t pd i x hp hi
      exact Or.inr ⟨t, pd0, j, hp0, hj, he ▸ hq⟩
  · obtain ⟨pd1, j, hp1, hj, he⟩ := c2 t pd' i x hp hi
    obtain ⟨pd0, j', hp0, hj', he'⟩ := c1 t pd1 j x hp1 hj
    exact ⟨pd0, j', hp0, hj', he'.trans he⟩
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (f2 t p hp)
    exact f1 t q hq

private theorem relOK_mono (Q Q' : w64 → w64 → Prop) (hQ : ∀ t a, Q t a → Q' t a) (fl fl' : FLPg)
    (h : relOK Q fl fl') : relOK Q' fl fl' := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  refine ⟨a, fun x hx => ?_, c, d, e, f⟩
  rcases b x hx with hx | ⟨t, pd, i, hp, hi, hq⟩
  · exact Or.inl hx
  · exact Or.inr ⟨t, pd, i, hp, hi, hQ _ _ hq⟩

private theorem mem_sortPgids'' (l : List w64) (x : w64) : x ∈ sortPgids l ↔ x ∈ l :=
  (List.mergeSort_perm _ _).mem_iff

private theorem getD_of_getElem?' {l : List w64} {i : Nat} {a : w64} (h : l[i]? = some a) :
    l.getD i 0 = a := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem relOK_release (fl : FLPg) (txid : w64)
    (hwf : ∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length) :
    relOK (fun t _ => t.toNat ≤ txid.toNat) fl (fl.release txid) := by
  let K := fl.pending.domList
  have hK : K.Nodup := GMap.nodup_dom_list _
  have hdom : ∀ (m : GMap w64 Pending), (∀ k, (m !! k).isSome → (fl.pending !! k).isSome) →
      ∀ k, (m !! k).isSome → k ∈ K := fun m hm k hk => (GMap.mem_dom_list _ _).2 (hm k hk)
  refine ⟨rfl, fun x hx => ?_, fun t pd' i x hp hi => ?_, ?_, fun t p hp => ?_,
    fun t p hp => ?_⟩
  · simp only [FLPg.release] at hx
    rw [mem_sortPgids'', List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨⟨t, pd⟩, hkv, hx⟩
    · exact Or.inl hx
    · rw [GMap.mem_toList, GMap.lookup_filter, Option.filter_eq_some_iff] at hkv
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
      exact Or.inr ⟨t, pd, i, hkv.1, hi, by simpa using hkv.2⟩
  · simp only [FLPg.release, GMap.lookup_filter, Option.filter_eq_some_iff] at hp
    exact ⟨pd', i, hp.1, hi, rfl⟩
  · simp only [FLPg.allIds, FLPg.release, FLPg.pendingIds]
    refine ((List.mergeSort_perm _ _).append_right _).trans ?_
    rw [List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine ((toList_flatMap_perm _ Pending.ids K hK (hdom _ fun k h => by
        simp only [GMap.lookup_filter] at h; revert h; cases fl.pending !! k <;> simp)).append
      (toList_flatMap_perm _ Pending.ids K hK (hdom _ fun k h => by
        simp only [GMap.lookup_filter] at h; revert h; cases fl.pending !! k <;> simp))).trans ?_
    refine (flatMap_append_perm' K _ _).symm.trans ?_
    refine List.Perm.trans ?_ (toList_flatMap_perm _ Pending.ids K hK (hdom _ fun _ h => h)).symm
    refine flatMap_perm_congr K _ _ fun k _ => ?_
    simp only [GMap.lookup_filter]
    rcases fl.pending !! k with _ | pd
    · exact List.Perm.refl _
    · by_cases hk : k.toNat ≤ txid.toNat
      · have : ¬ txid.toNat < k.toNat := by omega
        simp [hk, this, Option.filter]
      · have : txid.toNat < k.toNat := by omega
        simp [hk, this, Option.filter]
  · simp only [FLPg.release, GMap.lookup_filter, Option.filter_eq_some_iff] at hp
    exact hwf t p hp.1
  · simp only [FLPg.release, GMap.lookup_filter, Option.filter_eq_some_iff] at hp
    simp [hp.1]

private theorem mem_zip_idx3 {l1 l2 : List w64} {x : w64 × w64} (h : x ∈ l1.zip l2) :
    ∃ i : Nat, l1[i]? = some x.1 ∧ l2[i]? = some x.2 := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_zip_eq_some] at hi
  exact ⟨i, hi.1, hi.2⟩

private theorem rrOne_perm (b e : w64) (pd : Pending) (hl : pd.ids.length = pd.alloctx.length) :
    pd.ids.Perm ((releaseRangeOne b e pd).1 ++ (releaseRangeOne b e pd).2.ids) := by
  have he : pd.ids = (pd.ids.zip pd.alloctx).map Prod.fst := (List.map_fst_zip (by omega)).symm
  refine (List.Perm.of_eq he).trans ?_
  simp only [releaseRangeOne]
  rw [← List.map_append]
  refine (((List.Perm.append_left _ (srLoop_perm b e _ 0 _ (Nat.le_refl _) (by simp))).trans
    (List.filter_append_perm (inRR b e) _)).map _).symm

private theorem relOK_releaseRange (fl : FLPg) (b e : w64)
    (hwf : ∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length) :
    relOK (fun t a => b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ b.toNat ≤ a.toNat ∧
      a.toNat ≤ e.toNat) fl (fl.releaseRange b e) := by
  unfold FLPg.releaseRange
  split
  · exact relOK_refl _ fl hwf
  let K := fl.pending.domList
  have hK : K.Nodup := GMap.nodup_dom_list _
  have hdom : ∀ {V : Type} (m : GMap w64 V), (∀ k, (m !! k).isSome → (fl.pending !! k).isSome) →
      ∀ k, (m !! k).isSome → k ∈ K := fun m hm k hk => (GMap.mem_dom_list _ _).2 (hm k hk)
  refine ⟨rfl, fun x hx => ?_, fun t pd' i x hp hi => ?_, ?_, fun t p hp => ?_,
    fun t p hp => ?_⟩
  · simp only at hx
    rw [mem_sortPgids'', List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨⟨t, pd⟩, hkv, hx⟩
    · exact Or.inl hx
    · rw [GMap.mem_toList, GMap.lookup_filter, Option.filter_eq_some_iff] at hkv
      obtain ⟨hkv, hsel⟩ := hkv
      simp only [releaseRangeOne, inRR, List.mem_map, List.mem_filter] at hx
      obtain ⟨⟨x', a⟩, ⟨hxz, hin⟩, rfl⟩ := hx
      obtain ⟨i, hi1, hi2⟩ := mem_zip_idx3 hxz
      refine Or.inr ⟨t, pd, i, hkv, hi1, ?_⟩
      rw [getD_of_getElem?' hi2]
      simp only [decide_eq_true_eq] at hin hsel
      exact ⟨hsel.1, hsel.2.1, hin⟩
  · simp only [GMap.lookup_union, GMap.lookup_filter, GMap.lookup_fmap] at hp
    rcases hq : fl.pending !! t with _ | pd0
    · simp [hq] at hp
    rw [hq] at hp
    by_cases hsel : (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ pd0.lastReleaseBegin ≠ b)
    · have hs' : decide (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ pd0.lastReleaseBegin ≠ b) = true :=
        decide_eq_true hsel
      simp only [Option.filter_some, hs', Bool.not_true, Option.none_or, ite_false,
        Bool.false_eq_true, Option.map_some, ite_true] at hp
      split at hp
      rotate_left
      · cases hp
      cases hp
      simp only [releaseRangeOne, List.getElem?_map, Option.map_eq_some_iff] at hi ⊢
      obtain ⟨⟨x', a⟩, hxa, rfl⟩ := hi
      have hmem := List.mem_of_getElem? hxa
      rw [mem_srLoop, List.mem_filter] at hmem
      obtain ⟨j, hj1, hj2⟩ := mem_zip_idx3 hmem.1
      refine ⟨pd0, j, rfl, hj1, ?_⟩
      rw [getD_of_getElem?' hj2]
      symm; apply getD_of_getElem?'; rw [List.getElem?_map, hxa]; rfl
    · have hs' : decide (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ pd0.lastReleaseBegin ≠ b) = false :=
        decide_eq_false hsel
      simp only [Option.filter_some, hs', Bool.not_false, ite_true, Option.some_or] at hp
      cases hp
      exact ⟨pd', i, rfl, hi, rfl⟩
  · simp only [FLPg.allIds, FLPg.pendingIds]
    refine ((List.mergeSort_perm _ _).append_right _).trans ?_
    rw [List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine ((toList_flatMap_perm _ (fun p => (releaseRangeOne b e p).1) K hK (hdom _ fun k h => by
        simp only [GMap.lookup_filter] at h; revert h; cases fl.pending !! k <;> simp)).append
      (toList_flatMap_perm _ Pending.ids K hK (hdom _ fun k h => by
        simp only [GMap.lookup_union, GMap.lookup_filter, GMap.lookup_fmap] at h; revert h
        cases fl.pending !! k <;> simp))).trans ?_
    refine (flatMap_append_perm' K _ _).symm.trans ?_
    refine List.Perm.trans ?_ (toList_flatMap_perm _ Pending.ids K hK (hdom _ fun _ h => h)).symm
    refine flatMap_perm_congr K _ _ fun k _ => ?_
    simp only [GMap.lookup_union, GMap.lookup_filter, GMap.lookup_fmap]
    rcases hq : fl.pending !! k with _ | pd
    · exact List.Perm.refl _
    · by_cases hsel : (b.toNat ≤ k.toNat ∧ k.toNat ≤ e.toNat ∧ pd.lastReleaseBegin ≠ b)
      · have hs' : decide (b.toNat ≤ k.toNat ∧ k.toNat ≤ e.toNat ∧ pd.lastReleaseBegin ≠ b) =
            true := decide_eq_true hsel
        simp only [Option.filter_some, hs', Bool.not_true, Option.none_or, ite_false,
          Bool.false_eq_true, Option.map_some, ite_true, Option.getD_some]
        refine List.Perm.trans ?_ (rrOne_perm b e pd (hwf k pd hq)).symm
        refine List.Perm.append_left _ ?_
        by_cases hne : (releaseRangeOne b e pd).2.ids = []
        · simp [hne]
        · simp [hne]
      · have hs' : decide (b.toNat ≤ k.toNat ∧ k.toNat ≤ e.toNat ∧ pd.lastReleaseBegin ≠ b) =
            false := decide_eq_false hsel
        simp only [Option.filter_some, hs', Bool.not_false, ite_true, Option.some_or,
          Option.map_none, Option.getD_none, Option.map_some, Option.getD_some, List.nil_append,
          Bool.false_eq_true, ite_false]
        exact List.Perm.refl _
  · simp only [GMap.lookup_union, GMap.lookup_filter, GMap.lookup_fmap] at hp
    rcases hq : fl.pending !! t with _ | pd0
    · simp [hq] at hp
    rw [hq] at hp
    by_cases hsel : (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ pd0.lastReleaseBegin ≠ b)
    · have hs' : decide (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ pd0.lastReleaseBegin ≠ b) = true :=
        decide_eq_true hsel
      simp only [Option.filter_some, hs', Bool.not_true, Option.none_or, ite_false,
        Bool.false_eq_true, Option.map_some, ite_true] at hp
      split at hp
      rotate_left
      · cases hp
      cases hp
      simp only [releaseRangeOne, List.length_map]
    · have hs' : decide (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ pd0.lastReleaseBegin ≠ b) = false :=
        decide_eq_false hsel
      simp only [Option.filter_some, hs', Bool.not_false, ite_true, Option.some_or] at hp
      cases hp
      exact hwf t _ hq
  · simp only [GMap.lookup_union, GMap.lookup_filter, GMap.lookup_fmap] at hp
    rcases hq : fl.pending !! t with _ | pd0
    · simp [hq] at hp
    · simp

private def relSafe (ro : List w64) (t a : w64) : Prop :=
  ∀ T ∈ ro, ¬ (a.toNat ≤ T.toNat ∧ T.toNat < t.toNat)

private theorem relOK_fold (ro : List w64) :
    ∀ (l : List w64) (fl : FLPg) (m : w64),
      (∀ T ∈ ro, T.toNat < m.toNat ∨ T ∈ l) →
      l.Pairwise (fun x y => x.toNat ≤ y.toNat) →
      (∀ x ∈ l, m.toNat ≤ x.toNat + 1) →
      (∀ x ∈ l, 1 ≤ x.toNat ∧ x.toNat + 1 < 2 ^ 64) →
      (∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length) →
      relOK (relSafe ro) fl (l.foldl (fun (acc : FLPg × w64) t =>
          (acc.1.releaseRange acc.2 (t - 1), t + 1)) (fl, m)).1 ∧
      ∀ T ∈ ro, T.toNat < (l.foldl (fun (acc : FLPg × w64) t =>
          (acc.1.releaseRange acc.2 (t - 1), t + 1)) (fl, m)).2.toNat
  | [], fl, m, hinv, _, _, _, hwf => by
    refine ⟨relOK_refl _ fl hwf, fun T hT => ?_⟩
    rcases hinv T hT with h | h
    · exact h
    · simp at h
  | t :: l, fl, m, hinv, hsort, hm, hb, hwf => by
    simp only [List.foldl_cons]
    have ht := hb t (by simp)
    have htm1 : (t - 1).toNat = t.toNat - 1 := by
      simp only [BitVec.toNat_sub]; simp; omega
    have htp1 : (t + 1).toNat = t.toNat + 1 := by
      simp only [BitVec.toNat_add]; simp; omega
    have hstep := relOK_releaseRange fl m (t - 1) hwf
    have hstep' : relOK (relSafe ro) fl (fl.releaseRange m (t - 1)) := by
      refine relOK_mono _ _ (fun t' a hq T hT => ?_) _ _ hstep
      rw [htm1] at hq
      rcases hinv T hT with h | h
      · omega
      · have : t.toNat ≤ T.toNat := by
          rcases List.mem_cons.1 h with rfl | h
          · exact Nat.le_refl _
          · exact List.rel_of_pairwise_cons hsort h
        omega
    obtain ⟨h1, h2⟩ := relOK_fold ro l (fl.releaseRange m (t - 1)) (t + 1)
      (fun T hT => by
        rcases hinv T hT with h | h
        · left; rw [htp1]; have := hm t (by simp); omega
        · rcases List.mem_cons.1 h with rfl | h
          · left; rw [htp1]; omega
          · exact Or.inr h)
      (List.pairwise_cons.1 hsort).2
      (fun x hx => by rw [htp1]; have := List.rel_of_pairwise_cons hsort hx; omega)
      (fun x hx => hb x (by simp [hx])) hstep.2.2.2.2.1
    exact ⟨relOK_trans _ _ _ _ hstep' h1, h2⟩

private theorem sortPgids_sorted (l : List w64) :
    (sortPgids l).Pairwise (fun x y => x.toNat ≤ y.toNat) := by
  have := List.pairwise_mergeSort (le := fun x y : w64 => decide (x.toNat ≤ y.toNat))
    (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) l
  exact this.imp fun h => by simpa using h

private theorem relOK_releasePending (fl : FLPg) (ro : List w64)
    (hro : ∀ t ∈ ro, 1 ≤ t.toNat ∧ t.toNat + 1 < 2 ^ 64)
    (hwf : ∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length) :
    relOK (relSafe ro) fl (fl.releasePending ro) := by
  unfold FLPg.releasePending
  simp only
  have hS := sortPgids_sorted ro
  have hmem : ∀ x, x ∈ sortPgids ro ↔ x ∈ ro := mem_sortPgids'' ro
  generalize sortPgids ro = S at hS hmem
  -- the first step: everything before the oldest reader
  have h1 : relOK (relSafe ro) fl (if 0 < ((S.head?).getD (W64 (-1))).toNat then
      fl.release ((S.head?).getD (W64 (-1)) - 1) else fl) := by
    split
    · rename_i hpos
      refine relOK_mono _ _ (fun t a hq T hT => ?_) _ _ (relOK_release fl _ hwf)
      rcases hS' : S with _ | ⟨s0, S'⟩
      · rw [hS'] at hmem; exact absurd ((hmem T).2 hT) (by simp)
      · rw [hS'] at hq hmem hS
        simp only [List.head?_cons, Option.getD_some] at hq hpos
        have hT' := (hmem T).2 hT
        have : s0.toNat ≤ T.toNat := by
          rcases List.mem_cons.1 hT' with rfl | h
          · exact Nat.le_refl _
          · exact List.rel_of_pairwise_cons hS h
        have hs01 := (hro s0 ((hmem s0).1 (by simp))).1
        have : (s0 - 1).toNat = s0.toNat - 1 := by
          simp only [BitVec.toNat_sub]; simp; omega
        omega
    · exact relOK_refl _ fl hwf
  have hwf1 := h1.2.2.2.2.1
  generalize (if 0 < ((S.head?).getD (W64 (-1))).toNat then
      fl.release ((S.head?).getD (W64 (-1)) - 1) else fl) = fl1 at h1 hwf1
  have hfold := relOK_fold ro S fl1 ((S.head?).getD (W64 (-1)))
    (fun T hT => Or.inr ((hmem T).2 hT)) hS
    (fun x hx => by
      rcases hS' : S with _ | ⟨s0, S'⟩
      · rw [hS'] at hx; simp at hx
      · rw [hS'] at hx hS
        simp only [List.head?_cons, Option.getD_some]
        rcases List.mem_cons.1 hx with rfl | h
        · omega
        · have := List.rel_of_pairwise_cons hS h; omega)
    (fun x hx => hro x ((hmem x).1 hx)) hwf1
  obtain ⟨h2, h3⟩ := hfold
  generalize (S.foldl (fun (acc : FLPg × w64) t => (acc.1.releaseRange acc.2 (t - 1), t + 1))
    (fl1, (S.head?).getD (W64 (-1)))) = res at h2 h3
  rcases res with ⟨fl2, m2⟩
  simp only at h2 h3 ⊢
  refine relOK_trans _ _ _ _ (relOK_trans _ _ _ _ h1 h2)
    (relOK_mono _ _ (fun t a hq T hT => ?_) _ _ (relOK_releaseRange fl2 m2 _ h2.2.2.2.2.1))
  have := h3 T hT
  omega

private theorem releasePending_free (fl : FLPg) (ro : List w64) :
    ∃ L, (fl.releasePending ro).free = sortPgids L := by
  unfold FLPg.releasePending
  simp only
  generalize (List.foldl _ _ _) = res
  rcases res with ⟨fl2, m2⟩
  simp only
  unfold FLPg.releaseRange
  rw [if_neg (by simp only [W64, BitVec.toNat_ofInt]; have := m2.isLt; omega)]
  exact ⟨_, rfl⟩

private theorem sortPgids_incr' (l : List w64) (hnd : (sortPgids l).Nodup) : PgidsIncr (sortPgids l) := by
  unfold PgidsIncr
  refine ((sortPgids_sorted l).and hnd).imp fun {x y} ⟨h1, h2⟩ => ?_
  have : x.toNat ≠ y.toNat := fun h => h2 (BitVec.eq_of_toNat_eq h)
  omega

/-! ## Lemma statements (U3) -/

omit [GooseExts] in
private theorem pendSlots_empty (fl : FLPg) (h : fl.pending = ∅) : pendSlots fl = [] := by
  simp [pendSlots, FLPg.pendingIds, h]

omit [GooseExts] in
private theorem W64_toNat_of_lt (s : Nat) (h : s < 2 ^ 64) : (W64 (s : Int)).toNat = s := by
  simp only [W64, BitVec.toNat_ofInt]; omega

private theorem treeSlot_lt_hwm (C : CommitSt) (h2 : treeOK C) (s : Nat) (hs : s ∈ treeSlots C) :
    s < C.hwm := by
  simp only [treeSlots, pagesSlots, List.mem_flatMap, List.mem_range'] at hs
  obtain ⟨⟨id, pg⟩, hip, j, hj, rfl⟩ := hs
  have := h2.2.2.2.1 id pg ((GMap.mem_toList _ _ _).1 hip)
  simp only at hj
  omega

private theorem storeSlot_lt (σ : StoreSt) (h : storeOK σ) (s : Nat) (hs : s ∈ storeSlots σ) :
    s < 2 ^ 64 := by
  simp only [storeSlots, mem_list_dedup, List.mem_append] at hs
  rcases hs with hs | hs
  · have := treeSlot_lt_hwm σ.C h.2.1 s hs
    have hm := h.1.2.2.2.2.2.2.1.2.2.1
    have := (metaOf (σ.C.slot σ.C.txid)).pgid'.isLt
    omega
  · simp only [pendSlots, List.mem_map] at hs
    obtain ⟨x, -, rfl⟩ := hs
    exact x.isLt

private theorem mem_pagesSlots (P : Pages) (s : Nat) : s ∈ pagesSlots P ↔ coversSlot P s := by
  simp only [pagesSlots, List.mem_flatMap, List.mem_range', coversSlot]
  constructor
  · rintro ⟨⟨id, pg⟩, hip, j, hj, rfl⟩
    exact ⟨id, pg, (GMap.mem_toList _ _ _).1 hip, by omega, by simp only at hj; omega⟩
  · rintro ⟨id, pg, hp, h1, h2⟩
    exact ⟨(id, pg), (GMap.mem_toList _ _ _).2 hp, s - id, by simp only; omega, by omega⟩

private theorem tree_in_store (σ : StoreSt) (s : Nat) (h : coversSlot σ.C.pages s) :
    s ∈ storeSlots σ := by
  simp only [storeSlots, mem_list_dedup, List.mem_append]
  exact Or.inl ((mem_pagesSlots _ _).2 h)

omit [GooseExts] in
private theorem mem_sortPgids (l : List w64) (x : w64) : x ∈ sortPgids l ↔ x ∈ l :=
  (List.mergeSort_perm _ _).mem_iff

omit [GooseExts] in
private theorem nodup_len_le (l : List w64) (B : Nat) (hnd : l.Nodup) (hb : ∀ x ∈ l, x.toNat < B) :
    l.length ≤ B := by
  have h1 : (l.map BitVec.toNat).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact hnd.imp (fun {a b} hne e => hne (BitVec.eq_of_toNat_eq e))
  have h2 : l.map BitVec.toNat ⊆ List.range B := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact List.mem_range.2 (hb x hx)
  have := h1.length_le_of_subset h2
  simpa using this

omit [GooseExts] in
private theorem sortPgids_incr (l : List w64) (hnd : l.Nodup) : PgidsIncr (sortPgids l) := by
  have hs : (sortPgids l).Pairwise (fun x y => decide (x.toNat ≤ y.toNat)) :=
    List.pairwise_mergeSort (fun a b c h1 h2 => by simp at *; omega)
      (fun a b => by simp; omega) l
  have hn : (sortPgids l).Nodup := (List.mergeSort_perm _ _).nodup_iff.2 hnd
  unfold PgidsIncr
  refine (hs.and hn).imp fun {x y} ⟨h1, h2⟩ => ?_
  simp only [decide_eq_true_eq] at h1
  have : x.toNat ≠ y.toNat := fun h => h2 (BitVec.eq_of_toNat_eq h)
  omega


open Classical in
private theorem lent_fold_le (s : Nat) (l : List (Nat × RdInfo)) (q : Qp)
    (h : l.foldr (fun kv acc => if coversSlot kv.2.v.pages s then optAdd rq acc else acc) none
      = some q) : q.val ≤ (l.length : Rat) * rq.val := by
  induction l generalizing q with
  | nil => simp at h
  | cons kv l ih =>
    simp only [List.foldr_cons] at h
    have hq := rq.2
    split at h
    · revert h
      generalize hf : List.foldr _ none l = r
      intro h
      cases r with
      | none =>
        simp only [optAdd, Option.some.injEq] at h; subst h
        simp only [List.length_cons]; push_cast
        have : (0 : Rat) ≤ (l.length : Rat) * rq.val :=
          Rat.mul_nonneg (by exact_mod_cast Nat.zero_le _) (by grind)
        grind
      | some b =>
        simp only [optAdd, Option.some.injEq] at h; subst h
        have := ih b hf
        simp only [List.length_cons, Qp.val_add]; push_cast
        grind
    · have := ih q h
      simp only [List.length_cons]; push_cast
      grind

omit [GooseExts] in
private theorem rq_val : rq.val = 1 / (4 * ((sync.rwmutex.actualMaxReaders + 1 : Int) : Rat)) := by
  simp only [rq, Qp.val_half, sync.rfrac_unseal, sync.rfracDef, Qp.val_div, Qp.val_one]
  rw [sync.posToQpZ_val _ (by have := sync.actualMaxReaders_pos; omega)]
  grind


/-- What is lent of a slot is below the half (`|R| · rfrac ≤ 1`, by the readers' `mtok`
deposits). Used by U3 (every borrow). -/
theorem lent_lt_half (σ : StoreSt) (hR : σ.R.size ≤ Int.toNat sync.rwmutex.actualMaxReaders)
    (s : Nat) (q : Qp) (h : lent σ s = some q) : q < (1 : Qp).half := by
  classical
  have hM := sync.actualMaxReaders_pos
  have hrq := rq_val
  have hwq : wq.val = 1 / 8 := by
    simp only [wq, Qp.val_half, Qp.val_one]; grind
  -- the readers' part
  have hr : ∀ q', GMap.mapFold (fun _ (ri : RdInfo) acc =>
      if coversSlot ri.v.pages s then optAdd rq acc else acc) none σ.R = some q' →
      q'.val < 1 / 4 := by
    intro q' hq'
    have := lent_fold_le s σ.R.toList q' hq'
    have hsz : (σ.R.toList.length : Rat) ≤ ((sync.rwmutex.actualMaxReaders : Int) : Rat) := by
      have : σ.R.toList.length ≤ Int.toNat sync.rwmutex.actualMaxReaders := hR
      have : (σ.R.toList.length : Int) ≤ sync.rwmutex.actualMaxReaders := by omega
      exact_mod_cast this
    have hx : rq.val * (4 * ((sync.rwmutex.actualMaxReaders : Int) : Rat) + 4) = 1 := by
      rw [hrq]
      have : (4 * ((sync.rwmutex.actualMaxReaders : Int) : Rat) + 4) =
          4 * ((sync.rwmutex.actualMaxReaders + 1 : Int) : Rat) := by push_cast; grind
      rw [this]; apply Rat.div_mul_cancel
      have : (0 : Rat) < ((sync.rwmutex.actualMaxReaders + 1 : Int) : Rat) := by
        exact_mod_cast (by omega : (0 : Int) < sync.rwmutex.actualMaxReaders + 1)
      grind
    have hmul := Rat.mul_le_mul_of_nonneg_right hsz (Rat.le_of_lt rq.2)
    have := rq.2
    grind
  have hrq4 : rq.val < 1 / 4 := by
    simp only [rq, Qp.val_half]
    have h1 : sync.rfrac.val ≤ 1 / 2 := by
      rw [sync.rfrac_unseal, sync.rfracDef, Qp.val_div, Qp.val_one,
        sync.posToQpZ_val _ (by omega)]
      have h2 : (2 : Rat) ≤ ((sync.rwmutex.actualMaxReaders + 1 : Int) : Rat) := by
        exact_mod_cast (by omega : (2 : Int) ≤ sync.rwmutex.actualMaxReaders + 1)
      generalize ((sync.rwmutex.actualMaxReaders + 1 : Int) : Rat) = M at h2
      have : 1 / M * M = 1 := Rat.div_mul_cancel (by grind)
      have hp : (0 : Rat) ≤ 1 / M := Rat.le_of_lt (by
        rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.2 (by grind))
      have := Rat.mul_le_mul_of_nonneg_left h2 hp
      grind
    grind
  rw [Qp.lt_iff, Qp.val_half, Qp.val_one]
  unfold lent at h
  revert h
  generalize hf : GMap.mapFold _ none σ.R = r
  intro h
  have hqpos := q.2
  split at h
  · split at h
    · cases r with
      | none =>
        simp only [optAdd, Option.some.injEq] at h; subst h; rw [hwq]
        show (1 : Rat) / 8 < 1 / 2; grind
      | some b =>
        simp only [optAdd, Option.some.injEq] at h; subst h
        have := hr b hf; simp only [Qp.val_add]; rw [hwq]; grind
    · subst h; have := hr q hf; grind
  · subst h; have := hr q hf; grind

theorem storeOK_register (σ : StoreSt) (k : Nat) (r : RdInfo) (b : Loc) (l : Nat)
    (h : storeOK σ) (hms : σ.ms = some (b, l)) (hk : σ.R !! k = none)
    (hv : r.v = View.ofC b σ.C) : storeOK (σ.register k r) := by
  have hlt := treeSlot_lt64 σ h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  have hlook : ∀ k' r', (σ.register k r).R !! k' = some r' → (k' = k ∧ r' = r) ∨
      (k' ≠ k ∧ σ.R !! k' = some r') := by
    intro k' r' h'
    simp only [StoreSt.register, GMap.lookup_insert_eq_iff] at h'
    split at h'
    · rename_i he; cases h'; exact Or.inl ⟨he.symm, rfl⟩
    · rename_i he; exact Or.inr ⟨fun e => he e.symm, h'⟩
  refine ⟨h1, h2, h3, h4, h5, h6, fun k' r' hr => ?_, h8, h9, fun k' r' hr => ?_, h11, h12, h13,
    fun hm => (by simp [StoreSt.register, hms] at hm), h15, h16, h17, h18, h19,
    fun hp s hs ht hpo k' r' hr => ?_, h21⟩
  · rcases hlook k' r' hr with ⟨-, rfl⟩ | ⟨-, hr⟩
    · simp only [StoreSt.rOK, hv]
      refine ⟨Nat.le_refl _, h18 b, fun s hs => tree_in_store' σ s hs, ⟨σ.C, h2, rfl⟩, h9,
        fun b' l' hb => ?_⟩
      simp only [StoreSt.register, hms, Option.some.injEq, Prod.mk.injEq] at hb
      exact hb.1
    · exact h7 k' r' hr
  · rcases hlook k' r' hr with ⟨-, rfl⟩ | ⟨-, hr⟩
    · simp only [hv]
      exact ⟨pagesAgree_refl _ h2.2.2.1, fun v hv' => pagesAgree_symm _ _ (h11 v hv')⟩
    · exact h10 k' r' hr
  · rcases hlook k' r' hr with ⟨-, rfl⟩ | ⟨-, hr⟩
    · simp only [hv]; intro hc; exact ht ((mem_pagesSlots' _ _).2 hc)
    · exact h20 hp s hs ht hpo k' r' hr

theorem storeOK_deregister (σ : StoreSt) (k : Nat) (h : storeOK σ) :
    storeOK (σ.deregister k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun k' r hr => h7 k' r ?_, h8, h9,
    fun k' r hr => h10 k' r ?_, h11, h12, h13, fun hms => ⟨?_, (h14 hms).2⟩, h15, h16, h17, h18,
    h19, fun hp s hs ht hpo k' r hr => h20 hp s hs ht hpo k' r ?_, h21⟩
  · exact ((GMap.lookup_delete_Some _ _ _ _).1 hr).2
  · exact ((GMap.lookup_delete_Some _ _ _ _).1 hr).2
  · simp only [StoreSt.deregister, (h14 hms).1]; exact GMap.delete_empty k
  · exact ((GMap.lookup_delete_Some _ _ _ _).1 hr).2

theorem storeOK_wbegin (σ : StoreSt) (v : View) (b : Loc) (l : Nat) (h : storeOK σ)
    (hms : σ.ms = some (b, l)) (hw : σ.wtx = none) (hwv : σ.wv = none)
    (hv : v = View.ofC b σ.C) : storeOK (σ.wbegin v) := by
  have hlt := treeSlot_lt64 σ h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  subst hv
  have hpt : ∀ t pd, σ.fl.pending !! t = some pd → t.toNat ≤ σ.C.txid := by
    intro t pd hp
    rcases h3.2.2.1 t pd hp with h' | ⟨h', -⟩
    · exact h'
    · rw [hw] at h'; cases h'
  have hsm : σ.C.txid + 1 < 2 ^ 64 := h3.2.2.2.1
  refine ⟨h1, h2, ⟨h3.1, h3.2.1, fun t pd hp => Or.inl (hpt t pd hp), h3.2.2.2⟩, h4,
    fun w hw' => ?_, fun h' => (by simp [StoreSt.wbegin] at h'), h7, fun v' hv' => ?_, h9,
    fun k r hr => ⟨(h10 k r hr).1, fun v' hv' => ?_⟩, fun v' hv' => ?_, h12, h13,
    fun hm => (by simp [StoreSt.wbegin, hms] at hm), fun h' => (by simp [StoreSt.wbegin] at h'),
    fun h' => (by simp [StoreSt.wbegin] at h'), fun s hs => ?_, h18, h19,
    fun _ s hs ht hpo k r hr => ?_, h21⟩
  · simp only [StoreSt.wbegin, Option.some.injEq, Bool.false_eq_true, ite_false] at hw' ⊢
    omega
  · simp only [StoreSt.wbegin, Option.some.injEq] at hv'; subst hv'
    refine ⟨rfl, h18 b, fun s hs => tree_in_store' σ s hs, ⟨σ.C, h2, rfl⟩, h9,
      fun _ => ⟨rfl, rfl⟩, fun _ b' l' hb => ?_⟩
    simp only [StoreSt.wbegin, hms, Option.some.injEq, Prod.mk.injEq] at hb
    exact hb.1
  · simp only [StoreSt.wbegin, Option.some.injEq] at hv'; subst hv'
    exact (h10 k r hr).1
  · simp only [StoreSt.wbegin, Option.some.injEq] at hv'; subst hv'
    exact pagesAgree_refl _ h2.2.2.1
  · rcases h17 s hs with h' | h'
    · exact Or.inl h'
    · rw [hw] at h'
      exact Or.inl (not_pend_of_only_none _ s
        (hlt s ((mem_pagesSlots' _ _).1 hs)) h')
  · exfalso
    obtain ⟨t, pd, x, hp, hx, rfl⟩ := (mem_pendSlots _ _).1 hs
    have e := hpo t pd hp (by rw [W64_toNat_eq]; exact hx)
    simp only [StoreSt.wbegin, Option.some.injEq] at e
    have := hpt t pd hp
    omega

theorem storeOK_wreturn (σ : StoreSt) (h : storeOK σ) : storeOK σ.wreturn := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun v hv => ?_, h9, h10, h11, h12, h13,
    fun hms => ⟨(h14 hms).1, rfl⟩, fun _ => rfl, h16, h17⟩
  obtain ⟨a, b, c, d, e, f, -⟩ := h8 v hv
  exact ⟨a, b, c, d, e, f, fun h => by simp [StoreSt.wreturn] at h⟩

/-- Re-borrowing the parked view at a remap, on the new mapping's base. -/
theorem storeOK_wborrow (σ : StoreSt) (b : Loc) (l : Nat) (h : storeOK σ)
    (hwl : σ.wlent = false) (hms : σ.ms = some (b, l)) (hwv : σ.wv ≠ none) :
    storeOK (σ.wborrow b) := by
  obtain ⟨v, hwv⟩ : ∃ v, σ.wv = some v := Option.ne_none_iff_exists'.1 hwv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  have hw' : (σ.wborrow b).wv = some { v with base := b } := by
    simp [StoreSt.wborrow, hwv]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun v' hv' => ?_, h9, fun k r hr => ⟨(h10 k r hr).1,
      fun v' hv' => ?_⟩, fun v' hv' => ?_, h12, h13, fun hm => ?_, fun hm => ?_,
    fun hw => ?_, h17, h18, h19, h20, h21⟩
  · rw [hw'] at hv'; cases hv'
    obtain ⟨a, b1, c, ⟨C, hC, hv⟩, e, f, -⟩ := h8 v hwv
    refine ⟨a, b1, c, ⟨C, hC, ?_⟩, e, f, fun _ b' l' hb => ?_⟩
    · rw [← hv]; rfl
    · simp only [StoreSt.wborrow, hms, Option.some.injEq, Prod.mk.injEq] at hb
      exact hb.1
  · rw [hw'] at hv'; cases hv'; exact (h10 k r hr).2 v hwv
  · rw [hw'] at hv'; cases hv'; exact h11 v hwv
  · simp [StoreSt.wborrow, hms] at hm
  · rw [hw'] at hm; cases hm
  · rw [h16 hw] at hwv; cases hwv

/-- The writer's `close`: published, or with nothing pending for it (rolled back). -/
theorem storeOK_wclose (σ : StoreSt) (h : storeOK σ)
    (hp : σ.pub = true ∨ ∀ w, σ.wtx = some w → σ.fl.pending !! W64 (w : Int) = none) :
    storeOK σ.wclose := by
  have hlt := treeSlot_lt64 σ h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  have hsm : σ.C.txid + 1 < 2 ^ 64 := h3.2.2.2.1
  -- every pending entry is a committed transaction's
  have hpt : ∀ t pd, σ.fl.pending !! t = some pd → t.toNat ≤ σ.C.txid := by
    intro t pd hpd
    rcases h3.2.2.1 t pd hpd with h' | ⟨h', -⟩
    · exact h'
    · rcases hp with hp | hp
      · have := h5 _ h'; simp only [hp, ite_true, Nat.add_zero] at this; omega
      · have := hp _ h'
        rw [W64_toNat_eq] at this; rw [this] at hpd; cases hpd
  have hnp : ∀ s, s ∈ treeSlots σ.C → s ∉ pendSlots σ.fl := by
    intro s hs hm
    obtain ⟨t, pd, x, hpd, hx, rfl⟩ := (mem_pendSlots _ _).1 hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
    have := ((h18 default).2 x.toNat ((mem_pagesSlots' _ _).1 hs)).2.2 t pd i hpd
      (by rw [W64_toNat_eq]; exact hi)
    have := hpt t pd hpd
    simp only [View.ofC] at *
    omega
  refine ⟨h1, h2, ⟨h3.1, h3.2.1, fun t pd hpd => Or.inl (hpt t pd hpd), h3.2.2.2⟩, h4,
    fun w hw => (by simp [StoreSt.wclose] at hw), fun _ => rfl, h7,
    fun v hv => (by simp [StoreSt.wclose] at hv), h9,
    fun k r hr => ⟨(h10 k r hr).1, fun v hv => (by simp [StoreSt.wclose] at hv)⟩,
    fun v hv => (by simp [StoreSt.wclose] at hv), h12, h13,
    fun hm => ⟨(h14 hm).1, rfl⟩, fun _ => rfl, fun _ => rfl,
    fun s hs => Or.inl (hnp s hs), h18, h19, fun _ s hs _ hpo => ?_, h21⟩
  exfalso
  obtain ⟨t, pd, x, hpd, hx, rfl⟩ := (mem_pendSlots _ _).1 hs
  have := hpo t pd hpd (by rw [W64_toNat_eq]; exact hx)
  simp [StoreSt.wclose] at this

/-- `Free` by the live writer `w` (before its publish) of a page of the current tree, or of the
old synced freelist page (whose bytes `pg` then enter the store). -/
theorem storeOK_free (σ : StoreSt) (w : Nat) (id : w64) (n : Nat) (pg : Nat → List w8)
    (h : storeOK σ) (hw : σ.wtx = some w) (hpub : σ.pub = false)
    (hcan : σ.fl.canFree (W64 (w : Int)) id n)
    (hpage : ((∃ p, σ.C.pages !! id.toNat = some p ∧ 1 + pageOverflow p = n) ∧
        ∀ j < n, pg (id.toNat + j) = σ.bytes (id.toNat + j)) ∨
      (σ.C.flpg = some id.toNat ∧ ∀ j < n, ¬ coversSlot σ.C.pages (id.toNat + j) ∧
        (pg (id.toNat + j)).length = 4096 ∧
        ∀ b l, σ.ms = some (b, l) → id.toNat + j < l / 4096) ∧ id.toNat + n ≤ σ.C.hwm) :
    storeOK (σ.free (W64 (w : Int)) id n pg) := by
  have hslt : ∀ s, s ∈ storeSlots σ → s < 2 ^ 64 := by
    intro s hs
    simp only [storeSlots, mem_list_dedup, List.mem_append] at hs
    rcases hs with hs | hs
    · exact treeSlot_lt64 σ h s ((mem_pagesSlots' _ _).1 hs)
    · obtain ⟨t, pd, x, -, -, rfl⟩ := (mem_pendSlots _ _).1 hs; exact x.isLt
  have htlt := treeSlot_lt64 σ h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  have hsm : σ.C.txid + 1 < 2 ^ 64 := h3.2.2.2.1
  have hww : w = σ.C.txid + 1 := by have := h5 w hw; simp [hpub] at this; omega
  have hT : (W64 (w : Int)).toNat = w := W64_toNat_of_lt' w (by omega)
  obtain ⟨hc2, hcn, hcfresh, hcal, hclen⟩ := hcan
  generalize W64 (w : Int) = T at hT hcfresh hcal hclen ⊢
  -- the run is below the high-water mark, hence `2 ^ 62`
  have hrun_hwm : id.toNat + n ≤ σ.C.hwm := by
    rcases hpage with ⟨⟨p, hp, hpn⟩, -⟩ | ⟨-, hb⟩
    · have := h2.2.2.2.1 id.toNat p hp; omega
    · exact hb
  -- the run's slots are not store slots before, in the freelist-page case
  have hrun_new : (σ.C.flpg = some id.toNat ∧ ∀ j < n, ¬ coversSlot σ.C.pages (id.toNat + j) ∧
      (pg (id.toNat + j)).length = 4096 ∧ ∀ b l, σ.ms = some (b, l) → id.toNat + j < l / 4096) →
      ∀ s, id.toNat ≤ s → s < id.toNat + n → s ∉ storeSlots σ := by
    intro ⟨_, hb⟩ s hs1 hs2 hs
    simp only [storeSlots, mem_list_dedup, List.mem_append] at hs
    rcases hs with hs | hs
    · exact (hb (s - id.toNat) (by omega)).1 (by
        rw [show id.toNat + (s - id.toNat) = s by omega]; exact (mem_pagesSlots' _ _).1 hs)
    · obtain ⟨t, pd, x, hp, hx, hxs⟩ := (mem_pendSlots _ _).1 hs
      apply hcfresh x ((mem_runIds_toNat id n hcn x).2 (by omega))
      simp only [FLPg.allIds, FLPg.pendingIds, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩
  -- the run, in the tree case, is the page's slots
  have hrun_tree : ((∃ p, σ.C.pages !! id.toNat = some p ∧ 1 + pageOverflow p = n) ∧
      ∀ j < n, pg (id.toNat + j) = σ.bytes (id.toNat + j)) →
      ∀ s, id.toNat ≤ s → s < id.toNat + n → coversSlot σ.C.pages s := by
    intro ⟨⟨p, hp, hpn⟩, _⟩ s hs1 hs2
    exact ⟨id.toNat, p, hp, hs1, by omega⟩
  -- the bytes: unchanged on every store slot, the freed page's in the freelist-page case
  have hbytes : ∀ s, s < 2 ^ 64 → (σ.free T id n pg).bytes s =
      if id.toNat ≤ s ∧ s < id.toNat + n then pg s else σ.bytes s := by
    intro s hs
    simp only [StoreSt.free]
    by_cases hr : id.toNat ≤ s ∧ s < id.toNat + n
    · rw [if_pos ((inRun_W64 id n s hs).2 hr), if_pos hr]
    · rw [if_neg (fun h' => hr ((inRun_W64 id n s hs).1 h')), if_neg hr]
  have hbytes_store : ∀ s, s ∈ storeSlots σ → (σ.free T id n pg).bytes s = σ.bytes s := by
    intro s hs
    rw [hbytes s (hslt s hs)]
    split
    · rename_i hr
      rcases hpage with ⟨hA, hpgb⟩ | hB
      · have := hpgb (s - id.toNat) (by omega)
        rwa [show id.toNat + (s - id.toNat) = s by omega] at this
      · exact absurd hs (hrun_new hB.1 s hr.1 hr.2)
    · rfl
  -- store slots grow by the run
  have hstore : ∀ s, s ∈ storeSlots (σ.free T id n pg) ↔
      s ∈ storeSlots σ ∨ (id.toNat ≤ s ∧ s < id.toNat + n) := by
    intro s
    simp only [storeSlots, mem_list_dedup, List.mem_append, StoreSt.free]
    rw [pendSlots_free σ.fl T id n hcn s]
    constructor
    · rintro (h' | h' | h')
      · exact Or.inl (Or.inl h')
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
    · rintro ((h' | h') | h')
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  have hpagesFrom : ∀ P : Pages, (∀ s, coversSlot P s → s ∈ storeSlots σ) →
      pagesFromBytes σ.bytes P → pagesFromBytes (σ.free T id n pg).bytes P := by
    intro P hin hP id' pg' hp'
    refine (hP id' pg' hp').trans ?_
    refine flatMap_congr' _ _ _ fun s hs => (hbytes_store s (hin s ?_)).symm
    simp only [List.mem_range'] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    exact ⟨id', pg', hp', by omega, by omega⟩
  -- the MVCC rule of a view in the store, older than the writer
  have hmv : ∀ v : View, mvccView σ.fl v → viewInStore σ v → v.txid < w →
      pagesAgree σ.C.pages v.pages → mvccView (σ.fl.freePages T id n) v := by
    intro v hv hin hvt hag
    refine mvccView_free σ.fl v T id n hv (by omega) ⟨hc2, hcn, hcfresh, hcal, hclen⟩ ?_
      (fun s hs => hslt s (hin s hs)) h4.2.2.2.2
    rcases hpage with hA | hB
    · by_cases hc : ∃ j < n, coversSlot v.pages (id.toNat + j)
      · left
        obtain ⟨j, hj, q, qp, hq, hq1, hq2⟩ := hc
        obtain ⟨⟨p, hp, hpn⟩, -⟩ := hA
        obtain ⟨e1, e2⟩ := hag id.toNat p q qp (id.toNat + j) hp hq (by omega) (by omega) hq1 hq2
        subst e1 e2
        exact ⟨p, hq, hpn⟩
      · right; intro j hj hc'; exact hc ⟨j, hj, hc'⟩
    · right
      intro j hj hc'
      exact hrun_new hB.1 (id.toNat + j) (by omega) (by omega) (hin _ hc')
  refine ⟨h1, h2, ?_, ?_, h5, h6, fun k r hr => ?_, fun v hv => ?_, hpagesFrom _
      (fun s hs => tree_in_store' σ s hs) h9, h10, h11, fun s hs => ?_, fun b l hb s hs => ?_,
    h14, h15, h16, fun s hs => ?_, fun b => ?_, fun x a hx => ?_, fun _ s hs ht hpo k r hr => ?_,
    h21⟩
  · -- flBelow
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h3
    refine ⟨b1, fun t pd x hp hx hle => ?_, fun t pd hp => ?_, b4, b5, fun x hx => ?_⟩
    · rcases freePages_lookup σ.fl T id n t pd hp with ⟨-, hp⟩ | ⟨rfl, -⟩
      · exact b2 t pd x hp hx hle
      · simp only [StoreSt.free] at hle; rw [hT] at hle; omega
    · rcases freePages_lookup σ.fl T id n t pd hp with ⟨-, hp⟩ | ⟨rfl, P, hP, rfl⟩
      · rcases b3 t pd hp with h' | ⟨h', h''⟩
        · exact Or.inl h'
        · exact Or.inr ⟨h', h''⟩
      · right
        refine ⟨by simp only [StoreSt.free]; rw [hT]; exact hw, fun a ha => ?_⟩
        simp only [List.mem_append, List.mem_replicate] at ha
        rcases ha with ha | ⟨-, rfl⟩
        · rcases hq : σ.fl.pending !! t with _ | q
          · rw [hq] at hP; simp only [Option.getD_none] at hP; subst hP; simp at ha
          · rw [hq] at hP; simp only [Option.getD_some] at hP; subst hP
            rcases b3 t q hq with h' | ⟨-, h''⟩
            · rw [hT] at h'; omega
            · exact h'' a ha
        · rcases hal : σ.fl.allocs !! id with _ | a
          · simp only [Option.getD_none]; rw [hT]; simp; omega
          · simp only [hal, Option.getD_some] at hcal ⊢
            have := h19 id a hal
            have hne : a.toNat ≠ w := fun e => hcal (BitVec.eq_of_toNat_eq (by rw [e, hT]))
            rw [hT]; omega
    · have hx' := (pendingIds_free_perm σ.fl T id n).subset hx
      simp only [List.mem_append] at hx'
      rcases hx' with hx' | hx'
      · exact b6 x hx'
      · have := (mem_runIds_toNat id n hcn x).1 hx'; omega
  · -- WF
    obtain ⟨w1, w2, w3, w4, w5⟩ := h4
    have hperm : (σ.fl.freePages T id n).allIds.Perm (σ.fl.allIds ++ runIds id n) := by
      simp only [FLPg.allIds]
      rw [List.append_assoc]
      exact (pendingIds_free_perm σ.fl T id n).append_left _
    refine ⟨hperm.nodup_iff.2 (List.nodup_append.2 ⟨w1, runIds_nodup id n hcn,
        fun a ha b hb e => hcfresh b hb (e ▸ ha)⟩),
      fun x hx => ?_, w3, ?_, fun t p hp => ?_⟩
    · rcases List.mem_append.1 (hperm.subset hx) with hx | hx
      · exact w2 x hx
      · have := (mem_runIds_toNat id n hcn x).1 hx; omega
    · simp only [StoreSt.free]; rw [hperm.length_eq, List.length_append]
      simp only [runIds, List.length_map, List.length_range]; omega
    · rcases freePages_lookup σ.fl T id n t p hp with ⟨-, hp⟩ | ⟨rfl, P, hP, rfl⟩
      · exact w5 t p hp
      · simp only [List.length_append, List.length_replicate, runIds, List.length_map,
          List.length_range]
        rcases hq : σ.fl.pending !! t with _ | q
        · rw [hq] at hP; simp only [Option.getD_none] at hP; subst hP; rfl
        · rw [hq] at hP; simp only [Option.getD_some] at hP; subst hP; rw [w5 t q hq]
  · -- readers
    obtain ⟨a, b, c, d, e, f⟩ := h7 k r hr
    refine ⟨a, hmv r.v b c (by omega) (h10 k r hr).1, fun s hs => (hstore s).2 (Or.inl (c s hs)),
      d, hpagesFrom _ c e, f⟩
  · -- the writer's view
    obtain ⟨a, b, c, d, e, f, g⟩ := h8 v hv
    have hvt : v.txid + 1 = w := by rw [hw] at a; cases a; rfl
    refine ⟨a, hmv v b c (by omega) (h11 v hv), fun s hs => (hstore s).2 (Or.inl (c s hs)), d,
      hpagesFrom _ c e, f, g⟩
  · -- slots and their bytes
    rcases (hstore s).1 hs with hs | hr
    · rw [hbytes_store s hs]; exact h12 s hs
    · refine ⟨by omega, ?_⟩
      rw [hbytes s (by omega), if_pos hr]
      rcases hpage with hA | hB
      · have hc := hrun_tree hA s hr.1 hr.2
        have := h12 s (tree_in_store' σ s hc)
        obtain ⟨-, hpgb⟩ := hA
        rw [show s = id.toNat + (s - id.toNat) by omega, hpgb _ (by omega),
          show id.toNat + (s - id.toNat) = s by omega]
        exact this.2
      · have := (hB.1.2 (s - id.toNat) (by omega)).2.1
        rwa [show id.toNat + (s - id.toNat) = s by omega] at this
  · rcases (hstore s).1 hs with hs | hr
    · exact h13 b l hb s hs
    · rcases hpage with hA | hB
      · exact h13 b l hb s (tree_in_store' σ s (hrun_tree hA s hr.1 hr.2))
      · have := (hB.1.2 (s - id.toNat) (by omega)).2.2 b l hb
        rwa [show id.toNat + (s - id.toNat) = s by omega] at this
  · -- tree slots pending only for the writer
    by_cases hp : s ∈ pendSlots σ.fl
    · right
      intro t pd hp' hx
      rcases freePages_lookup σ.fl T id n t pd hp' with ⟨-, hp'⟩ | ⟨rfl, -⟩
      · rcases h17 s hs with h' | h'
        · exact absurd hp h'
        · exact h' t pd hp' hx
      · rw [hT]; exact hw
    · by_cases hr : id.toNat ≤ s ∧ s < id.toNat + n
      · right
        intro t pd hp' hx
        rcases freePages_lookup σ.fl T id n t pd hp' with ⟨-, hp'⟩ | ⟨rfl, -⟩
        · exact absurd ((mem_pendSlots _ _).2 ⟨t, pd, _, hp', hx,
            W64_toNat_of_lt' s (htlt s ((mem_pagesSlots' _ _).1 hs))⟩) hp
        · rw [hT]; exact hw
      · left
        simp only [StoreSt.free]
        rw [pendSlots_free σ.fl T id n hcn s]
        rintro (h' | h') <;> contradiction
  · -- the current tree's MVCC rule
    exact hmv _ (h18 b) (fun s hs => tree_in_store' σ s hs) (by simp [View.ofC]; omega)
      (pagesAgree_refl _ h2.2.2.1)
  · simp only [StoreSt.free, FLPg.freePages, GMap.lookup_delete_iff] at hx
    split at hx
    · cases hx
    · exact h19 x a hx
  · -- the writer-only pending slots
    simp only [StoreSt.free] at hs
    rw [pendSlots_free σ.fl T id n hcn s] at hs
    rcases hs with hs | hrn
    · refine h20 hpub s hs ht (fun t pd hp hx => ?_) k r hr
      obtain ⟨pd', hp', hsub⟩ := freePages_pending_old σ.fl T id n t pd hp
      exact hpo t pd' hp' (hsub _ hx)
    · rcases hpage with hA | hB
      · exact absurd ((mem_pagesSlots' _ _).2 (hrun_tree hA s hrn.1 hrn.2)) ht
      · intro hc
        exact hrun_new hB.1 s hrn.1 hrn.2 ((h7 k r hr).2.2.1 s hc)

/-- `Allocate` by the live writer of free ids. -/
theorem storeOK_alloc (σ : StoreSt) (w : Nat) (r : w64) (n : Nat) (h : storeOK σ)
    (hw : σ.wtx = some w) (ha : σ.fl.canAlloc r n) (hn : 0 < n) :
    storeOK (σ.alloc (W64 (w : Int)) r n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  have hsm : σ.C.txid + 1 < 2 ^ 64 := h3.2.2.2.1
  have hww := h5 w hw
  have hfree : ∀ x, x ∈ (σ.fl.alloc (W64 (w : Int)) r n).free → x ∈ σ.fl.free := by
    intro x hx; simp only [FLPg.alloc, List.mem_filter] at hx; exact hx.1
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := h3
  obtain ⟨w1, w2, w3, w4, w5⟩ := h4
  have hsub : ((σ.fl.alloc (W64 (w : Int)) r n).allIds).Sublist σ.fl.allIds := by
    simp only [FLPg.allIds, FLPg.alloc, FLPg.pendingIds]
    exact List.Sublist.append List.filter_sublist (List.Sublist.refl _)
  refine ⟨h1, h2, ⟨fun x hx => hb1 x (hfree x hx), hb2, hb3, hb4,
      fun x hx => hb5 x (hfree x hx), hb6⟩,
    ⟨w1.sublist hsub, fun x hx => w2 x (hsub.subset hx), ?_, ?_, w5⟩, h5, h6,
    fun k r' hr => ?_, fun v hv => ?_, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    fun b => mvccView_alloc _ _ _ _ _ (h18 b) ha hn, fun x a hx => ?_, h20, h21⟩
  · simp only [PgidsIncr, FLPg.alloc]; exact w3.filter _
  · have := hsub.length_le; simp only [StoreSt.alloc]; omega
  · obtain ⟨a, b, c, d, e, f⟩ := h7 k r' hr
    exact ⟨a, mvccView_alloc _ _ _ _ _ b ha hn, c, d, e, f⟩
  · obtain ⟨a, b, c, d, e, f, g⟩ := h8 v hv
    exact ⟨a, mvccView_alloc _ _ _ _ _ b ha hn, c, d, e, f, g⟩
  · simp only [StoreSt.alloc, FLPg.alloc, GMap.lookup_insert_eq_iff] at hx
    split at hx
    · cases hx
      show _ ≤ σ.C.txid + 1
      rw [W64_toNat_of_lt' w (by split at hww <;> omega)]
      split at hww <;> omega
    · exact h19 x a hx

/-- `ReleasePendingPages` with no live writer, `ro` holding every registered reader's txid
(`metaR`'s `F`, design §3.6). -/
theorem storeOK_release (σ : StoreSt) (ro : List w64) (h : storeOK σ) (hw : σ.wtx = none)
    (hwv : σ.wlent = false) (hro : ∀ k r, σ.R !! k = some r → W64 (r.v.txid : Int) ∈ ro)
    (hro' : ∀ t ∈ ro, t.toNat ≤ σ.C.txid) (hro1 : ∀ t ∈ ro, 1 ≤ t.toNat) :
    storeOK (σ.release ro) := by
  have htlt := treeSlot_lt64 σ h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  have hc63 : σ.C.txid < 2 ^ 63 := h2.2.2.2.2.2
  have hwvn := h16 hw
  have hpubf := h6 hw
  obtain ⟨w1, w2, w3, w4, w5⟩ := h4
  have hrel := relOK_releasePending σ.fl ro (fun t ht => ⟨hro1 t ht, by have := hro' t ht; omega⟩) w5
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hrel
  generalize hfl' : σ.fl.releasePending ro = fl' at r1 r2 r3 r4 r5 r6
  have hσ' : (σ.release ro).fl = fl' := by simp only [StoreSt.release]; exact hfl'
  -- every pending entry is a committed transaction's
  have hpt : ∀ t pd, σ.fl.pending !! t = some pd → t.toNat ≤ σ.C.txid := by
    intro t pd hp
    rcases h3.2.2.1 t pd hp with h' | ⟨h', -⟩
    · exact h'
    · rw [hw] at h'; cases h'
  have hpend_sub : ∀ s, s ∈ pendSlots fl' → s ∈ pendSlots σ.fl := by
    intro s hs
    obtain ⟨t, pd', x, hp, hx, rfl⟩ := (mem_pendSlots _ _).1 hs
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
    obtain ⟨pd, j, hp0, hj, -⟩ := r3 t pd' i x hp hi
    exact (mem_pendSlots _ _).2 ⟨t, pd, x, hp0, List.mem_of_getElem? hj, rfl⟩
  have htree_np : ∀ s, s ∈ treeSlots σ.C → s ∉ pendSlots σ.fl := by
    intro s hs
    rcases h17 s hs with h' | h'
    · exact h'
    · rw [hw] at h'
      exact not_pend_of_only_none _ s (htlt s ((mem_pagesSlots' _ _).1 hs)) h'
  -- the MVCC rule of a view the release must spare
  have hmv : ∀ v : View, mvccView σ.fl v →
      (∀ s, coversSlot v.pages s → W64 (s : Int) ∈ fl'.free → False) → mvccView fl' v := by
    intro v ⟨m1, m2⟩ hno
    refine ⟨fun id pg hp a ha => m1 id pg hp a (r1 ▸ ha), fun s hs => ?_⟩
    obtain ⟨a, b, c⟩ := m2 s hs
    refine ⟨a, fun hx => hno s hs hx, fun t pd' i hp hi => ?_⟩
    obtain ⟨pd, j, hp0, hj, he⟩ := r3 t pd' i _ hp hi
    rw [← he]; exact c t pd j hp0 hj
  have hreader : ∀ k r, σ.R !! k = some r →
      ∀ s, coversSlot r.v.pages s → W64 (s : Int) ∈ fl'.free → False := by
    intro k r hr s hs hx
    obtain ⟨-, ⟨-, m2⟩, -⟩ := h7 k r hr
    obtain ⟨-, hnf, hpend⟩ := m2 s hs
    rcases r2 _ hx with hx | ⟨t, pd, i, hp, hi, hq⟩
    · exact hnf hx
    · obtain ⟨ha, ht⟩ := hpend t pd i hp hi
      have hT := hro k r hr
      have hrt : r.v.txid ≤ σ.C.txid := (h7 k r hr).1
      have := hq _ hT
      rw [W64_toNat_of_lt' _ (by omega)] at this
      exact this ⟨ha, ht⟩
  refine ⟨h1, h2, ?_, ?_, h5, h6, fun k r hr => ?_, fun v hv => ?_, h9, h10, h11,
    fun s hs => h12 s ?_, fun b l hb s hs => h13 b l hb s ?_, h14, h15, h16, fun s hs => ?_,
    fun b => ?_, fun x a hx => ?_, fun _ s hs _ hpo => ?_, h21⟩
  · -- flBelow
    rw [hσ']
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h3
    have hpid : ∀ x, x ∈ fl'.pendingIds → x ∈ σ.fl.pendingIds := by
      intro x hx
      simp only [FLPg.pendingIds, List.mem_flatMap] at hx ⊢
      obtain ⟨⟨t, pd'⟩, hkv, hx⟩ := hx
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
      obtain ⟨pd, j, hp0, hj, -⟩ := r3 t pd' i x ((GMap.mem_toList _ _ _).1 hkv) hi
      exact ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp0, List.mem_of_getElem? hj⟩
    refine ⟨fun x hx => ?_, fun t pd' x hp hx hle => ?_, fun t pd' hp => ?_, b4, fun x hx => ?_,
      fun x hx => b6 x (hpid x hx)⟩
    · rcases r2 x hx with hx | ⟨t, pd, i, hp, hi, -⟩
      · exact b1 x hx
      · exact b2 t pd x hp (List.mem_of_getElem? hi) (hpt t pd hp)
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
      obtain ⟨pd, j, hp0, hj, -⟩ := r3 t pd' i x hp hi
      exact b2 t pd x hp0 (List.mem_of_getElem? hj) hle
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (r6 t pd' hp)
      exact Or.inl (hpt t q hq)
    · rcases r2 x hx with hx | ⟨t, pd, i, hp, hi, -⟩
      · exact b5 x hx
      · apply b6
        simp only [FLPg.pendingIds, List.mem_flatMap]
        exact ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, List.mem_of_getElem? hi⟩
  · -- WF
    rw [hσ']
    obtain ⟨L, hL⟩ := releasePending_free σ.fl ro
    rw [hfl'] at hL
    have hnd := r4.nodup_iff.2 w1
    refine ⟨hnd, fun x hx => w2 x (r4.subset hx), ?_, by rw [r4.length_eq]; exact w4, r5⟩
    rw [hL]
    apply sortPgids_incr'
    rw [← hL]
    exact (List.nodup_append.1 hnd).1
  · obtain ⟨a, b, c, d, e, f⟩ := h7 k r hr
    refine ⟨a, ?_, fun s hs => ?_, d, e, f⟩
    · rw [hσ']; exact hmv r.v b (hreader k r hr)
    · have hin := c s hs
      rw [mem_storeSlots] at hin ⊢
      simp only [StoreSt.release]
      rw [hfl']
      rcases hin with hin | hin
      · exact Or.inl hin
      · right
        obtain ⟨t, pd, x, hp, hx, hxs⟩ := (mem_pendSlots _ _).1 hin
        have hxa : x ∈ fl'.allIds := r4.symm.subset (by
          simp only [FLPg.allIds, FLPg.pendingIds, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩)
        simp only [FLPg.allIds, List.mem_append] at hxa
        rcases hxa with hxa | hxa
        · exfalso
          apply hreader k r hr s hs
          rw [← hxs, W64_toNat_eq]; exact hxa
        · simp only [pendSlots, List.mem_map]
          exact ⟨x, hxa, hxs⟩
  · simp only [StoreSt.release, hwvn] at hv; cases hv
  · rw [mem_storeSlots] at hs ⊢
    simp only [StoreSt.release] at hs
    rw [hfl'] at hs
    exact hs.imp id (hpend_sub s)
  · rw [mem_storeSlots] at hs ⊢
    simp only [StoreSt.release] at hs
    rw [hfl'] at hs
    exact hs.imp id (hpend_sub s)
  · left; rw [hσ']; exact fun hp => htree_np s hs (hpend_sub s hp)
  · rw [hσ']
    refine hmv _ (h18 b) (fun s hs hx => ?_)
    rcases r2 _ hx with hx | ⟨t, pd, i, hp, hi, -⟩
    · exact ((h18 b).2 s hs).2.1 hx
    · exact htree_np s ((mem_pagesSlots' _ _).2 hs) ((mem_pendSlots _ _).2
        ⟨t, pd, _, hp, List.mem_of_getElem? hi, W64_toNat_of_lt' s (htlt s hs)⟩)
  · rw [hσ', r1] at hx; exact h19 x a hx
  · exfalso
    rw [hσ'] at hs hpo
    obtain ⟨t, pd, x, hp, hx, rfl⟩ := (mem_pendSlots _ _).1 hs
    have := hpo t pd hp (by rw [W64_toNat_eq]; exact hx)
    simp [StoreSt.release, hw] at this

/-- **The commit point**: the new committed state `C'` (spill's post, design §4.2: its tree
`treeOK`, every dropped base page pending for `w`, its new pages the writer's allocations, read
from `bs`), at the next txid. -/
theorem storeOK_publish (σ : StoreSt) (w : Nat) (C' : CommitSt) (bs : Nat → List w8)
    (h : storeOK σ) (hw : σ.wtx = some w) (hpub : σ.pub = false) (ht : C'.txid = w)
    (hmeta : C'.metaOk) (htree : treeOK C') (hhwm : C'.hwm ≤ 2 ^ 62)
    (hdrop : ∀ s ∈ treeSlots σ.C, s ∉ treeSlots C' → s ∈ pendSlots σ.fl)
    (hnew : ∀ s ∈ treeSlots C', s ∉ treeSlots σ.C → s ∉ pendSlots σ.fl ∧
      (∀ k r, σ.R !! k = some r → ¬ coversSlot r.v.pages s) ∧ (bs s).length = 4096 ∧
      W64 (s : Int) ∉ σ.fl.free ∧ (∀ b l, σ.ms = some (b, l) → s < l / 4096) ∧ 2 ≤ s)
    (hnp : ∀ s ∈ treeSlots C', s ∉ pendSlots σ.fl)
    (hbytes : ∀ id pg, C'.pages !! id = some pg → σ.C.pages !! id = some pg ∨
      ((∀ j < 1 + pageOverflow pg, id + j ∉ storeSlots σ) ∧
        pg = (List.range' id (1 + pageOverflow pg)).flatMap bs))
    (hfl : flBelow σ.fl C' (some w)) :
    storeOK (σ.publish C' bs) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  have hww : w = σ.C.txid + 1 := by have := h5 w hw; simp [hpub] at this; omega
  have hsub : ∀ s, s ∈ storeSlots σ → s ∈ storeSlots (σ.publish C' bs) := by
    intro s hs
    rw [mem_storeSlots] at hs ⊢
    simp only [StoreSt.publish]
    rcases hs with hs | hs
    · by_cases h' : s ∈ treeSlots C'
      · exact Or.inl h'
      · exact Or.inr (hdrop s hs h')
    · exact Or.inr hs
  have hb_old : ∀ s, s ∈ storeSlots σ → (σ.publish C' bs).bytes s = σ.bytes s := by
    intro s hs
    rw [mem_storeSlots] at hs
    simp only [StoreSt.publish, if_pos hs]
  have hnew' : ∀ s, s ∈ storeSlots (σ.publish C' bs) → s ∉ storeSlots σ →
      s ∈ treeSlots C' ∧ s ∉ treeSlots σ.C ∧ s ∉ pendSlots σ.fl := by
    intro s hs hn
    rw [mem_storeSlots] at hs hn
    simp only [StoreSt.publish] at hs
    rcases hs with hs | hs
    · exact ⟨hs, fun h' => hn (Or.inl h'), fun h' => hn (Or.inr h')⟩
    · exact absurd (Or.inr hs) hn
  have hb_new : ∀ s, s ∉ storeSlots σ → (σ.publish C' bs).bytes s = bs s := by
    intro s hs
    rw [mem_storeSlots] at hs
    simp only [StoreSt.publish, if_neg hs]
  have hpagesFrom : ∀ P : Pages, (∀ s, coversSlot P s → s ∈ storeSlots σ) →
      pagesFromBytes σ.bytes P → pagesFromBytes (σ.publish C' bs).bytes P := by
    intro P hin hP id' pg' hp'
    refine (hP id' pg' hp').trans ?_
    refine flatMap_congr' _ _ _ fun s hs => (hb_old s (hin s ?_)).symm
    simp only [List.mem_range'] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    exact ⟨id', pg', hp', by omega, by omega⟩
  -- a new page's slots are no view's
  have hagree : ∀ Q : Pages, (∀ s, coversSlot Q s → s ∈ storeSlots σ) →
      pagesAgree σ.C.pages Q → pagesAgree C'.pages Q := by
    intro Q hQ hag i pi j pj s hi hj e1 e2 e3 e4
    rcases hbytes i pi hi with hold | ⟨hn, -⟩
    · exact hag i pi j pj s hold hj e1 e2 e3 e4
    · exfalso
      have := hn (s - i) (by omega)
      rw [show i + (s - i) = s by omega] at this
      exact this (hQ s ⟨j, pj, hj, e3, e4⟩)
  refine ⟨hmeta, htree, (by simp only [StoreSt.publish]; rw [hw]; exact hfl), h4,
    fun w' hw' => ?_, fun h' => (by simp only [StoreSt.publish] at h'; rw [hw] at h'; cases h'),
    fun k r hr => ?_, fun v hv => ?_, fun id pg hp => ?_,
    fun k r hr => ⟨hagree _ (h7 k r hr).2.2.1 (h10 k r hr).1, (h10 k r hr).2⟩,
    fun v hv => hagree _ (h8 v hv).2.2.1 (h11 v hv), fun s hs => ?_, fun b l hb s hs => ?_,
    h14, h15, h16, fun s hs => Or.inl (hnp s hs), fun b => ?_, fun x a hx => ?_,
    fun hp => (by simp [StoreSt.publish] at hp), hhwm⟩
  · simp only [StoreSt.publish, ite_true, Nat.add_zero] at hw' ⊢
    rw [hw] at hw'; cases hw'; exact ht.symm
  · obtain ⟨a, b, c, d, e, f⟩ := h7 k r hr
    exact ⟨by simp only [StoreSt.publish]; omega, b, fun s hs => hsub s (c s hs), d,
      hpagesFrom _ c e, f⟩
  · obtain ⟨a, b, c, d, e, -, g⟩ := h8 v hv
    exact ⟨a, b, fun s hs => hsub s (c s hs), d, hpagesFrom _ c e,
      fun hp => by simp [StoreSt.publish] at hp, g⟩
  · rcases hbytes id pg hp with hold | ⟨hn, hpg⟩
    · refine (h9 id pg hold).trans (flatMap_congr' _ _ _ fun s hs => (hb_old s ?_).symm)
      simp only [List.mem_range'] at hs
      obtain ⟨j, hj, rfl⟩ := hs
      exact tree_in_store' σ _ ⟨id, pg, hold, by omega, by omega⟩
    · refine hpg.trans (flatMap_congr' _ _ _ fun s hs => (hb_new s ?_).symm)
      simp only [List.mem_range'] at hs
      obtain ⟨j, hj, rfl⟩ := hs
      simpa using hn j hj
  · by_cases ho : s ∈ storeSlots σ
    · rw [hb_old s ho]; exact h12 s ho
    · obtain ⟨hs1, hs2, -⟩ := hnew' s hs ho
      obtain ⟨-, -, hl, -, -, h2s⟩ := hnew s hs1 hs2
      exact ⟨h2s, by rw [hb_new s ho]; exact hl⟩
  · by_cases ho : s ∈ storeSlots σ
    · exact h13 b l hb s ho
    · obtain ⟨hs1, hs2, -⟩ := hnew' s hs ho
      exact (hnew s hs1 hs2).2.2.2.2.1 b l hb
  · refine ⟨fun id pg _ a ha => ?_, fun s hs => ?_⟩
    · have := h19 _ a ha; simp only [View.ofC, StoreSt.publish]; omega
    · have hs' : s ∈ treeSlots C' := (mem_pagesSlots' _ _).2 hs
      have hs64 : s < 2 ^ 64 := by have := cover_lt_hwm C' htree s hs; omega
      refine ⟨?_, ?_, fun t pd i hp hi => ?_⟩
      · by_cases ho : s ∈ treeSlots σ.C
        · exact ((h18 b).2 s ((mem_pagesSlots' _ _).1 ho)).1
        · exact (hnew s hs' ho).2.2.2.2.2
      · by_cases ho : s ∈ treeSlots σ.C
        · exact ((h18 b).2 s ((mem_pagesSlots' _ _).1 ho)).2.1
        · exact (hnew s hs' ho).2.2.2.1
      · exfalso
        exact hnp s hs' ((mem_pendSlots _ _).2 ⟨t, pd, _, hp, List.mem_of_getElem? hi,
          W64_toNat_of_lt' s hs64⟩)
  · have := h19 x a hx; simp only [StoreSt.publish]; omega

private theorem storeOK_rollbackE (σ : StoreSt) (w : Nat) (h : storeOK σ) (hw : σ.wtx = some w)
    (hpub : σ.pub = false) : storeOK (σ.rollbackE (W64 (w : Int))) := by
  have htlt := treeSlot_lt64 σ h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  have hsm : σ.C.txid + 1 < 2 ^ 64 := h3.2.2.2.1
  have hww : w = σ.C.txid + 1 := by have := h5 w hw; simp [hpub] at this; omega
  have hT : (W64 (w : Int)).toNat = w := W64_toNat_of_lt' w (by omega)
  generalize W64 (w : Int) = T at hT ⊢
  have hsub : ∀ s, s ∈ storeSlots (σ.rollbackE T) → s ∈ storeSlots σ := by
    intro s hs
    simp only [storeSlots, mem_list_dedup, List.mem_append, StoreSt.rollbackE] at hs ⊢
    exact hs.imp id (pendSlots_rollback σ.fl T s)
  -- a slot of the store that leaves it is pending only for the writer
  have honly : ∀ s, s ∈ pendSlots σ.fl → s ∉ pendSlots (σ.fl.rollbackEntry T) →
      pendingOnlyFromWriter σ.fl σ.wtx s := by
    intro s hs hs' t pd hp hx
    have hs64 : s < 2 ^ 64 := by
      obtain ⟨t', pd', x, -, -, hxs⟩ := (mem_pendSlots _ _).1 hs
      rw [← hxs]; exact x.isLt
    by_cases ht : t = T
    · subst ht; rw [hw, hT]
    · exfalso; apply hs'
      refine (mem_pendSlots _ _).2 ⟨t, pd, _, ?_, hx, W64_toNat_of_lt' s hs64⟩
      simp only [FLPg.rollbackEntry]; exact (GMap.lookup_delete_Some _ _ _ _).2 ⟨fun e => ht e.symm, hp⟩
  have hin : ∀ v : View, viewInStore σ v → (∀ s, coversSlot v.pages s → s ∉ treeSlots σ.C →
      s ∈ pendSlots σ.fl → pendingOnlyFromWriter σ.fl σ.wtx s → False) →
      viewInStore (σ.rollbackE T) v := by
    intro v hv hno s hs
    have := hv s hs
    simp only [storeSlots, mem_list_dedup, List.mem_append, StoreSt.rollbackE] at this ⊢
    rcases this with h' | h'
    · exact Or.inl h'
    · by_cases hp : s ∈ pendSlots (σ.fl.rollbackEntry T)
      · exact Or.inr hp
      · by_cases ht : s ∈ treeSlots σ.C
        · exact Or.inl ht
        · exact (hno s hs ht h' (honly s h' hp)).elim
  obtain ⟨L, hL⟩ := pendingIds_rollback_perm σ.fl T
  have hperm : σ.fl.allIds.Perm (L ++ (σ.fl.rollbackEntry T).allIds) := by
    simp only [FLPg.allIds]
    refine (hL.append_left _).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  obtain ⟨w1, w2, w3, w4, w5⟩ := h4
  refine ⟨h1, h2, ⟨h3.1, fun t pd x hp hx hle => h3.2.1 t pd x (rollback_pending _ _ _ _ hp).2 hx hle,
      fun t pd hp => h3.2.2.1 t pd (rollback_pending _ _ _ _ hp).2, h3.2.2.2.1, h3.2.2.2.2.1,
      fun x hx => h3.2.2.2.2.2 x (hL.symm.subset (List.mem_append_right _ hx))⟩,
    ⟨(List.nodup_append.1 (hperm.nodup_iff.1 w1)).2.1,
      fun x hx => w2 x (hperm.symm.subset (List.mem_append_right _ hx)), w3, ?_,
      fun t p hp => w5 t p (rollback_pending _ _ _ _ hp).2⟩, h5, h6,
    fun k r hr => ?_, fun v hv => ?_, h9, h10, h11, fun s hs => h12 s (hsub s hs),
    fun b l hb s hs => h13 b l hb s (hsub s hs), h14, h15, h16, fun s hs => ?_,
    fun b => mvccView_rollback _ _ T (h18 b), fun x a hx => ?_, fun _ s hs _ hpo => ?_, h21⟩
  · have := hperm.length_eq; simp only [List.length_append] at this
    simp only [StoreSt.rollbackE]; omega
  · obtain ⟨a, b, c, d, e, f⟩ := h7 k r hr
    exact ⟨a, mvccView_rollback _ _ T b, hin _ c (fun s hs ht hp ho =>
      h20 hpub s hp ht ho k r hr hs), d, e, f⟩
  · obtain ⟨a, b, c, d, e, f, g⟩ := h8 v hv
    refine ⟨a, mvccView_rollback _ _ T b, hin _ c (fun s hs ht _ _ => ht ?_), d, e, f, g⟩
    rw [(f hpub).1] at hs; exact (mem_pagesSlots' _ _).2 hs
  · rcases h17 s hs with h' | h'
    · exact Or.inl (fun hp => h' (pendSlots_rollback _ _ _ hp))
    · exact Or.inr (fun t pd hp hx => h' t pd (rollback_pending _ _ _ _ hp).2 hx)
  · obtain ⟨hne, ha | ⟨pd, i, hpd, -, hi2⟩⟩ := rollback_allocs σ.fl T x a hx
    · exact h19 x a ha
    · rcases h3.2.2.1 T pd hpd with h' | ⟨-, h''⟩
      · rw [hT] at h'; omega
      · have := h'' a (List.mem_of_getElem? hi2); rw [hT] at this
        show _ ≤ σ.C.txid + 1; omega
  · exfalso
    obtain ⟨t, pd, x, hp, hx, rfl⟩ := (mem_pendSlots _ _).1 hs
    obtain ⟨hne, -⟩ := rollback_pending _ _ _ _ hp
    have := hpo t pd hp (by rw [W64_toNat_eq]; exact hx)
    simp only [StoreSt.rollbackE, hw, Option.some.injEq] at this
    exact hne (BitVec.eq_of_toNat_eq (by rw [hT]; exact this.symm))


/-- `freelist.Rollback(w)` by the live writer before its publish (no change without a pending
entry, `FLPg.rollback`). -/
theorem storeOK_rollback (σ : StoreSt) (w : Nat) (h : storeOK σ) (hw : σ.wtx = some w)
    (hpub : σ.pub = false) : storeOK (σ.rollback (W64 (w : Int))) := by
  by_cases hn : σ.fl.pending !! W64 (w : Int) = none
  · have e : σ.rollback (W64 (w : Int)) = σ := by
      unfold StoreSt.rollback FLPg.rollback; rw [if_pos hn]
    rw [e]; exact h
  · have e : σ.rollback (W64 (w : Int)) = σ.rollbackE (W64 (w : Int)) := by
      unfold StoreSt.rollback StoreSt.rollbackE FLPg.rollback; rw [if_neg hn]
    rw [e]; exact storeOK_rollbackE σ w h hw hpub

/-- `Reload`/`NoSyncReload` of ids that are `W` slots below the high-water mark. -/
theorem storeOK_reload (σ : StoreSt) (ids : List w64) (h : storeOK σ)
    (hids : ∀ x ∈ ids, 2 ≤ x.toNat ∧ x.toNat < σ.C.hwm ∧ x.toNat < 2 ^ 62 ∧
      (x.toNat ∉ storeSlots σ ∨ x ∈ σ.fl.pendingIds))
    (hnd : ids.Nodup) : storeOK (σ.reload ids) := by
  have hlt := storeSlot_lt σ h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  have hfree : ∀ x, x ∈ (σ.fl.reload ids).free ↔ x ∈ ids ∧ x ∉ σ.fl.pendingIds := by
    intro x
    simp only [FLPg.reload, mem_sortPgids, List.mem_filter, decide_eq_true_eq]
  -- the MVCC rule of a view in the store survives
  have hmv : ∀ v : View, mvccView σ.fl v → viewInStore σ v → mvccView (σ.fl.reload ids) v := by
    intro v ⟨m1, m2⟩ hin
    refine ⟨m1, fun s hs => ?_⟩
    obtain ⟨a, -, c⟩ := m2 s hs
    refine ⟨a, fun hx => ?_, c⟩
    obtain ⟨hx1, hx2⟩ := (hfree _).1 hx
    have hsin := hin s hs
    rcases (hids _ hx1).2.2.2 with h' | h'
    · rw [W64_toNat_of_lt s (hlt s hsin)] at h'; exact h' hsin
    · exact hx2 h'
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := h3
  refine ⟨h1, h2, ⟨fun x hx => (hids x ((hfree x).1 hx).1).2.1, hb2, hb3, hb4,
      fun x hx => (hids x ((hfree x).1 hx).1).2.2.1, hb6⟩, ?_, h5, h6,
    fun k r hr => ?_, fun v hv => ?_, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    fun b => hmv _ (h18 b) (fun s hs => tree_in_store σ s hs), h19, h20, h21⟩
  · obtain ⟨w1, w2, w3, w4, w5⟩ := h4
    have hpnd : σ.fl.pendingIds.Nodup := (List.nodup_append.1 w1).2.1
    have hF : (sortPgids (ids.filter fun x => decide (x ∉ σ.fl.pendingIds))).Nodup :=
      (List.mergeSort_perm _ _).nodup_iff.2 (hnd.filter _)
    have hall : ∀ x ∈ (σ.fl.reload ids).allIds, x.toNat < 2 ^ 62 := by
      intro x hx
      simp only [FLPg.allIds, List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hids x ((hfree x).1 hx).1).2.2.1
      · exact hb6 x hx
    have hnd' : (σ.fl.reload ids).allIds.Nodup := by
      simp only [FLPg.allIds]
      refine List.nodup_append.2 ⟨hF, hpnd, fun a ha b hb hab => ?_⟩
      subst hab
      exact ((hfree a).1 ha).2 hb
    refine ⟨hnd', fun x hx => ?_, sortPgids_incr _ (hnd.filter _), ?_, w5⟩
    · simp only [FLPg.allIds, List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hids x ((hfree x).1 hx).1).1
      · exact w2 x (List.mem_append_right _ hx)
    · have := nodup_len_le _ _ hnd' hall
      simp only [StoreSt.reload]; omega
  · obtain ⟨a, b, c, d, e, f⟩ := h7 k r hr
    exact ⟨a, hmv r.v b c, c, d, e, f⟩
  · obtain ⟨a, b, c, d, e, f, g⟩ := h8 v hv
    exact ⟨a, hmv v b c, c, d, e, f, g⟩

/-- `munmap` with no reader and the writer's view in. -/
theorem storeOK_gather (σ : StoreSt) (h : storeOK σ) (hR : σ.R = ∅) (hwv : σ.wlent = false) :
    storeOK σ.gather := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun k r hr => ?_, fun v hv => ?_, h9,
    fun k r hr => ?_, h11, h12, fun b l hb => ?_, fun _ => ⟨hR, hwv⟩, h15, h16, h17⟩
  · simp [StoreSt.gather, hR] at hr
  · obtain ⟨a, b, c, d, e, f, -⟩ := h8 v hv
    exact ⟨a, b, c, d, e, f, fun h => by simp [StoreSt.gather, hwv] at h⟩
  · simp [StoreSt.gather, hR] at hr
  · simp [StoreSt.gather] at hb

/-- `mmap` of a mapping covering every store slot. -/
theorem storeOK_carve (σ : StoreSt) (b : Loc) (l : Nat) (h : storeOK σ) (hms : σ.ms = none)
    (hl : ∀ s ∈ storeSlots σ, s < l / 4096) : storeOK (σ.carve b l) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  obtain ⟨hR, hwl⟩ := h14 hms
  refine ⟨h1, h2, h3, h4, h5, h6, fun k r hr => ?_, fun v hv => ?_, h9,
    fun k r hr => ?_, h11, h12, fun b' l' hb => ?_, fun hb => ?_, h15, h16, h17⟩
  · simp [StoreSt.carve, hR] at hr
  · obtain ⟨a, b, c, d, e, f, -⟩ := h8 v hv
    exact ⟨a, b, c, d, e, f, fun h => by simp [StoreSt.carve, hwl] at h⟩
  · simp [StoreSt.carve, hR] at hr
  · simp only [StoreSt.carve, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl⟩ := hb
    exact hl
  · simp [StoreSt.carve] at hb

/-- `Open`'s loaded freelist: no reader, no writer, nothing pending. -/
theorem storeOK_setFl (σ : StoreSt) (fl : FLPg) (h : storeOK σ) (hR : σ.R = ∅)
    (hw : σ.wtx = none) (hwv : σ.wv = none) (hfl : fl.WF ∧ fl.pending = ∅ ∧
      flBelow fl σ.C none ∧ (∀ x ∈ fl.free, ¬ coversSlot σ.C.pages x.toNat) ∧ fl.allocs = ∅) :
    storeOK (σ.setFl fl) := by
  have hlt := storeSlot_lt σ h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  obtain ⟨hwf, hpe, hbl, hcov, hal⟩ := hfl
  have hsub : ∀ s, s ∈ storeSlots (σ.setFl fl) → s ∈ storeSlots σ := by
    intro s hs
    simp only [storeSlots, StoreSt.setFl, mem_list_dedup, List.mem_append,
      pendSlots_empty fl hpe, List.not_mem_nil, or_false] at hs ⊢
    exact Or.inl hs
  refine ⟨h1, h2, ?_, hwf, fun w hw' => by simp [StoreSt.setFl, hw] at hw', h6,
    fun k r hr => by simp [StoreSt.setFl, hR] at hr,
    fun v hv => by simp [StoreSt.setFl, hwv] at hv, h9,
    fun k r hr => by simp [StoreSt.setFl, hR] at hr,
    fun v hv => by simp [StoreSt.setFl, hwv] at hv,
    fun s hs => h12 s (hsub s hs), fun b l hb s hs => h13 b l hb s (hsub s hs), h14, h15, h16,
    fun s _ => Or.inl (by simp [StoreSt.setFl, pendSlots_empty fl hpe]), fun b => ?_,
    fun x a hx => by simp [StoreSt.setFl, hal] at hx,
    fun _ s hs => (by simp [StoreSt.setFl, pendSlots_empty fl hpe] at hs), h21⟩
  · simpa [StoreSt.setFl, hw] using hbl
  · refine ⟨fun id pg _ a ha => by simp [StoreSt.setFl, hal] at ha, fun s hs => ⟨(h18 b).2 s hs |>.1,
      fun hx => ?_, fun t pd i ht => by simp [StoreSt.setFl, hpe] at ht⟩⟩
    have := hcov _ hx
    rw [W64_toNat_of_lt s (hlt s (tree_in_store σ s hs))] at this
    exact this hs

end store

end bbolt
end EtcdGrove
end Perennial
