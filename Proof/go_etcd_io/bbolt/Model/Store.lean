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
freelist, the registered readers, the writer's borrowed base view (out from its begin to its
close), the live writer's txid, whether it has published (between its meta write and its
`close`), and the bytes of the store slots (stable while they are store slots). -/
structure StoreSt where
  ms : MapSt
  C : CommitSt
  fl : FLPg
  R : GMap Nat RdInfo
  wv : Option View
  wtx : Option Nat
  pub : Bool
  bytes : Nat → List w8

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
  match σ.wv with
  | some v => if coversSlot v.pages s then optAdd wq r else r
  | none => r

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
  (∀ b l, σ.ms = some (b, l) → v.base = b)

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
  (σ.ms = none → σ.R = ∅ ∧ σ.wv = none) ∧
  (∀ s, s ∈ treeSlots σ.C → s ∉ pendSlots σ.fl ∨ pendingOnlyFromWriter σ.fl σ.wtx s)

/-! ## Transitions (one per `Inv/Store.lean` lemma) -/

/-- A reader registers under the key `k` with the view `r.v`. -/
def StoreSt.register (σ : StoreSt) (k : Nat) (r : RdInfo) : StoreSt := { σ with R := σ.R.insert k r }
proj_simps StoreSt.register

/-- A reader deregisters. -/
def StoreSt.deregister (σ : StoreSt) (k : Nat) : StoreSt := { σ with R := σ.R.delete k }
proj_simps StoreSt.deregister

/-- The writer begins: its txid is the next one, its base view `v` borrowed. -/
def StoreSt.wbegin (σ : StoreSt) (v : View) : StoreSt :=
  { σ with wv := some v, wtx := some (σ.C.txid + 1), pub := false }
proj_simps StoreSt.wbegin

/-- The writer's view returned for a remap (`wtx`, `pub` kept: round 4, N6). -/
def StoreSt.wreturn (σ : StoreSt) : StoreSt := { σ with wv := none }
proj_simps StoreSt.wreturn

/-- The writer's view re-borrowed after a remap (on the new base). -/
def StoreSt.wborrow (σ : StoreSt) (v : View) : StoreSt := { σ with wv := some v }
proj_simps StoreSt.wborrow

/-- The writer's `close`: the view returned, no live writer (the only reset of `wtx`/`pub`). -/
def StoreSt.wclose (σ : StoreSt) : StoreSt := { σ with wv := none, wtx := none, pub := false }
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

/-! ## Lemma statements (U3) -/

/-- What is lent of a slot is below the half (`|R| · rfrac ≤ 1`, by the readers' `mtok`
deposits). Used by U3 (every borrow). -/
theorem lent_lt_half (σ : StoreSt) (hR : σ.R.size ≤ Int.toNat sync.rwmutex.actualMaxReaders)
    (s : Nat) (q : Qp) (h : lent σ s = some q) : q < (1 : Qp).half := by
  sorry

theorem storeOK_register (σ : StoreSt) (k : Nat) (r : RdInfo) (b : Loc) (l : Nat)
    (h : storeOK σ) (hms : σ.ms = some (b, l)) (hk : σ.R !! k = none)
    (hv : r.v = View.ofC b σ.C) : storeOK (σ.register k r) := by
  sorry

theorem storeOK_deregister (σ : StoreSt) (k : Nat) (h : storeOK σ) :
    storeOK (σ.deregister k) := by
  sorry

theorem storeOK_wbegin (σ : StoreSt) (v : View) (b : Loc) (l : Nat) (h : storeOK σ)
    (hms : σ.ms = some (b, l)) (hw : σ.wtx = none) (hwv : σ.wv = none)
    (hv : v = View.ofC b σ.C) : storeOK (σ.wbegin v) := by
  sorry

theorem storeOK_wreturn (σ : StoreSt) (h : storeOK σ) : storeOK σ.wreturn := by
  sorry

/-- Re-borrowing at a remap: the view `v` (the returned one, on the new base `b`) has the
writer's view's facts and agrees with the other views. -/
theorem storeOK_wborrow (σ : StoreSt) (v : View) (b : Loc) (l : Nat) (h : storeOK σ)
    (hwv : σ.wv = none) (hms : σ.ms = some (b, l)) (hok : (σ.wborrow v).wOK v)
    (hagree : pagesAgree σ.C.pages v.pages ∧
      ∀ k r, σ.R !! k = some r → pagesAgree v.pages r.v.pages) :
    storeOK (σ.wborrow v) := by
  sorry

/-- The writer's `close`: published, or with nothing pending for it (rolled back). -/
theorem storeOK_wclose (σ : StoreSt) (h : storeOK σ)
    (hp : σ.pub = true ∨ ∀ w, σ.wtx = some w → σ.fl.pending !! W64 (w : Int) = none) :
    storeOK σ.wclose := by
  sorry

/-- `Free` by the live writer `w` (before its publish) of a page of the current tree, or of the
old synced freelist page (whose bytes `pg` then enter the store). -/
theorem storeOK_free (σ : StoreSt) (w : Nat) (id : w64) (n : Nat) (pg : Nat → List w8)
    (h : storeOK σ) (hw : σ.wtx = some w) (hpub : σ.pub = false)
    (hcan : σ.fl.canFree (W64 (w : Int)) id n)
    (hpage : (∃ p, σ.C.pages !! id.toNat = some p ∧ 1 + pageOverflow p = n) ∨
      (σ.C.flpg = some id.toNat ∧ ∀ j < n, ¬ coversSlot σ.C.pages (id.toNat + j) ∧
        (pg (id.toNat + j)).length = 4096)) :
    storeOK (σ.free (W64 (w : Int)) id n pg) := by
  sorry

/-- `Allocate` by the live writer of free ids. -/
theorem storeOK_alloc (σ : StoreSt) (w : Nat) (r : w64) (n : Nat) (h : storeOK σ)
    (hw : σ.wtx = some w) (ha : σ.fl.canAlloc r n) :
    storeOK (σ.alloc (W64 (w : Int)) r n) := by
  sorry

/-- `ReleasePendingPages` with no live writer, `ro` holding every registered reader's txid
(`metaR`'s `F`, design §3.6). -/
theorem storeOK_release (σ : StoreSt) (ro : List w64) (h : storeOK σ) (hw : σ.wtx = none)
    (hwv : σ.wv = none) (hro : ∀ k r, σ.R !! k = some r → W64 (r.v.txid : Int) ∈ ro)
    (hro' : ∀ t ∈ ro, t.toNat ≤ σ.C.txid) :
    storeOK (σ.release ro) := by
  sorry

/-- **The commit point**: the new committed state `C'` (spill's post, design §4.2: its tree
`treeOK`, every dropped base page pending for `w`, its new pages the writer's allocations, read
from `bs`), at the next txid. -/
theorem storeOK_publish (σ : StoreSt) (w : Nat) (C' : CommitSt) (bs : Nat → List w8)
    (h : storeOK σ) (hw : σ.wtx = some w) (hpub : σ.pub = false) (ht : C'.txid = w)
    (hmeta : C'.metaOk) (htree : treeOK C')
    (hdrop : ∀ s ∈ treeSlots σ.C, s ∉ treeSlots C' → s ∈ pendSlots σ.fl)
    (hnew : ∀ s ∈ treeSlots C', s ∉ treeSlots σ.C → s ∉ pendSlots σ.fl ∧
      (∀ k r, σ.R !! k = some r → ¬ coversSlot r.v.pages s) ∧ (bs s).length = 4096)
    (hbytes : pagesFromBytes (fun s => if s ∈ treeSlots σ.C ∨ s ∈ pendSlots σ.fl then σ.bytes s
      else bs s) C'.pages)
    (hfl : flBelow σ.fl C' (some w)) :
    storeOK (σ.publish C' bs) := by
  sorry

/-- `freelist.Rollback(w)` by the live writer before its publish. -/
theorem storeOK_rollback (σ : StoreSt) (w : Nat) (h : storeOK σ) (hw : σ.wtx = some w)
    (hpub : σ.pub = false) : storeOK (σ.rollback (W64 (w : Int))) := by
  sorry

/-- `Reload`/`NoSyncReload` of ids that are `W` slots below the high-water mark. -/
theorem storeOK_reload (σ : StoreSt) (ids : List w64) (h : storeOK σ)
    (hids : ∀ x ∈ ids, 2 ≤ x.toNat ∧ x.toNat < σ.C.hwm ∧ x.toNat < 2 ^ 62 ∧
      (x.toNat ∉ storeSlots σ ∨ x ∈ σ.fl.pendingIds))
    (hnd : ids.Nodup) : storeOK (σ.reload ids) := by
  sorry

/-- `munmap` with no reader and the writer's view in. -/
theorem storeOK_gather (σ : StoreSt) (h : storeOK σ) (hR : σ.R = ∅) (hwv : σ.wv = none) :
    storeOK σ.gather := by
  sorry

/-- `mmap` of a mapping covering every store slot. -/
theorem storeOK_carve (σ : StoreSt) (b : Loc) (l : Nat) (h : storeOK σ) (hms : σ.ms = none)
    (hl : ∀ s ∈ storeSlots σ, s < l / 4096) : storeOK (σ.carve b l) := by
  sorry

/-- `Open`'s loaded freelist: no reader, no writer, nothing pending. -/
theorem storeOK_setFl (σ : StoreSt) (fl : FLPg) (h : storeOK σ) (hR : σ.R = ∅)
    (hw : σ.wtx = none) (hwv : σ.wv = none) (hfl : fl.WF ∧ fl.pending = ∅ ∧
      flBelow fl σ.C none ∧ ∀ x ∈ fl.free, ¬ coversSlot σ.C.pages x.toNat) :
    storeOK (σ.setFl fl) := by
  sorry

end store

end bbolt
end EtcdGrove
end Perennial
