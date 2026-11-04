/-
The page store's invariant and its lemmas (U0a of `notes/bbolt-proof-plan.md`; design §3.6):
`pagesInv`, the store slots' cells (lent at `rq` to readers and at `wq` to the writer) and
page-cache bytes, the meta cells' lending (`metaLend`, minibolt's `metaLent`), and the fancy
updates at `pagesN N` that the protocols take (U3 proves them).

Each lemma takes the invariant and the caller's shares of the agreed ghost state, and gives them
back updated; slots moving between the store and the writer's `W` slots move with their cells
and bytes (`slotsOwn`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Locks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section store
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The store slots of a committed state and a freelist (`storeSlots σ = slotsOf σ.C σ.fl`). -/
def slotsOf (C : CommitSt) (fl : FLPg) : List Nat := listDedup (treeSlots C ++ pendSlots fl)

/-- A view's cells at the fraction `q`: page `id` at `base + 4096 · id`. -/
def viewCells (q : Qp) (v : View) : IProp GF :=
  iprop([∗map] id ↦ pg ∈ v.pages, bytesPointsto (v.base +ₗ ((id * 4096 : Nat) : Int)) (DFrac.own q) pg)

/-- The page-cache bytes of slot `s` of the file `p`, all of them, holding `bs`. -/
def osSlot (p : GoString) (s : Nat) (bs : List w8) : IProp GF :=
  iprop(∃ xs : List (w8 × Bool), osBytes p (4096 * s) (DFrac.own 1) xs ∗ ⌜xs.map Prod.fst = bs⌝)

/-- The slots `S` whole, as they move between the store and `W`: their client cell halves (when
mapped) and their page-cache bytes, holding `bs`. -/
def slotsOwn (ms : MapSt) (p : GoString) (S : List Nat) (bs : Nat → List w8) : IProp GF :=
  iprop([∗list] s ∈ S, (match ms with
      | some (base, _) => bytesPointsto (base +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s)
      | none => iprop(emp)) ∗
    osSlot p s (bs s))

/-- **The store slots' cells**: per slot `s`, `e_s` of the client half held here, the rest
(`lent σ s`) lent; nothing while unmapped. -/
def storeCells (σ : StoreSt) : IProp GF :=
  match σ.ms with
  | none => iprop(emp)
  | some (base, _) => iprop([∗list] s ∈ storeSlots σ,
      ∃ e : Qp, ⌜fracSum e (lent σ s) (1 : Qp).half⌝ ∗
        bytesPointsto (base +ₗ ((4096 * s : Nat) : Int)) (DFrac.own e) (σ.bytes s))

/-- **The meta cells' lend quarter**: home; out with the writer (during the meta write); or lent
to the one reader holding `metalock`, which deposits `mlk` and `mtok (rfrac/2)`. -/
def metaLend (B : BNs) (σ : StoreSt) : IProp GF :=
  iprop((metaCellsQ (1 : Qp).half.half σ.ms σ.C ∗ ghostVar B.out (1 : Qp).half false) ∨
    ghostVar B.out (1 : Qp).half true ∨
    (ghostVar B.out (1 : Qp).half false ∗ ghostVar B.mlk 1 () ∗
      ghostVar B.mtok sync.rfrac.half ()))

/-- **The page store's invariant** (design §3.6). -/
def pagesInv (B : BNs) (p : GoString) : IProp GF :=
  iprop(∃ σ : StoreSt,
    ghostVar B.cur (1 : Qp).half.half σ.C ∗ ghostVar B.fl (1 : Qp).half σ.fl ∗
    ghostVar B.map (1 : Qp).half.half σ.ms ∗ ghostVar B.wv (1 : Qp).half σ.wst ∗
    ghostMapAuth B.rds 1 σ.R ∗
    ([∗map] k ↦ r ∈ σ.R, k ↪[B.fltx] (W64 (r.v.txid : Int)) ∗ ghostVar B.mtok sync.rfrac ()) ∗
    storeCells σ ∗ ([∗list] s ∈ storeSlots σ, osSlot p s (σ.bytes s)) ∗
    metaLend B σ ∗ ⌜storeOK σ⌝)

/-! ## Lemma statements (U3), fancy updates at `pagesN N` -/

omit go_gctx sem in
private theorem pagesInv_timeless (B : BNs) (p : GoString) : Timeless (pagesInv (GF := GF) B p) := by
  have h1 : ∀ σ : StoreSt, Timeless (storeCells (GF := GF) σ) := by
    intro σ; unfold storeCells; split <;> infer_instance
  have h2 : ∀ σ : StoreSt, Timeless (metaLend (GF := GF) B σ) := by
    intro σ; unfold metaLend metaCellsQ; split <;> infer_instance
  have h3 : ∀ s bs, Timeless (osSlot (GF := GF) p s bs) := by
    intro s bs
    have : ∀ off dq xs, Timeless (osBytes (GF := GF) p off dq xs) := fun _ _ _ => by
      unfold osBytes bytesG; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)
    unfold osSlot; infer_instance
  unfold pagesInv
  infer_instance

section lemmas
variable (B : BNs) (N : Namespace) (p : GoString) (E : CoPset) (hE : ↑(pagesN N) ⊆ E)
include hE

/-- `beginTx`, under `metalock` (`metaR`'s `cur`) and `Pm rfrac` (its `map` share and `mtok`):
register the reader `k` (its `fltx` fragment, inserted by the caller in `metaR`'s auth) with the
view of `C` at the mapping, borrowing `rq` of each of its slots and depositing `mtok rfrac`. -/
theorem store_register (C : CommitSt) (b : Loc) (l k : Nat) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half (some (b, l) : MapSt) ∗ ghostVar B.mtok sync.rfrac () ∗
      k ↪[B.fltx] (W64 (C.txid : Int)) ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half (some (b, l) : MapSt) ∗
      k ↪[B.rds] (⟨View.ofC b C⟩ : RdInfo) ∗ viewCells rq (View.ofC b C) := by
  sorry

/-- `removeTx`, before `RUnlock`: deregister the reader `k`, its cells back; the deposits
returned. -/
theorem store_deregister (k : Nat) (r : RdInfo) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ k ↪[B.rds] r ∗ viewCells rq r.v ⊢
    |={E}=> ghostVar B.mtok sync.rfrac () ∗ k ↪[B.fltx] (W64 (r.v.txid : Int)) := by
  sorry

/-- The writer's begin (after `store_release`): its txid the next, its base view (`C`'s at the
mapping) borrowed at `wq`. -/
theorem store_wbegin (C : CommitSt) (b : Loc) (l : Nat) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗ ghostVar B.wv (1 : Qp).half wIdle ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      ghostVar B.wv (1 : Qp).half ((some (View.ofC b C), some (C.txid + 1), false, true) : WSt) ∗
      viewCells wq (View.ofC b C) := by
  sorry

/-- The remap: the writer's view returned (parked) before `munmap`. -/
theorem store_wreturn (v : View) (w : Option Nat) (pb : Bool) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗
      ghostVar B.wv (1 : Qp).half ((some v, w, pb, true) : WSt) ∗ viewCells wq v ⊢
    |={E}=> ghostVar B.wv (1 : Qp).half ((some v, w, pb, false) : WSt) := by
  sorry

/-- The remap: the parked view re-borrowed on the new mapping's base. -/
theorem store_wborrow (v : View) (w : Option Nat) (pb : Bool) (b : Loc) (l : Nat) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗
      ghostVar B.wv (1 : Qp).half ((some v, w, pb, false) : WSt) ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ⊢
    |={E}=> ghostVar B.wv (1 : Qp).half ((some { v with base := b }, w, pb, true) : WSt) ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      viewCells wq { v with base := b } := by
  sorry

/-- The writer's `close` (any path): its view returned (if lent), no live writer; published, or
nothing pending for it. -/
theorem store_wclose (v : View) (w : Nat) (pb wl : Bool) (fl : FLPg)
    (hp : pb = true ∨ fl.pending !! W64 (w : Int) = none) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗
      ghostVar B.wv (1 : Qp).half ((some v, some w, pb, wl) : WSt) ∗
      (if wl then viewCells wq v else iprop(emp)) ∗ ghostVar B.fl (1 : Qp).half fl ⊢
    |={E}=> ghostVar B.wv (1 : Qp).half wIdle ∗ ghostVar B.fl (1 : Qp).half fl := by
  sorry

/-- `Free(w, p)` of `n` slots from `id` by the live writer before its publish: a page of the
current tree, or the old synced freelist page, whose slots then move `W → store` (F4.5). -/
theorem store_free (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt) (w : Nat) (id : w64)
    (n : Nat) (pg : Nat → List w8) (hw : ws.2.1 = some w) (hpub : ws.2.2.1 = false)
    (hcan : fl.canFree (W64 (w : Int)) id n) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ws ∗
      ((⌜∃ q, C.pages !! id.toNat = some q ∧ 1 + pageOverflow q = n⌝) ∨
        (⌜C.flpg = some id.toNat⌝ ∗ slotsOwn ms p (List.range' id.toNat n) pg)) ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half (fl.freePages (W64 (w : Int)) id n) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws := by
  sorry

/-- `Allocate` by the live writer: the ids leave the free list (their slots are `W` slots
already). -/
theorem store_alloc (fl : FLPg) (ws : WSt) (w : Nat) (r : w64) (n : Nat)
    (hw : ws.2.1 = some w) (ha : fl.canAlloc r n) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.wv (1 : Qp).half ws ⊢
    |={E}=> ghostVar B.fl (1 : Qp).half (fl.alloc (W64 (w : Int)) r n) ∗
      ghostVar B.wv (1 : Qp).half ws := by
  sorry

/-- `ReleasePendingPages` with no live writer, under `metalock` (`metaR`'s `F`, whose values are
`readonlyTXIDs` `ro`): the released slots move `store → W`, with their cells and bytes. -/
theorem store_release (C : CommitSt) (fl : FLPg) (ms : MapSt) (F : GMap Nat w64)
    (ro : List w64) (hro : ro.Perm (F.toList.map Prod.snd)) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half wIdle ∗ ghostMapAuth B.fltx 1 F ⊢
    |={E}=> ∃ (S : List Nat) (bs : Nat → List w8),
      ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half (fl.releasePending ro) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half wIdle ∗
      ghostMapAuth B.fltx 1 F ∗ slotsOwn ms p S bs ∗
      ⌜∀ s, s ∈ S ↔ s ∈ slotsOf C fl ∧ s ∉ slotsOf C (fl.releasePending ro)⌝ := by
  sorry

/-- **The commit point** (U10): the committed state moves `C → C'` (with `metaR`'s half and the
writer's quarter of `cur`), the new tree's slots `S` move `W → store` with their bytes; the
writer has published. The side conditions are spill's post (design §4.2). -/
theorem store_publish (C C' : CommitSt) (fl : FLPg) (ms : MapSt) (v : View) (w : Nat)
    (wl : Bool) (S : List Nat) (bs : Nat → List w8)
    (ht : C'.txid = w) (hmeta : C'.metaOk) (htree : treeOK C')
    (hdrop : ∀ s ∈ treeSlots C, s ∉ treeSlots C' → s ∈ pendSlots fl)
    (hS : ∀ s, s ∈ S ↔ s ∈ treeSlots C' ∧ s ∉ slotsOf C fl)
    (hbytes : ∀ id pg, C'.pages !! id = some pg → C.pages !! id = some pg ∨
      ((∀ j < 1 + pageOverflow pg, id + j ∈ S) ∧
        pg = (List.range' id (1 + pageOverflow pg)).flatMap bs))
    (hfl : flBelow fl C' (some w)) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ((some v, some w, false, wl) : WSt) ∗ slotsOwn ms p S bs ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half C' ∗ ghostVar B.cur (1 : Qp).half.half C' ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ((some v, some w, true, wl) : WSt) := by
  sorry

/-- `freelist.Rollback(w)` by the live writer before its publish: `w`'s pending pages are not
pending; slots leaving the store (B3: a freed old synced freelist page) move `store → W`. -/
theorem store_rollback (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt) (w : Nat)
    (hw : ws.2.1 = some w) (hpub : ws.2.2.1 = false) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ws ⊢
    |={E}=> ∃ (S : List Nat) (bs : Nat → List w8),
      ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half (fl.rollback (W64 (w : Int))) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ∗ slotsOwn ms p S bs ∗
      ⌜∀ s, s ∈ S ↔ s ∈ slotsOf C fl ∧ s ∉ slotsOf C (fl.rollback (W64 (w : Int)))⌝ := by
  sorry

/-- `Reload`/`NoSyncReload`: the free ids rebuilt from `W` slots below the high-water mark. -/
theorem store_reload (C : CommitSt) (fl : FLPg) (ids : List w64)
    (hids : ∀ x ∈ ids, 2 ≤ x.toNat ∧ x.toNat < C.hwm ∧ x.toNat < 2 ^ 62 ∧
      (x.toNat ∉ slotsOf C fl ∨ x ∈ fl.pendingIds)) (hnd : ids.Nodup) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half (fl.reload ids) := by
  iintro ⟨#Hinv, Hcur, Hfl⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, Hcur', Hfl', Hmap', Hwv, Hrds, Hdep, Hcells, Hos, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  subst hC hfl
  imod ghostVar_update_halves (σ.fl.reload ids) B.fl σ.fl σ.fl $$ Hfl Hfl' with ⟨Hfl, Hfl'⟩
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv Hrds Hdep Hcells Hos Hml] with _
  · inext
    iexists (σ.reload ids)
    have e1 : storeCells (GF := GF) (σ.reload ids) = storeCells σ := rfl
    have e2 : metaLend (GF := GF) B (σ.reload ids) = metaLend B σ := rfl
    rw [e1, e2]
    iframe
    ipureintro
    exact storeOK_reload σ ids Hok hids hnd
  imodintro; iframe

/-- `munmap` (a remap, `Close`), with `Pm 1` (`mtok 1`, its `map` quarter) and the writer's view
parked: every store cell comes out at the client half, and the meta lend quarter. -/
theorem store_gather (C : CommitSt) (fl : FLPg) (b : Loc) (l : Nat) (ws : WSt)
    (hwl : ws.2.2.2 = false) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      ghostVar B.map (1 : Qp).half.half (some (b, l) : MapSt) ∗ ghostVar B.mtok 1 () ∗
      ghostVar B.wv (1 : Qp).half ws ⊢
    |={E}=> ∃ bs : Nat → List w8,
      ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.map (1 : Qp).half (none : MapSt) ∗ ghostVar B.map (1 : Qp).half.half (none : MapSt) ∗
      ghostVar B.mtok 1 () ∗ ghostVar B.wv (1 : Qp).half ws ∗
      ([∗list] s ∈ slotsOf C fl,
        bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s)) ∗
      metaCellsQ (1 : Qp).half.half (some (b, l)) C := by
  sorry

/-- `mmap` (a remap): the new mapping's store cells in, holding the page cache's bytes (the
caller read them with OsFs's `osCell_agree`), and the meta lend quarter. -/
theorem store_carve (C : CommitSt) (fl : FLPg) (b : Loc) (l : Nat) (ws : WSt)
    (bs : Nat → List w8) (hl : ∀ s ∈ slotsOf C fl, s < l / 4096) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half (none : MapSt) ∗
      ghostVar B.map (1 : Qp).half.half (none : MapSt) ∗ ghostVar B.mtok 1 () ∗
      ghostVar B.wv (1 : Qp).half ws ∗
      ([∗list] s ∈ slotsOf C fl,
        bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s)) ∗
      metaCellsQ (1 : Qp).half.half (some (b, l)) C ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      ghostVar B.map (1 : Qp).half.half (some (b, l) : MapSt) ∗ ghostVar B.mtok 1 () ∗
      ghostVar B.wv (1 : Qp).half ws := by
  sorry

/-- `beginTx`'s `t.init` under `metalock` and `Pm rfrac`: the reader deposits `mlk` and
`mtok (rfrac/2)` and borrows the meta cells' quarter. -/
theorem meta_borrow (C : CommitSt) (ms : MapSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.mlk 1 () ∗
      ghostVar B.mtok sync.rfrac.half () ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half ms ⊢
    |={E}=> metaCellsQ (1 : Qp).half.half ms C ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half ms := by
  sorry

/-- The reader gives the meta cells' quarter back and gets its deposits. -/
theorem meta_return (C : CommitSt) (ms : MapSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ metaCellsQ (1 : Qp).half.half ms C ∗
      ghostVar B.cur (1 : Qp).half C ∗ ghostVar B.map sync.rfrac.half.half ms ⊢
    |={E}=> ghostVar B.mlk 1 () ∗ ghostVar B.mtok sync.rfrac.half () ∗
      ghostVar B.cur (1 : Qp).half C ∗ ghostVar B.map sync.rfrac.half.half ms := by
  sorry

/-- `writeMeta`, holding `metalock` (`mlk`): the writer takes the meta cells' quarter
(`out := true`). -/
theorem meta_take (C : CommitSt) (ms : MapSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.out (1 : Qp).half false ∗
      ghostVar B.mlk 1 () ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half ms ⊢
    |={E}=> metaCellsQ (1 : Qp).half.half ms C ∗ ghostVar B.out (1 : Qp).half true ∗
      ghostVar B.mlk 1 () ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half ms := by
  iintro ⟨#Hinv, Hout, Hmlk, Hcur, Hmap⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, Hcur', Hfl, Hmap', Hwv, Hrds, Hdep, Hcells, Hos, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  subst hC hms
  unfold metaLend
  icases Hml with (⟨Hm, Hout'⟩ | Hout' | ⟨Hout', Hmlk', -⟩)
  · imod ghostVar_update_halves true B.out false false $$ Hout Hout' with ⟨Hout, Hout'⟩
    imod Hclose $$ [Hcur' Hfl Hmap' Hwv Hrds Hdep Hcells Hos Hout'] with _
    · inext; iexists σ; iframe
      ipureintro; exact Hok
    imodintro; iframe
  · icombine Hout Hout' gives % ⟨_, hb⟩; cases hb
  · icombine Hmlk Hmlk' gives % ⟨hq, _⟩
    exfalso
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    grind

/-- The writer puts the meta cells' quarter back, holding the current committed state's metas
(after `store_publish`, or unchanged). -/
theorem meta_put (C : CommitSt) (ms : MapSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.out (1 : Qp).half true ∗
      metaCellsQ (1 : Qp).half.half ms C ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half ms ⊢
    |={E}=> ghostVar B.out (1 : Qp).half false ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half ms := by
  iintro ⟨#Hinv, Hout, Hm, Hcur, Hmap⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, Hcur', Hfl, Hmap', Hwv, Hrds, Hdep, Hcells, Hos, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  subst hC hms
  unfold metaLend
  icases Hml with (⟨-, Hout'⟩ | Hout' | ⟨Hout', -, -⟩)
  · icombine Hout Hout' gives % ⟨_, hb⟩; cases hb
  · imod ghostVar_update_halves false B.out true true $$ Hout Hout' with ⟨Hout, Hout'⟩
    imod Hclose $$ [Hcur' Hfl Hmap' Hwv Hrds Hdep Hcells Hos Hout' Hm] with _
    · inext; iexists σ; iframe
      isplitl; · ileft; iframe
      ipureintro; exact Hok
    imodintro; iframe
  · icombine Hout Hout' gives % ⟨_, hb⟩; cases hb

end lemmas

end store

end bbolt
end EtcdGrove
end Perennial
