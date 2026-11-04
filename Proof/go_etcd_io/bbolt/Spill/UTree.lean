/-
The spill's pure tree facts (U9e, `notes/bbolt-proof-plan.md`), part 7: **the unspilled tree**
(`uTree X bl P hwm n lo hi h F D N E`), what `node.spill` takes: the materialized subtree of node `n`
of bucket `bl`, not yet spilled, over the spill's page map `P` (the writer's buffers over the base
pages, `spP`) and high-water mark `hwm`. A leaf: its keys sorted within `[lo, hi)`, its nested
buckets' values `bvalS`; a branch (of at least two entries): each entry an unspilled child with
its own `uTree` (the child's bounds the entry's; not empty, U9j: `node.spill` reads a child's
`inodes[0]` in the sort and before `parent.put`; `rebalance` removed the empty nodes; its
children nodes of its own tree, no earlier spill's pieces: U9j, their kill in its spill is framed
by its nodes), or a finished subtree (`fTree`: an `sTree` from
its first key, the entry's), its other children spilled nodes (pieces). The indices: `h` the
height, `F` the base pages its nodes own (freed by the spill), `D` the slots it owns (its nodes'
pages and its finished subtrees' and nested buckets'), `N` its nodes, `E` its leaf entries in
order by data (`El`: flags, key, value; a finished subtree's its pages' `treeEls`).

The statement is independent of the slices' sources (only entries by data, `wDat`, appear), so it
is kept by `dereference`'s copies and a remap (`Spill/UTreeStep`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.STreeWrite
public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Model.TreeData

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section utree
variable [GooseExts]

/-- **The spill's page map**: the writer's buffers (`tx.pages`) over the base view's pages
(`spillC`'s). -/
def spP (X : WX) : Pages := X.bufPages ∪ X.v.pages

/-- The slots of the pages `S` in `P` (each page its extent; a missing page its own slot). -/
def pgSlots (P : Pages) (S : List Nat) : List Nat :=
  S.flatMap fun x => match P !! x with
    | some pg => List.range' x (1 + pageOverflow pg)
    | none => [x]

/-- A node's own page, if it has one (page id `0`: none): a base page of the view, readable by
`Tx.page` and freeable (`node.free`'s premises but the freelist's). -/
def ownPg (v : View) (pgid : w64) : Prop :=
  pgid ≠ W64 0 → ∃ pg, v.pages !! pgid.toNat = some pg ∧ 16 ≤ pg.length ∧
    pageId pg = pgid.toNat ∧ (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
    2 ≤ pgid.toNat ∧ pgid.toNat + (1 + pageOverflow pg) ≤ 2 ^ 62

/-- The base page a node owns (none for page id `0`). -/
def ownF (pgid : w64) : List Nat := if pgid = W64 0 then [] else [pgid.toNat]

/-- The slots of a node's own page. -/
def ownSl (v : View) (pgid : w64) : List Nat :=
  if pgid = W64 0 then [] else pgSlots v.pages [pgid.toNat]

/-- A leaf element by data: its flags, key and value. -/
abbrev El : Type := Nat × List w8 × List w8

/-- An entry's leaf element by data. -/
def wEl (w : WEntry) : El := (w.flags.toNat, w.key, w.value)

/-- **The leaf elements of the tree from `root`** (flags, key, value), in order: what the leaves
of a written tree hold (`treeEntries` without the flags). (U9g's, moved from `Spill/BktSpec`.) -/
def treeEls (P : Pages) (root : Nat) : List El :=
  (treeLeaves P root).flatMap fun pg =>
    (List.range (pageCount pg)).map fun i => (leafFlags pg i, leafKey pg i, leafValue pg i)

theorem treeEls_entries (P : Pages) (root : Nat) :
    (treeEls P root).map (fun e => (e.2.1, e.2.2)) = treeEntries P root := by
  unfold treeEls treeEntries leafEnts
  rw [List.map_flatMap]
  congr 1; funext pg
  rw [List.map_map]; rfl

/-- **A finished subtree** at page `id` whose first key is `k`: an `sTree` from `k`, its leaf
elements `E`. -/
def fTree (P : Pages) (hwm id : Nat) (k : List w8) (hi : Option (List w8)) (h : Nat)
    (S : List Nat) (E : List El) : Prop :=
  sTree P hwm id (some k) hi h S ∧
    (∃ pg, P !! id = some pg ∧ 0 < pageCount pg ∧ pageKey pg 0 = k) ∧ treeEls P id = E

/-- **An unspilled node** `n` (record `r`) of bucket `bl`, its keys within `[lo, hi)`: live, of its
bucket, not spilled, owning its inodes' capacity (`node.split`), its entries sorted, keys not
empty, each entry within `bboltEntryMax` (it fits a page), its own page (if any) a base page. -/
def uNode (X : WX) (bl n : Loc) (r : NRec) (lo hi : Option (List w8)) : Prop :=
  n ∈ X.live ∧ r.nv.bucket' = bl ∧ r.nv.spilled' = false ∧ r.capOwn = true ∧
  r.ins.length = r.ws.length ∧ wsSorted r.ws ∧
  (∀ w ∈ r.ws, keyIn lo hi w.key ∧ 0 < w.key.length ∧
    w.key.length + w.value.length ≤ bboltEntryMax) ∧
  ownPg X.v r.nv.pgid'

/-- **A spilled node** `c` of bucket `bl` (a piece of an earlier spill, in a branch's
children): `c.spill()` returns at once. Not empty (U9j: `node.spill` sorts its children by their
first keys, `inodes[0]`). -/
def spilledN (X : WX) (bl c : Loc) : Prop :=
  c ∈ X.live ∧ ∃ rc, X.node bl c = some rc ∧ rc.nv.bucket' = bl ∧ rc.nv.spilled' = true ∧
    rc.cs = [] ∧ 0 < rc.ws.length

/-- **An entry's descriptor** in an unspilled branch: its unspilled child (none for a finished
subtree), and the base pages, slots and nodes it owns. -/
structure UE where
  ch : Option Loc
  F : List Nat
  D : List Nat
  N : List Loc
  E : List El

mutual
/-- **The unspilled tree** (see the module doc). -/
inductive uTree (X : WX) (bl : Loc) (P : Pages) (hwm : Nat) :
    Loc → Option (List w8) → Option (List w8) → Nat → List Nat → List Nat → List Loc → List El →
      Prop
  | leaf (n : Loc) (r : NRec) (lo hi : Option (List w8)) (Sb : Nat → List Nat) :
      X.node bl n = some r → uNode X bl n r lo hi → r.nv.isLeaf' = true → r.cs = [] →
      (∀ i w, r.ws[i]? = some w → isBktFlag w.flags → bvalS P hwm w.value (Sb i)) →
      (∀ i w, r.ws[i]? = some w → ¬ isBktFlag w.flags → Sb i = []) →
      uTree X bl P hwm n lo hi 0 (ownF r.nv.pgid')
        (ownSl X.v r.nv.pgid' ++ (List.range r.ws.length).flatMap fun i => pgSlots P (Sb i)) [n]
        (r.ws.map wEl)
  | branch (n : Loc) (r : NRec) (lo hi : Option (List w8)) (h : Nat) (es : List UE) :
      X.node bl n = some r → uNode X bl n r lo hi → r.nv.isLeaf' = false → 2 ≤ r.ws.length →
      es.length = r.ws.length →
      (∀ i w e, r.ws[i]? = some w → es[i]? = some e → uEnt X bl P hwm n lo hi r.ws r.cs h i w e) →
      (es.filterMap UE.ch).Nodup →
      (∀ c ∈ r.cs, (∃ e ∈ es, e.ch = some c) ∨ spilledN X bl c) →
      r.cs.Nodup → (n :: es.flatMap UE.N).Nodup →
      (r.nv.pgid' = W64 0 → ∀ e ∈ es, e.ch = none) →
      uTree X bl P hwm n lo hi (h + 1) (ownF r.nv.pgid' ++ es.flatMap UE.F)
        (ownSl X.v r.nv.pgid' ++ es.flatMap UE.D) (n :: es.flatMap UE.N) (es.flatMap UE.E)

/-- **Entry `i` (`w`, descriptor `e`) of the unspilled branch `n`** (entries `ws`, children `cs`,
bounds `[lo, hi)`, children of height `h`): an unspilled child `c` (its page id and key the
entry's, its bounds the entry's), or a finished subtree at the entry's page, from its key. -/
inductive uEnt (X : WX) (bl : Loc) (P : Pages) (hwm : Nat) :
    Loc → Option (List w8) → Option (List w8) → List WEntry → List Loc → Nat → Nat → WEntry →
      UE → Prop
  | child (n : Loc) (lo hi : Option (List w8)) (ws : List WEntry) (cs : List Loc) (h i : Nat)
      (w : WEntry) (c : Loc) (rc : NRec) (F D : List Nat) (N : List Loc) (E : List El) :
      c ∈ cs → X.node bl c = some rc → rc.nv.parent' = n → rc.nv.pgid' = w.pgid →
      rc.key = w.key → rc.nv.key' ≠ slice.nil → 0 < rc.ws.length ∧ (∀ c' ∈ rc.cs, c' ∈ N) →
      uTree X bl P hwm c (childLo lo (wKey ws) i) (childHi hi (wKey ws) ws.length i) h F D N E →
      uEnt X bl P hwm n lo hi ws cs h i w ⟨some c, F, D, N, E⟩
  | fin (n : Loc) (lo hi : Option (List w8)) (ws : List WEntry) (cs : List Loc) (h i : Nat)
      (w : WEntry) (S : List Nat) (E : List El) :
      fTree P hwm w.pgid.toNat w.key (childHi hi (wKey ws) ws.length i) h S E →
      uEnt X bl P hwm n lo hi ws cs h i w ⟨none, [], pgSlots P S, [], E⟩
end

/-! ## The freelist and the slots -/

/-- **The slots `L` are owned** (by the trees being spilled, or kept): distinct, below the
high-water mark `hwm` and `2 ^ 62`, neither free nor pending; the freelist's ids distinct, below
the mark. An allocation (from the free ids, or at the mark) never returns an owned slot, and a
free of an owned page's slots (removed from `L`) can be done. -/
def slotInv (fl : FLPg) (hwm : Nat) (L : List Nat) : Prop :=
  L.Nodup ∧ (∀ s ∈ L, s < hwm ∧ s < 2 ^ 62 ∧ W64 (s : Int) ∉ fl.allIds) ∧
  fl.allIds.Nodup ∧ (∀ id ∈ fl.allIds, id.toNat < hwm)

/-- **The base pages `F` can be freed by the writer** `txid`: not in the page cache, not
allocated by it. -/
def spFree (X : WX) (fl : FLPg) (txid : w64) (F : List Nat) : Prop :=
  ∀ id ∈ F, X.t.pm !! W64 (id : Int) = none ∧ (fl.allocs !! W64 (id : Int)).getD 0 ≠ txid

/-- The slots allocated by the steps `st`, or at or above the mark `hwm`: the slots a spill may
add. -/
def newSlot (st : List FLStep) (hwm s : Nat) : Prop :=
  (∃ id n, FLStep.alloc id n ∈ st ∧ id.toNat ≤ s ∧ s < id.toNat + n) ∨ hwm ≤ s

/-! ## Records modulo sources (what `dereference` and a remap keep) -/

/-- **`r'` is `r` but its slices' sources**: the struct but the key slice (nil or not as before),
the entries by data, the inodes' count, the children, the key and the capacity. -/
def nodeSim (r r' : NRec) : Prop :=
  r'.nv = { r.nv with key' := r'.nv.key' } ∧ (r'.nv.key' = slice.nil ↔ r.nv.key' = slice.nil) ∧
  r'.ws.map wDat = r.ws.map wDat ∧ r'.ins.length = r.ins.length ∧ r'.cs = r.cs ∧
  r'.key = r.key ∧ r'.capOwn = r.capOwn

/-- **A bucket's record but its nodes and sources**: its struct, header, caches and inline page
bytes. -/
def bktSim (B B' : BRec) : Prop :=
  B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.nm = B.nm ∧ B'.bm = B.bm ∧ B'.ipg = B.ipg

/-- **The frame of a spill in bucket `bl`** from `X` to `X'`, the nodes `T` touched: the other
buckets' records modulo sources, `bl`'s struct, header and caches, its untouched nodes modulo
sources (live as before), and the transaction's root, handles, registry, live buckets, base pages
and txid unchanged; the buffers and page cache grown (old buffers kept), the mark not lower; every
object still one (U9h: a node fresh after a later step was fresh at the start). -/
def spFrame (X X' : WX) (bl : Loc) (T : List Loc) : Prop :=
  X'.rl = X.rl ∧ X'.handles = X.handles ∧ X'.nloc = X.nloc ∧ X'.liveB = X.liveB ∧
  X'.v.pages = X.v.pages ∧ X'.v.txid = X.v.txid ∧ X'.t.t = X.t.t ∧
  X'.t.mv.txid' = X.t.mv.txid' ∧ X.t.mv.pgid'.toNat ≤ X'.t.mv.pgid'.toNat ∧
  (∀ id bs, X.t.bufs !! id = some bs → X'.t.bufs !! id = some bs) ∧
  (∀ id p, X.t.pm !! id = some p → X'.t.pm !! id = some p) ∧
  (∀ bl', bl' ≠ bl → ∀ B, X.t.bs !! bl' = some B → ∃ B', X'.t.bs !! bl' = some B' ∧
    bktSim B B' ∧ ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) ∧
  (∀ bl', bl' ≠ bl → X.t.bs !! bl' = none → X'.t.bs !! bl' = none) ∧
  (∀ B, X.t.bs !! bl = some B → ∃ B', X'.t.bs !! bl = some B' ∧ bktSim B B' ∧
    ∀ l, l ∉ T → optRel nodeSim (B.ns !! l) (B'.ns !! l)) ∧
  (∀ l, l ∉ T → (∃ bl' B, X.t.bs !! bl' = some B ∧ (B.ns !! l).isSome) →
    (l ∈ X'.live ↔ l ∈ X.live)) ∧
  (∀ l, (X.t.objs !! l).isSome → (X'.t.objs !! l).isSome)

/-! ## What every step of the spill keeps -/

/-- **The spill's global state** (between `allocate`s; what `allocate` needs and what the writes
need): the writer's txid, the mark's pages inside the mapping, `allocate`'s premises
(`derefPre`, `liveFresh`, `liveReach`), the page cache's ids the buffers' and above
the base pages' slots, and the mark below `2 ^ 62`; (batch 37, U9l) every buffer's id below the
mark, not free in the writer side's freelist `fl` (so `allocate`'s new id is no buffer's, and
`spFrame` keeps the old buffers) and no page of the view (so the positions of a bucket the spill
frees, view pages, have no buffer: `Bucket.free`'s premise for an inlineable child). -/
def spG (X : WX) (txid : w64) (ml : Nat) (fl : FLPg) : Prop :=
  X.t.mv.txid' = txid ∧ X.t.mv.pgid'.toNat * 4096 ≤ ml ∧ derefPre X ∧ liveFresh X ∧
  liveReach X ∧
  (∀ id, (X.t.pm !! id).isSome ↔ (X.t.bufs !! id).isSome) ∧
  X.t.mv.pgid'.toNat < 2 ^ 62 ∧
  (∀ id, (X.t.bufs !! id).isSome →
    id.toNat < X.t.mv.pgid'.toNat ∧ id ∉ fl.free ∧ X.v.pages !! id.toNat = none)

end utree

end Spill

end bbolt
end EtcdGrove
end Perennial
