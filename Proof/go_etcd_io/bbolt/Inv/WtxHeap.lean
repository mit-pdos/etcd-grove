/-
The writer's heap at a fraction (U0a of `notes/bbolt-proof-plan.md`; design §3.10, §3.13): the
old `ownWriteTxG` (`old/bbolt/.../WriteTxPred.lean`) with every points-to at `dq`, over the live
and dead objects (A3), the handles' `FillPercent` fields beside their points-tos (`fills`, F3)
and the root bucket's (`rootFill`, B6.5).

A slice the writer keeps is in the view (`Src.view`: a pure fact), or persistent heap bytes
(`Src.own`: `↦*□`, the cloned keys and `Put`'s values), or stale. A live object's slices carry
their facts; a dead object keeps only its points-tos. A bucket's `page` field is read only while
it is view-backed (`PageSt.view`, N2).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Store
public import Proof.go_etcd_io.bbolt.Model.LTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The transaction's root bucket: its field `root`. -/
def txRoot (tx : Loc) : Loc := structFieldRef Tx go!"root" tx

/-- A kept slice and its source (see the module doc). -/
def srcOwn (v : View) (s : GoSlice) (src : Src) (bs : List w8) : IProp GF :=
  match src with
  | .view => iprop(⌜inViewAt v s bs⌝)
  | .own _ => iprop(s ↦*□ bs)
  | .stale => iprop(True)

omit hos in
/-- A kept slice's source is persistent (a pure fact, persistent bytes, or nothing). -/
instance srcOwn_persistent (v : View) (s : GoSlice) (src : Src) (bs : List w8) :
    Persistent (srcOwn (GF := GF) v s src bs) := by
  cases src <;> unfold srcOwn <;> infer_instance

/-- The inode `it` is the entry `w` (its slices' facts only for a live node). -/
def wOwn (v : View) (live : Bool) (it : Inode) (w : WEntry) : IProp GF :=
  iprop(⌜it.flags' = w.flags ∧ it.pgid' = w.pgid⌝ ∗
    if live then srcOwn v it.key' w.ks w.key ∗ srcOwn v it.value' w.vs w.value else emp)

/-- A bucket's inline page, as its `page` field's status says (N2). -/
def pageOwn (v : View) (B : BRec) : IProp GF :=
  match B.pst with
  | .view => iprop(⌜inViewLoc v B.bv.page' B.ipg⌝)
  | _ => match B.isrc with
    | .own _ => if B.bv.page' = null then iprop(emp) else bytesPointsto B.bv.page' DFrac.discard B.ipg
    | _ => iprop(emp)

/-- **An object of the writer's heap** at `dq` (a bucket: its fields but `FillPercent`, its
header, its maps, its page; a node: its struct, inodes, children and key), live (with its slices'
facts on the view `v`) or dead. A bucket's `tx` field is persistent but the root bucket's (U0b:
`boltBkt` holds a handle's `↦□`; `Tx.close` writes the root bucket whole). A dead node keeps only
its struct (U8 fix: `rebalance`'s root collapse gives the collapsed child's `inodes` and
`children` to the root, so its slices are not its own; keeping its location an object keeps it
out of the registry's fresh locations, `nlocOK`). A node owns its `inodes`' capacity unless it
is a piece of `node.split` other than the last (`NRec.capOwn`, U9a fix). -/
def objOwn (v : View) (l : Loc) (dq : DFrac) : Bool → WObj → IProp GF
  | live, .bkt B => iprop(
      l.[Bucket, go!"InBucket"] ↦{dq} B.bv.InBucket' ∗
      (if l = B.bv.tx'.[Tx, go!"root"] then l.[Bucket, go!"tx"] ↦{dq} B.bv.tx'
       else l.[Bucket, go!"tx"] ↦□ B.bv.tx') ∗
      l.[Bucket, go!"buckets"] ↦{dq} B.bv.buckets' ∗ l.[Bucket, go!"page"] ↦{dq} B.bv.page' ∗
      l.[Bucket, go!"rootNode"] ↦{dq} B.bv.rootNode' ∗ l.[Bucket, go!"nodes"] ↦{dq} B.bv.nodes' ∗
      B.bv.InBucket' ↦{dq} B.ib ∗ B.bv.nodes' ↦${dq} B.nm ∗ B.bv.buckets' ↦${dq} B.bm ∗
      (if live then pageOwn v B else emp))
  | true, .node _ r => iprop(
      l ↦{dq} r.nv ∗ r.nv.inodes' ↦*{dq} r.ins ∗
      (if r.capOwn then ownSliceCap Inode r.nv.inodes' dq else emp) ∗
      ([∗list] it;w ∈ r.ins;r.ws, wOwn v true it w) ∗
      r.nv.children' ↦*{dq} r.cs ∗ ownSliceCap Loc r.nv.children' dq ∗
      (if true ∧ r.nv.key' ≠ slice.nil then srcOwn v r.nv.key' r.ksrc r.key else emp))
  | false, .node _ r => iprop(l ↦{dq} r.nv)

/-- The transaction's fields but `db`, `stats` and `root`, its meta copy, and its page cache
`pages` with the buffers. -/
def txFields (tx : Loc) (dq : DFrac) (X : WX) : IProp GF :=
  iprop(tx.[Tx, go!"writable"] ↦{dq} X.t.t.writable' ∗ tx.[Tx, go!"managed"] ↦{dq} X.t.t.managed' ∗
    tx.[Tx, go!"meta"] ↦{dq} X.t.t.meta' ∗ tx.[Tx, go!"pages"] ↦{dq} X.t.t.pages' ∗
    tx.[Tx, go!"commitHandlers"] ↦{dq} X.t.t.commitHandlers' ∗
    tx.[Tx, go!"WriteFlag"] ↦{dq} X.t.t.WriteFlag' ∗
    X.t.t.meta' ↦{dq} X.t.mv ∗ X.t.t.pages' ↦${dq} X.t.pm ∗
    ([∗map] id ↦ pl ∈ X.t.pm, ∃ bs, ⌜X.t.bufs !! id = some bs⌝ ∗ bytesPointsto pl dq bs))

/-- The root bucket's `FillPercent` (not a handle; `newBucket` sets `0.5`), non-NaN (B6.5). -/
def rootFill (tx : Loc) (dq : DFrac) : IProp GF :=
  iprop(∃ f : w64, ⌜¬ float64IsNaN f⌝ ∗ (tx.[Tx, go!"root"]).[Bucket, go!"FillPercent"] ↦{dq} f)

/-- **Every handle's `FillPercent`** at `dq`, non-NaN, its value beside its points-to (F3). -/
def fills (H : GMap Loc (GoString × Nat)) (dq : DFrac) : IProp GF :=
  iprop([∗map] b ↦ _x ∈ H, ∃ f : w64, ⌜¬ float64IsNaN f⌝ ∗ b.[Bucket, go!"FillPercent"] ↦{dq} f)

/-- **The writer's heap's facts** (`wtxHeap_heapOK` reads them): the root bucket's location, a
node in at most one bucket (`objsDisj`), every bucket's `tx` field the transaction, and no node
its own parent (`n.parent` and `n` are two objects: `nextSibling`, `prevSibling`) (U8 fixes),
every registered node a node object (batch 8, moved from `nlocOK`: a fresh location is
unregistered, for `Bucket.node`'s registry insert), and every bucket the root bucket or a
handle's (batch 20 item 5: its `FillPercent` is `rootFill`'s or `fills`'). -/
def heapOK (tx : Loc) (X : WX) : Prop :=
  X.rl = txRoot (GF := GF) tx ∧ objsDisj X.t ∧
  (∀ bl B, X.t.bs !! bl = some B → B.bv.tx' = tx) ∧
  (∀ bl B n r, X.t.bs !! bl = some B → B.ns !! n = some r → r.nv.parent' ≠ n) ∧
  (∀ n y, X.nloc !! n = some y → (X.t.objs !! n).isSome) ∧
  (∀ bl B, X.t.bs !! bl = some B → bl = X.rl ∨ (X.handles !! bl).isSome)

/-- **The writer's heap** at `dq` (design §3.13): its nodes (`objs`, live in `live`) and, apart,
its buckets (`bobjs`, live in `liveB`; batch 14). -/
def wtxHeap (tx : Loc) (dq : DFrac) (X : WX) : IProp GF :=
  iprop(⌜heapOK (GF := GF) tx X⌝ ∗ txFields tx dq X ∗ rootFill tx dq ∗
    ([∗map] l ↦ o ∈ X.t.objs, objOwn X.v l dq (decide (l ∈ X.live)) o) ∗
    [∗map] bl ↦ B ∈ X.t.bobjs, objOwn X.v bl dq (decide (bl ∈ X.liveB)) (.bkt B))

omit go_gctx hos sem in
/-- An inserted map still has every key it had (for `heapOK`'s registry clause). -/
theorem isSome_insert_of {V : Type} (m : GMap Loc V) (k j : Loc) (v : V) (h : (m !! j).isSome) :
    ((m.insert k v) !! j).isSome := by
  by_cases hk : k = j
  · subst hk; rw [GMap.lookup_insert]; rfl
  · rw [GMap.lookup_insert_ne _ _ hk]; exact h

omit hos in
open Iris.ProofMode in
/-- The heap's facts, read. -/
theorem wtxHeap_heapOK (tx : Loc) (dq : DFrac) (X : WX) :
    wtxHeap (GF := GF) tx dq X ⊢ ⌜heapOK (GF := GF) tx X⌝ := by
  unfold wtxHeap
  iintro ⟨%H, -⟩
  ipureintro; exact H

/-! ## Remaps: views become stale -/

/-- A source after a remap. -/
def Src.unview : Src → Src
  | .view => .stale
  | s => s

/-- A bucket after a remap: its view-backed page stale (N2), and its source too (batch 9: a page
in the old mapping has no bytes after it, whatever its source). -/
def BRec.unview (B : BRec) : BRec :=
  { B with isrc := if B.pst = .view then .stale else B.isrc.unview,
           pst := if B.pst = .view then .stale else B.pst,
           ns := B.ns.fmap fun r => { r with ws := r.ws.map fun w =>
             { w with ks := w.ks.unview, vs := w.vs.unview }, ksrc := r.ksrc.unview } }

/-- An entry after a remap. -/
def WEntry.unview (w : WEntry) : WEntry := { w with ks := w.ks.unview, vs := w.vs.unview }

/-- A node's record after a remap (moved from U4's `Mmap/Rebase`, batch 14). -/
def NRec.unview (r : NRec) : NRec := { r with ws := r.ws.map WEntry.unview, ksrc := r.ksrc.unview }

/-- An object after a remap. -/
def WObj.unview : WObj → WObj
  | .bkt B => .bkt B.unview
  | .node bl r => .node bl { r with ws := r.ws.map fun w =>
      { w with ks := w.ks.unview, vs := w.vs.unview }, ksrc := r.ksrc.unview }

/-- `X` after a remap to the base `b`: the view re-based, every view source stale. -/
def WX.rebase (X : WX) (b : Loc) : WX :=
  { X with v := { X.v with base := b },
           t := { X.t with bs := X.t.bs.fmap BRec.unview,
                           dead := X.t.dead.fmap fun p => (p.1, p.2.unview),
                           deadB := X.t.deadB.fmap BRec.unview } }

/-- **`dereference`'s coverage contract** (design §4.2, over the live nodes, A3): no live
node's entry or key is a view slice. (A bucket's `page` is outside it, N2.) -/
def derefOK (X : WX) : Prop :=
  ∀ l o, X.t.objs !! l = some o → l ∈ X.live →
    match o with
    | .node _ r => (∀ w ∈ r.ws, w.ks ≠ .view ∧ w.vs ≠ .view) ∧ r.ksrc ≠ .view
    | .bkt _ => True

/-! ## Lemma statements (U5, U4, U8, U9) -/

theorem wtxHeap_fractional (tx : Loc) (X : WX) :
    Fractional (fun q => wtxHeap (GF := GF) tx (DFrac.own q) X) := by
  sorry

omit hos in
open Iris.ProofMode in
theorem fills_fractional (H : GMap Loc (GoString × Nat)) :
    Fractional (fun q => fills (GF := GF) H (DFrac.own q)) := by
  have hel : ∀ b : Loc, Fractional (fun q : Qp => iprop(∃ f : w64, ⌜¬ float64IsNaN f⌝ ∗
      b.[Bucket, go!"FillPercent"] ↦{DFrac.own q} f : IProp GF)) := by
    intro b
    have hf : ∀ f : w64, Fractional (fun q : Qp =>
        (b.[Bucket, go!"FillPercent"] ↦{DFrac.own q} f : IProp GF)) := fun f =>
      fractional_of_dfractional (h := inferInstance) _
    refine ⟨fun p q => ⟨?_, ?_⟩⟩
    · iintro ⟨%f, %Hn, Hp⟩
      icases ((hf f).fractional p q).1 $$ Hp with ⟨H1, H2⟩
      isplitl [H1]
      · iexists f; iframe; ipureintro; exact Hn
      · iexists f; iframe; ipureintro; exact Hn
    · iintro ⟨⟨%f, %Hn, H1⟩, ⟨%g, %Hg, H2⟩⟩
      icombine H1 H2 gives %He
      obtain ⟨-, rfl⟩ := He
      iexists f
      isplitr
      · ipureintro; exact Hn
      iapply ((hf f).fractional p q).2
      iframe
  have hel' : ∀ (b : Loc) (_x : GoString × Nat), Fractional (fun q : Qp => iprop(∃ f : w64,
      ⌜¬ float64IsNaN f⌝ ∗ b.[Bucket, go!"FillPercent"] ↦{DFrac.own q} f : IProp GF)) :=
    fun b _ => hel b
  unfold fills
  exact fractional_bigSepM (Ψ := fun b _ q => iprop(∃ f : w64, ⌜¬ float64IsNaN f⌝ ∗
      b.[Bucket, go!"FillPercent"] ↦{DFrac.own q} f : IProp GF))

omit hos in
open Iris.ProofMode in
/-- An object's facts can be dropped (live to dead; a node keeps only its struct). U8. -/
theorem objOwn_weaken (v : View) (l : Loc) (dq : DFrac) (b b' : Bool) (o : WObj)
    (h : b' = true → b = true) :
    objOwn (GF := GF) v l dq b o ⊢ objOwn v l dq b' o := by
  cases b' with
  | true => rw [h rfl]
  | false =>
    cases b with
    | false => exact .rfl
    | true =>
      cases o with
      | bkt B =>
        unfold objOwn
        iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, -⟩
        dsimp only
        iframe
        simp only [Bool.false_eq_true, ↓reduceIte]; iempintro
      | node bl r =>
        unfold objOwn
        iintro ⟨H1, -⟩
        iexact H1

omit hos in
open Iris.ProofMode in
/-- A node's struct, out of its object (live or dead), and back. -/
theorem objOwn_node_ptr_acc (v : View) (l : Loc) (dq : DFrac) (b : Bool) (bl : Loc) (r : NRec) :
    objOwn (GF := GF) v l dq b (.node bl r) ⊢
      l ↦{dq} r.nv ∗ (l ↦{dq} r.nv -∗ objOwn v l dq b (.node bl r)) := by
  cases b with
  | true =>
    unfold objOwn
    dsimp only
    iintro ⟨Hl, Hr⟩
    iframe Hl
    iintro Hl
    iframe
  | false =>
    unfold objOwn
    dsimp only
    iintro Hl
    iframe Hl
    iintro Hl
    iexact Hl

open Iris.ProofMode in
/-- An object goes dead (spill's spilled children, rebalance's removed nodes, `DeleteBucket`'s
bucket and nodes): its facts are dropped, its points-tos kept. U8. -/
theorem wtxHeap_kill (tx : Loc) (dq : DFrac) (X : WX) (l : Loc) :
    wtxHeap (GF := GF) tx dq X ⊢ wtxHeap tx dq { X with live := X.live.delete l } := by
  unfold wtxHeap txFields
  iintro ⟨%Hrl, Hf, Hrf, Hm, Hb⟩
  iframe
  isplitr
  · ipureintro; exact Hrl
  iapply (BigSepM.bigSepM_mono_of_forall ?_) $$ Hm
  intro k o
  apply objOwn_weaken
  intro h
  simp only [decide_eq_true_eq, GMap.mem_iff, GMap.lookup_delete_iff] at h ⊢
  split at h <;> simp_all

/-- `X` with the node `l` (record `r`) added to bucket `bl` (record `B`), live. -/
def WX.addNode (X : WX) (bl l : Loc) (B : BRec) (r : NRec) : WX :=
  { X with t := { X.t with bs := X.t.bs.insert bl { B with ns := B.ns.insert l r } },
           live := X.live.insert l () }

-- `wtxHeap_node_insert`: U7's `Write/Heap.lean` (proved; batch 8).

-- `wtxHeap_rebase` (the remap): U4's `Mmap/Rebase.lean` (proved; batch 9).

end heap

end bbolt
end EtcdGrove
end Perennial
