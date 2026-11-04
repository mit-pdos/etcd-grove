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
`boltBkt` holds a handle's `↦□`; `Tx.close` writes the root bucket whole). -/
def objOwn (v : View) (l : Loc) (dq : DFrac) (live : Bool) : WObj → IProp GF
  | .bkt B => iprop(
      l.[Bucket, go!"InBucket"] ↦{dq} B.bv.InBucket' ∗
      (if l = B.bv.tx'.[Tx, go!"root"] then l.[Bucket, go!"tx"] ↦{dq} B.bv.tx'
       else l.[Bucket, go!"tx"] ↦□ B.bv.tx') ∗
      l.[Bucket, go!"buckets"] ↦{dq} B.bv.buckets' ∗ l.[Bucket, go!"page"] ↦{dq} B.bv.page' ∗
      l.[Bucket, go!"rootNode"] ↦{dq} B.bv.rootNode' ∗ l.[Bucket, go!"nodes"] ↦{dq} B.bv.nodes' ∗
      B.bv.InBucket' ↦{dq} B.ib ∗ B.bv.nodes' ↦${dq} B.nm ∗ B.bv.buckets' ↦${dq} B.bm ∗
      (if live then pageOwn v B else emp))
  | .node _ r => iprop(
      l ↦{dq} r.nv ∗ r.nv.inodes' ↦*{dq} r.ins ∗ ownSliceCap Inode r.nv.inodes' dq ∗
      ([∗list] it;w ∈ r.ins;r.ws, wOwn v live it w) ∗
      r.nv.children' ↦*{dq} r.cs ∗ ownSliceCap Loc r.nv.children' dq ∗
      (if live ∧ r.nv.key' ≠ slice.nil then srcOwn v r.nv.key' r.ksrc r.key else emp))

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

/-- **The writer's heap's facts** (`wtxHeap_heapOK` reads them): the root bucket's location, its
objects disjoint (`objsDisj`), and every bucket's `tx` field the transaction (U8 fixes). -/
def heapOK (tx : Loc) (X : WX) : Prop :=
  X.rl = txRoot (GF := GF) tx ∧ objsDisj X.t ∧
  (∀ bl B, X.t.bs !! bl = some B → B.bv.tx' = tx)

/-- **The writer's heap** at `dq` (design §3.13). -/
def wtxHeap (tx : Loc) (dq : DFrac) (X : WX) : IProp GF :=
  iprop(⌜heapOK (GF := GF) tx X⌝ ∗ txFields tx dq X ∗ rootFill tx dq ∗
    [∗map] l ↦ o ∈ X.t.objs, objOwn X.v l dq (decide (l ∈ X.live)) o)

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

/-- A bucket after a remap: its view-backed page stale (N2). -/
def BRec.unview (B : BRec) : BRec :=
  { B with isrc := B.isrc.unview, pst := if B.pst = .view then .stale else B.pst,
           ns := B.ns.fmap fun r => { r with ws := r.ws.map fun w =>
             { w with ks := w.ks.unview, vs := w.vs.unview }, ksrc := r.ksrc.unview } }

/-- An object after a remap. -/
def WObj.unview : WObj → WObj
  | .bkt B => .bkt B.unview
  | .node bl r => .node bl { r with ws := r.ws.map fun w =>
      { w with ks := w.ks.unview, vs := w.vs.unview }, ksrc := r.ksrc.unview }

/-- `X` after a remap to the base `b`: the view re-based, every view source stale. -/
def WX.rebase (X : WX) (b : Loc) : WX :=
  { X with v := { X.v with base := b },
           t := { X.t with bs := X.t.bs.fmap BRec.unview, dead := X.t.dead.fmap WObj.unview } }

/-- **`dereference`'s coverage contract** (design §4.2, over the live objects, A3): no live
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

theorem fills_fractional (H : GMap Loc (GoString × Nat)) :
    Fractional (fun q => fills (GF := GF) H (DFrac.own q)) := by
  sorry

omit hos in
open Iris.ProofMode in
/-- An object's facts can be dropped (live to dead). U8. -/
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
        iintro ⟨H1, H2, H3, Hws, H5, H6, -⟩
        dsimp only
        iframe
        isplitl [Hws]
        · iapply (BigSepL2.bigSepL2_mono_of_forall (Φ := fun _ it w => wOwn (GF := GF) v true it w)
            (Ψ := fun _ it w => wOwn (GF := GF) v false it w) ?_) $$ Hws
          intro _ it w
          unfold wOwn
          iintro ⟨%Hp, -⟩
          isplitr
          · ipureintro; exact Hp
          · simp only [Bool.false_eq_true, ↓reduceIte]; iempintro
        · simp only [Bool.false_eq_true, _root_.false_and, ↓reduceIte]; iempintro

open Iris.ProofMode in
/-- An object goes dead (spill's spilled children, rebalance's removed nodes, `DeleteBucket`'s
bucket and nodes): its facts are dropped, its points-tos kept. U8. -/
theorem wtxHeap_kill (tx : Loc) (dq : DFrac) (X : WX) (l : Loc) :
    wtxHeap (GF := GF) tx dq X ⊢ wtxHeap tx dq { X with live := X.live.delete l } := by
  unfold wtxHeap txFields
  iintro ⟨%Hrl, Hf, Hrf, Hm⟩
  iframe
  isplitr
  · ipureintro; exact Hrl
  iapply (BigSepM.bigSepM_mono_of_forall ?_) $$ Hm
  intro k o
  apply objOwn_weaken
  intro h
  simp only [decide_eq_true_eq, GMap.mem_iff, GMap.lookup_delete_iff] at h ⊢
  split at h <;> simp_all

/-- **The remap** (U4): after `dereference` (the coverage contract), the heap is the re-based
`X`'s; nothing of it reads the old mapping. -/
theorem wtxHeap_rebase (tx : Loc) (dq : DFrac) (X : WX) (b : Loc) (hcov : derefOK X) :
    wtxHeap (GF := GF) tx dq X ⊢ wtxHeap tx dq (X.rebase b) := by
  sorry

end heap

end bbolt
end EtcdGrove
end Perennial
