/-
A write transaction's objects (`WriteTxModel.lean`'s records) as resources.

`ownWriteTxG W txl T` owns, of the transaction at `txl`: its fields but `root` (`Tx_rest_root`),
its meta copy, its page cache and the buffers in it, and its buckets (`bktOwn`: the struct, the
`InBucket` header, the node and bucket caches, the inline page, the nodes: `nodeOwn`). The root
bucket is the transaction's field `root` (`txRoot txl`). Nothing in it depends on the view but
the pure facts of `Src.view` sources (`srcOwn`), so that once no source is the view, the same
resources stand over another view (a remap). It is what `Tx.allocate` and `dereference` need.

`wView W` is the view itself: the pages and the database field `data` at the
fraction `W.q`, the (persistent) `pageSize` and `logger` fields and half of the `freelist` field, held whole between operations.

`ownWriteTx W txl T` is the transaction between operations before `Commit`: both, with the
view's facts and the clean invariant (`txClean`).
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxModel
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.TxModel
public import Spec.go_etcd_io.bbolt.getDiscardLogger
public import Proof.go_etcd_io.bbolt.DBModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The slice `s` holds `bs`, from the source `src`. -/
def srcOwn (W : WView) (s : GoSlice) (src : Src) (bs : List w8) : IProp GF :=
  match src with
  | .view => iprop(⌜inViewAt W s bs⌝)
  | .own dq => iprop(s ↦*{dq} bs)
  | .stale => iprop(True)

/-- The inode `it` is the entry `w`. -/
def wOwn (W : WView) (it : Inode) (w : WEntry) : IProp GF :=
  iprop(⌜it.flags' = w.flags ∧ it.pgid' = w.pgid⌝ ∗ srcOwn W it.key' w.ks w.key ∗
    srcOwn W it.value' w.vs w.value)

/-- The node at `l` (record `r`). -/
def nodeOwn (W : WView) (l : Loc) (r : NRec) : IProp GF :=
  iprop(l ↦ r.nv ∗ r.nv.inodes' ↦* r.ins ∗ ownSliceCap Inode r.nv.inodes' (DFrac.own 1) ∗
    ([∗list] it;w ∈ r.ins;r.ws, wOwn W it w) ∗
    r.nv.children' ↦* r.cs ∗ ownSliceCap Loc r.nv.children' (DFrac.own 1) ∗
    (if r.nv.key' = slice.nil then iprop(True) else srcOwn W r.nv.key' r.ksrc r.key))

/-- The bytes of a bucket's inline page. -/
def pageOwn (W : WView) (B : BRec) : IProp GF :=
  if B.bv.page' = null then iprop(True) else
  match B.isrc with
  | .view => iprop(⌜inViewLoc W B.bv.page' B.ipg⌝)
  | .own dq => bytesPointsto B.bv.page' dq B.ipg
  | .stale => iprop(True)

/-- The bucket at `bl` (record `B`). -/
def bktOwn (W : WView) (bl : Loc) (B : BRec) : IProp GF :=
  iprop(bl ↦ B.bv ∗ B.bv.InBucket' ↦ B.ib ∗ B.bv.nodes' ↦$ B.nm ∗ B.bv.buckets' ↦$ B.bm ∗
    pageOwn W B ∗ [∗map] l ↦ r ∈ B.ns, nodeOwn W l r)

/-- The transaction's root bucket: its field `root`. -/
def txRoot (txl : Loc) : Loc := structFieldRef Tx go!"root" txl

/-- The fields of a `Tx` but `root`. -/
def Tx_rest_root (l : Loc) (dq : DFrac) (v : Tx) : IProp GF :=
  iprop("writable" ∷ structFieldRef Tx go!"writable" l ↦{dq} v.writable' ∗
    "managed" ∷ structFieldRef Tx go!"managed" l ↦{dq} v.managed' ∗
    "db" ∷ structFieldRef Tx go!"db" l ↦{dq} v.db' ∗
    "meta" ∷ structFieldRef Tx go!"meta" l ↦{dq} v.meta' ∗
    "pages" ∷ structFieldRef Tx go!"pages" l ↦{dq} v.pages' ∗
    "stats" ∷ structFieldRef Tx go!"stats" l ↦{dq} v.stats' ∗
    "commitHandlers" ∷ structFieldRef Tx go!"commitHandlers" l ↦{dq} v.commitHandlers' ∗
    "WriteFlag" ∷ structFieldRef Tx go!"WriteFlag" l ↦{dq} v.WriteFlag' ∗ ⌜l ≠ null⌝)

theorem Tx_split_root (l : Loc) (dq : DFrac) (v : Tx) :
    (l ↦{dq} v : IProp GF) ⊣⊢
      structFieldRef Tx go!"root" l ↦{dq} v.root' ∗ Tx_rest_root l dq v := by
  rw [typedPointsto_unseal_eq]
  simp only [TypedPointsto.typedPointstoDef, Tx_rest_root]
  constructor
  · iintro ⟨⟨Hwritable, Hmanaged, Hdb, Hmeta, Hroot, Hpages, Hstats, HcommitHandlers, HWriteFlag, -⟩, %Hn⟩
    iframe
    ipureintro; exact Hn
  · iintro ⟨Hroot, ⟨Hwritable, Hmanaged, Hdb, Hmeta, Hpages, Hstats, HcommitHandlers, HWriteFlag, %Hn⟩⟩
    iframe
    try (ipureintro; exact Hn)

/-- The transaction's resources (see the module doc). -/
def ownWriteTxG (W : WView) (txl : Loc) (T : WTx) : IProp GF :=
  iprop(Tx_rest_root txl (DFrac.own 1) T.t ∗ T.t.meta' ↦ T.mv ∗ T.t.pages' ↦$ T.pm ∗
    ([∗map] id ↦ p ∈ T.pm, ∃ bs, ⌜T.bufs !! id = some bs⌝ ∗ bytesPointsto p (DFrac.own 1) bs) ∗
    [∗map] bl ↦ B ∈ T.bs, bktOwn W bl B)

/-- The view (see the module doc). -/
def wView (W : WView) : IProp GF :=
  iprop(structFieldRef DB go!"data" W.dbl ↦{DFrac.own W.q} W.data ∗
    structFieldRef DB go!"pageSize" W.dbl ↦□ W64 (W.ps : Int) ∗
    structFieldRef DB go!"logger" W.dbl ↦□ W.lg ∗
    structFieldRef DB go!"freelist" W.dbl ↦{DFrac.own halfQ} W.fli ∗
    (globalAddr discardLogger ↦□ W.dl : IProp GF) ∗
    ⌜W.lg = interface.nil ∨ W.lg = discardIface W.dl⌝ ∗ pagesView W.data W.ps W.q W.pages)

/-- The clean invariant of the transaction at `txl` (its root bucket at `rl`; see
`WriteTxModel.lean`). -/
def txClean (W : WView) (txl rl : Loc) (T : WTx) : Prop :=
  T.t.writable' = true ∧ T.t.db' = W.dbl ∧ W.dbl ≠ null ∧ T.pm = ∅ ∧
  2 ≤ uint.nat T.mv.pgid' ∧ (T.bs !! rl).isSome ∧
  ∀ bl B, T.bs !! bl = some B → B.bv.tx' = txl ∧ bktClean W (uint.nat T.mv.pgid') bl B ∧
    ∀ name c, B.bm !! name = some c → (T.bs !! c).isSome

/-- The write transaction at `txl` between operations, before `Commit`. -/
def ownWriteTx (W : WView) (txl : Loc) (T : WTx) : IProp GF :=
  iprop(ownWriteTxG W txl T ∗ wView W ∗ ⌜viewOK W ∧ txClean W txl (structFieldRef Tx go!"root" txl) T⌝)

end own

end bbolt
end EtcdGrove
end Perennial
