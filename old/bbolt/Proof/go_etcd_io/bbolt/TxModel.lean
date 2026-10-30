/-
A transaction's view of the database (the read path's database invariant).

`pagesView data ps q pages`: the transaction holds the fraction `q` of the mapped cells of each
page it can see (`pages`: page id ↦ the page's bytes, its overflow pages included), page `id`
being `id * ps` bytes after the mapping's start `data`. A read transaction's `q` is a share of
the mapping's caller half (`Proof/os/FileModel.lean`); how the DB hands them out and takes them
back (open readers, pending pages) is the DB's business (`notes/bbolt-proof-plan.md`).

`treeWF pages hwm root`: the B+tree of a bucket whose root is page `root` is well-formed in
`pages`: every page of it is a well-formed leaf or branch (`PageModel.lean`: elements, keys and
values inside the page), its children are below the high-water mark `hwm` and well-formed, and
so are the trees of its nested buckets (a leaf element with `BucketLeafFlag`: its value is an
`InBucket` header, and either the bucket's root page, or, for an inline bucket, a leaf page
inside the value). The predicate is inductive: a page graph with a cycle (a corrupt file) does
not satisfy it, which is also why walking a tree terminates.
-/
module

public import Proof.go_etcd_io.bbolt.PageModel
public import Perennial.Golang.Theory.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

def bucketLeafFlag : Nat := 0x01

/-- The `InBucket` header in a bucket element's value: its root page. -/
def inBucketRoot (v : List w8) : Nat := leAt v 0 8

/-- An inline bucket's page: the value after its 16-byte header. -/
def inlinePage (v : List w8) : List w8 := v.drop 16

/- Well-formed bucket trees in `pages` (high-water mark `hwm`). `treeWF` is about the tree
rooted at a page id, `pageTreeWF` about one whose root page has the bytes `pg` (`len` of them
belong to the page: all of an inline bucket's, `(1 + overflow) * ps` of a file page's). -/
mutual
inductive treeWF (pages : GMap Nat (List w8)) (hwm : Nat) : Nat → Prop
  | page (root : Nat) (pg : List w8) :
      root < hwm → pages !! root = some pg → pageId pg = root →
      pageTreeWF pages hwm pg pg.length → treeWF pages hwm root

inductive pageTreeWF (pages : GMap Nat (List w8)) (hwm : Nat) : List w8 → Nat → Prop
  | leaf (pg : List w8) (len : Nat) :
      pageFlags pg = leafPageFlag → leafWF pg len →
      (∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag →
        bucketWF pages hwm (leafValue pg i)) →
      pageTreeWF pages hwm pg len
  | branch (pg : List w8) (len : Nat) :
      pageFlags pg = branchPageFlag → branchWF pg len hwm →
      (∀ i < pageCount pg, treeWF pages hwm (branchPgid pg i)) →
      pageTreeWF pages hwm pg len

/-- A nested bucket's value: a header, and the tree of its root page or its inline page. -/
inductive bucketWF (pages : GMap Nat (List w8)) (hwm : Nat) : List w8 → Prop
  | file (v : List w8) : 16 ≤ v.length → inBucketRoot v ≠ 0 → treeWF pages hwm (inBucketRoot v) →
      bucketWF pages hwm v
  | inline (v : List w8) : 16 ≤ v.length → inBucketRoot v = 0 →
      pageFlags (inlinePage v) = leafPageFlag →
      pageTreeWF pages hwm (inlinePage v) (inlinePage v).length → bucketWF pages hwm v
end

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The mapped cells of the pages `pages`, at the fraction `q`. -/
def pagesView (data : Loc) (ps : Nat) (q : Qp) (pages : GMap Nat (List w8)) : IProp GF :=
  [∗map] id ↦ pg ∈ pages, bytesPointsto (data +ₗ ((id * ps : Nat) : Int)) (DFrac.own q) pg

end preds

end bbolt
end EtcdGrove
end Perennial
