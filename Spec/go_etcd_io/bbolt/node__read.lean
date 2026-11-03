/-
`node.read` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U7; used by U7 (`Bucket.node`). Proof:
`Proof/go_etcd_io/bbolt/node__read.lean` (a `sorry` until U7).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.read(p)` of a page `pg` at `p` from the source `src` (a page of the view, or an inline
page's persistent bytes; `srcLoc`) that `ReadInodeFromPage` can read: the node takes the page's
id and kind, its inodes (a new slice of `pageInodesAt`, whose slices point into the page: the
entries `pageWsAs pg src`, each with its source's facts, `wOwn`) and its first key (nil for an
empty page). -/
abbrev node.read.spec : Prop :=
  ∀ (v : View) (n : Loc) (nv : node) (p : Loc) (src : Src) (pg : List w8) (qv : Qp),
  pageReadable pg → (pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag) →
  0 < p.addr → p.addr + pg.length ≤ maxAddr → (∀ i < pageCount pg, p.addr + elemEnd pg i ≤ maxAddr) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n ↦ nv ∗ srcLoc v p src pg ∗
      viewCells qv v }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"read")) (Val #p))
  {{ RET #(); ∃ s : GoSlice,
      n ↦ nodeAfterRead nv pg s (if 0 < pageCount pg then keySliceAt p pg 0 else slice.nil) ∗
      s ↦* pageInodesAt p pg ∗ ownSliceCap Inode s (DFrac.own 1) ∗
      ([∗list] it;w ∈ pageInodesAt p pg;pageWsAs pg src, wOwn v true it w) ∗
      srcLoc v p src pg ∗ viewCells qv v }}

end spec

end bbolt
end EtcdGrove
end Perennial
