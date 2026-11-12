/-
`n.write(p)` (`node.go`): the node into a page buffer (4d's `WriteInodeToPage`). Users: `node.spill`, `Bucket.write`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch** (integration I7). `Assert(p.Count() == 0 && p.Flags() == 0)` by `nodeWritable`
(4d's `Page.Count`/`Page.Flags`); `SetFlags`, the `0xFFFF` check (`nodeWritable`), `SetCount`
(4d's `Page.SetFlags`/`SetCount`, composed by `hdr_withHdr` into one `withHdr`); for a non-empty
node, 4d's `WriteInodeToPage` with the node's inodes (their slices from `wtxCore`'s realization,
`NodeR.itemsM`): its premises `nodeFits` and the branch rule are `nodeWritable`'s, its room
`pageHeaderSize + (nodeBody true ms).length = nodeSize N ≤ bs.length`. An empty node returns
before it: `writeNode bs' [] = bs'`. A caller gets `nodeWritable`'s key clause from
`wtxCore_keys`, the count from the split (`splitIdx`) or `inlineOk`, the empty header from a
fresh buffer (`db.allocate`'s zeroed page, `Bucket.write`'s `make`).

**Changes** (integration I7): the premise `nodeWritable` (the asserts and panics, 4d's
`WriteInodeToPage` premises; without it the triple was false of a non-empty buffer) and the post
`nodePage bs N` (was: some bytes of the same length).
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) `n.write(p)` into an empty page buffer: the buffer holds the node's page
(`nodePage`: its kind and count in the header, then 4d's `writeNode` of its inodes). -/
def node.write.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR) (p : Loc) (bs : List w8),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ ∗ bytesPointsto p (DFrac.own 1) bs ∗
      ⌜nodeSize N ≤ bs.length ∧ nodeWritable (BboltCommon.hdrOf bs) N⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"write")) (Val #p))
  {{ RET #(); wtxCore tx γ C ∗ bytesPointsto p (DFrac.own 1) (nodePage bs N) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
