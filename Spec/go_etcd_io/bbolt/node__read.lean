/-
`n.read(p)` (`node.go`): the node from a page (4d's `ReadInodeFromPage`). Users: `Bucket.node`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch** (integration I7). `txPage`'s realization gives the page's bytes at `p` with its
header's id `id` and `pageReadable` (4d's `Page.Id`, `Page.IsLeafPage`, `ReadInodeFromPage`): the
inodes are `pageInodesAt p bs`, whose models are `pageItems bs`; the first key, if any, as `key`.

**Changes** (integration I7): the post states the node's kind and inodes (4d's `pageItems`), not
only its page id.
-/
module

public import Spec.go_etcd_io.bbolt.Internal

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

/-- (internal) the node now holds the page's items (leaf or branch as the page says, 4d's
`pageItems`), its page id, its parent. -/
def node.read.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR) (id : w64) (p : Loc) (bs : List w8),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ ∗ txPage tx γ id p bs }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"read")) (Val #p))
  {{ RET #(); ∃ N' : NodeR, wtxCore tx γ { C with nodes := fun x => if x = n then some N' else C.nodes x } ∗
      ⌜N'.pgid = id ∧ N'.parent = N.parent ∧
        N'.isLeaf = BboltCommon.isLeafHdr (BboltCommon.hdrOf bs) ∧
        N'.inodes = (BboltCommon.pageItems bs).map InodeR.ofM⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
