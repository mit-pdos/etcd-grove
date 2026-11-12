/-
`b.write()` (`bucket.go`): an inline bucket's value: its header and its root node as a page.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch** (integration I7). `make([]byte, 16 + n.size())` (`node.size`) is zeroed, so the
fake page after the header is empty (`nodeWritable`'s header clause; `inlineOk` bounds the count
and the size, `wtxCore_keys` the keys); 4d's `inBucket_view` stores the handle's header; `node.write`
(its post `nodePage`). Users: `Bucket.spill` (after `inlineable`), `CreateBucket`'s and `CreateBucketIfNotExists`' fresh local
(`emptyBkt`).

**Changes** (integration I7): the root node is a premise (it was not: `n.size()` on a nil root
panics) and the value is stated (was: some bytes).
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** `bktH` (which object `b` is)
without the generations (the per-path generation counter it replaces was unobservable state,
redundant with ownership).
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

/-- (internal) a fresh value: the bucket's header (`ib`, its `InBucket`), then its root node
written as a page in zeroed bytes (`nodePage`; 4d's `encInBucket`). The bucket is a handle of the
writer whose cached root is inlineable (`Bucket.spill`), or `CreateBucket`'s fresh local
(`fresh`: `emptyBkt`, an empty leaf, a zero header). -/
def Bucket.write.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (b : Loc) (p : BPath)
    (n : Loc) (N : NodeR) (fresh : Bool),
  {{ (if fresh then emptyBkt (GF := GF) b ∗ ⌜N = NodeR.emptyLeaf⌝
      else wtxCore tx γ C ∗ bktH tx γ b p ∗
        ⌜C.roots b = some n ∧ C.nodes n = some N ∧ inlineOk N⌝) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"write")) (Val #()))
  {{ (s : GoSlice), RET #s;
      (if fresh then emptyBkt b else wtxCore tx γ C ∗ bktH tx γ b p) ∗
      ∃ ib : go_etcd_io.bbolt.internal.common.InBucket,
        s ↦* (BboltCommon.encInBucket ib ++ nodePage (List.replicate (nodeSize N) (W8 0)) N) ∗
        ownSliceCap w8 s (DFrac.own 1) ∗
        ⌜fresh = true → ib = ⟨W64 0, W64 0⟩⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
