/-
`b.free()` (`bucket.go`): every page of the bucket freed as pending (none for an inline bucket). Users: `DeleteBucket`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch (the freelist, integration I7).** `forEachPageNode` over the bucket's base-tree
pages (a bucket that existed at `Begin`: one created in this transaction is inline, root `0`):
4d's `Interface.Free` of each mapped page, `node.free` of each cached node. `canFree` from the
invariant (`Internal.lean`, "The freelist's side"): the extents are disjoint (the file's
well-formedness) and none was freed before in this transaction (a cached node's page is freed
only through its node, which then has `pgid = 0`; the bucket is deleted once: its handle's path
is gone from `T.cur`).
**Changes** (verify-round, A11 F9): the post keeps the abstraction relation (`repKept`: the pages
freed are pending, still readable in the snapshot), which `DeleteBucket`'s `physRep_delBkt` needs;
the premise `C.bkts b = none` (`DeleteBucket` already dropped the handle from its parent's cache):
on a cached handle `SetRootPage(0)` would make it read as an inline bucket.
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

/-- (internal) the bucket's pages pending for this txid. -/
def Bucket.free.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (b : Loc) (p : BPath),
  {{ wtxCore (GF := GF) tx γ C ∗ bktH tx γ b p ∗ ⌜C.bkts b = none⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"free")) (Val #()))
  {{ RET #(); ∃ C' : TxCore, wtxCore tx γ C' ∗ ⌜repKept C C' ∧ C'.bkts = C.bkts⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
