/-
`n.free()` (`node.go`): its page freed as pending for the txid (4d's `freelist.Free`).
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch.** If `n.pgid ≠ 0`: `tx.page(n.pgid)` (a page of the base tree), 4d's
`Interface.Free.spec` with `canFree` from `wtxCore`'s invariant (`Internal.lean`, "The freelist's
side": a cached node with `pgid ≠ 0` holds a base-tree page not yet freed by this transaction,
neither free nor pending, not allocated by `txid`), then `n.pgid = 0`, which keeps that invariant.

**Changes (integration I7).** The post said the node cache unchanged, but the code sets the
node's `pgid` to `0`: now the node is `{ N with pgid := 0 }`. Verify-round (A11 F9): and the
cache still represents every view it did (`repKept`: a cached node's data is its inodes, not its
page; the freed page stays readable in the snapshot until the commit).
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

/-- (internal) the node's old page pending, the node's page id now `0`. -/
def node.free.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"free")) (Val #()))
  {{ RET #(); ∃ C' : TxCore, wtxCore tx γ C' ∗
      ⌜C'.nodes = (fun x => if x = n then some { N with pgid := W64 0 } else C.nodes x) ∧
        repKept C C'⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
