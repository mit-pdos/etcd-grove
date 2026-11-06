/-
`node.free` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U8; used by U7 (`Bucket.free`), U8 (`node.rebalance`). Proof:
`Proof/go_etcd_io/bbolt/node__free.lean` (a `sorry` until U8).
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

/-- `n.free()` of a node of bucket `bl`, the writer's database side live (`wdbW`): if it was read
from a page (`pgid ≠ 0`), the page's extent is freed for the writer's txid (`Free`, a
`store_free` step: pending) and its `pgid` becomes `0`; else nothing. The extent's `Free` must
not panic (`canFree`); `tx.page(n.pgid)` reads the page (its header names `pgid`, a leaf or a
branch: `FastCheck`), and `Free` takes `tx.meta.Txid()`, the writer's txid. The bucket's `tx`
field is the transaction (`wtxHeap`'s `heapOK`). -/
abbrev node.free.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl n : Loc) (rn : NRec),
  X.node bl n = some rn → rn.nv.bucket' = bl →
  (rn.nv.pgid' ≠ W64 0 → X.t.pm !! rn.nv.pgid' = none ∧ X.t.mv.txid' = w.wtxid ∧
    ∃ pg, X.v.pages !! rn.nv.pgid'.toNat = some pg ∧
      16 ≤ pg.length ∧ pageId pg = rn.nv.pgid'.toNat ∧
      (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
      w.fl.canFree w.wtxid rn.nv.pgid' (1 + pageOverflow pg)) →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"free")) (Val #()))
  {{ RET #(); ∃ (X' : WX) (w' : WDb), wtxW K tx r m X' ∗ wdbW K tx X.v w' ∗
      ⌜(rn.nv.pgid' = W64 0 ∧ X' = X ∧ w' = w) ∨
       (∃ pg, rn.nv.pgid' ≠ W64 0 ∧ X.v.pages !! rn.nv.pgid'.toNat = some pg ∧
         X' = X.setNode bl n { rn with nv := { rn.nv with pgid' := W64 0 } } ∧
         w' = w.withFl (w.fl.freePages w.wtxid rn.nv.pgid' (1 + pageOverflow pg)))⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
