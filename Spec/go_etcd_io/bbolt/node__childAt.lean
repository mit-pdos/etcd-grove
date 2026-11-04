/-
`node.childAt` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U8; used by U7 (`Cursor.node`), U8 (siblings, `node.rebalance`). Proof:
`Proof/go_etcd_io/bbolt/node__childAt.lean` (a `sorry` until U8).
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

/-- `n.childAt(i)` of a live branch node `n` of bucket `bl`: `b.node` of its entry `i`'s child
page, with `n` as the parent (`Bucket.node.spec`). It panics on a leaf: excluded. -/
abbrev node.childAt.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec) (n : Loc)
    (rn : NRec) (i : w64) (w : WEntry),
  X.t.bs !! bl = some B → B.ns !! n = some rn → rn.nv.bucket' = bl → rn.nv.isLeaf' = false →
  n ∈ X.live → bl ∈ X.liveB → B.bv.nodes' ≠ null → 0 ≤ sint.Z i →
  rn.ws[sint.nat i]? = some w →
  (∀ l, B.nm !! w.pgid = some l → l ≠ null) → (B.nm !! w.pgid = none → matReady X B w.pgid) →
  {{ wtxW (GF := GF) K tx r m X }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"childAt")) (Val #i))
  {{ (l : Loc), RET #l; ∃ X' : WX, wtxW K tx r m X' ∗
      ⌜(B.nm !! w.pgid = some l ∧ X' = X) ∨ nodeAdded X X' bl l w.pgid n⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
