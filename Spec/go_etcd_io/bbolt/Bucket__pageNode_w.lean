/-
`Bucket.pageNode_w` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U6; used by U7 (`Bucket._forEachPageNode`, `Bucket.free`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__pageNode_w.lean` (a `sorry` until U6).
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

/-- `b.pageNode(id)` of a live bucket `bl` of the writer: the materialized node of position `id`
(`resolve`; a nil page), else its page (`wpageAt`; a nil node). It panics on a non-zero id of an
inline bucket, and `tx.page` on a bad page header: excluded by the premises. -/
abbrev Bucket.pageNode_w.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec) (id : w64),
  X.t.bs !! bl = some B → bl ∈ X.liveB → (B.ib.root' = W64 0 → id = W64 0) →
  (B.bv.nodes' = null → B.nm = ∅) →
  (∀ c l, B.nm !! c = some l → l ≠ null) →
  (resolve B id = none → ∃ pa pg, wpageAt X.v B id = some (pa, pg) ∧
    (B.ib.root' = W64 0 → B.pst = PageSt.view ∨ ∃ dq, B.isrc = Src.own dq) ∧
    (B.ib.root' ≠ W64 0 → X.t.pm !! id = none ∧ 16 ≤ pg.length ∧ pageId pg = id.toNat ∧
      (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
      id.toNat * 4096 < 0xFFFFFFFFFFFF)) →
  {{ wtxW (GF := GF) K tx r m X }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"pageNode")) (Val #id))
  {{ (p n : Loc), RET (PairV #p #n); wtxW K tx r m X ∗
      ⌜match resolve B id with
       | some l => p = null ∧ n = l
       | none => n = null ∧ ∃ pg, wpageAt X.v B id = some (p, pg)⌝ }}

/-- **`pageNode` at a fraction** (U6w): `Bucket.pageNode_w.spec` over the writer's working state at
any fraction `q` (`wtxWQ`; it only reads), given back unchanged. `spec` is its case `q = 1`. -/
abbrev Bucket.pageNode_w.specQ : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (bl : Loc) (B : BRec) (id : w64),
  X.t.bs !! bl = some B → bl ∈ X.liveB → (B.ib.root' = W64 0 → id = W64 0) →
  (B.bv.nodes' = null → B.nm = ∅) →
  (∀ c l, B.nm !! c = some l → l ≠ null) →
  (resolve B id = none → ∃ pa pg, wpageAt X.v B id = some (pa, pg) ∧
    (B.ib.root' = W64 0 → B.pst = PageSt.view ∨ ∃ dq, B.isrc = Src.own dq) ∧
    (B.ib.root' ≠ W64 0 → X.t.pm !! id = none ∧ 16 ≤ pg.length ∧ pageId pg = id.toNat ∧
      (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
      id.toNat * 4096 < 0xFFFFFFFFFFFF)) →
  {{ wtxWQ (GF := GF) K tx r m q X }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"pageNode")) (Val #id))
  {{ (p n : Loc), RET (PairV #p #n); wtxWQ K tx r m q X ∗
      ⌜match resolve B id with
       | some l => p = null ∧ n = l
       | none => n = null ∧ ∃ pg, wpageAt X.v B id = some (p, pg)⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
