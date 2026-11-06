/-
`Bucket.pageNode` of a reader (bbolt, internal to U6 of `notes/bbolt-proof-plan.md`): the page of a
position of the bucket (a reader's bucket has no nodes). Proof:
`Proof/go_etcd_io/bbolt/Bucket__pageNode_r.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.RCtx

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

/-- `b.pageNode(id)` of a reader's bucket `b` (value `bv`): the page `l` of position `id`
(`rPageAt`; its inline page, or the view's), no node. -/
abbrev Bucket.pageNode_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp : Loc) (id : w64) (l : Loc) (pg : List w8),
  16 ≤ bv.length → rPageAt v bv pp id.toNat = some (l, pg) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"pageNode")) (Val #id))
  {{ RET (PairV #l #null); rdTxK K tx src q T v ∗ rBktP v tx b dq bv ibp pp }}

end spec

end bbolt
end EtcdGrove
end Perennial
