/-
`node.childIndex` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U8; used by U8 (`nextSibling`, `prevSibling`, `node.rebalance`). Proof:
`Proof/go_etcd_io/bbolt/node__childIndex.lean` (a `sorry` until U8).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.childIndex(child)` on a live node whose entries are sorted and not stale: the search index
of `child.key` (its bytes `kb`, from their source) in `n`'s entries. The view's base is a mapped address (`0 < v.base.addr`, from `mapFields`). -/
abbrev node.childIndex.spec : Prop :=
  ∀ (v : View) (n bl : Loc) (r : NRec) (dq : DFrac) (qv : Qp) (child : Loc) (cv : node)
    (dqc : DFrac) (ks : Src) (kb : List w8),
  wsSorted r.ws → wsLive r.ws → ks ≠ Src.stale → 0 < v.base.addr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ objOwn v n dq true (WObj.node bl r) ∗
      viewCells qv v ∗ child ↦{dqc} cv ∗ srcOwn v cv.key' ks kb }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"childIndex")) (Val #child))
  {{ RET #(W64 (wsIdx r.ws kb : Int)); objOwn v n dq true (WObj.node bl r) ∗ viewCells qv v ∗
      child ↦{dqc} cv }}

end spec

end bbolt
end EtcdGrove
end Perennial
