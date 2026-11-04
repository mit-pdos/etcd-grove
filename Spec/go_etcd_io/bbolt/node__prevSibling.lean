/-
`node.prevSibling` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U8; used by U8 (`node.rebalance`). Proof:
`Proof/go_etcd_io/bbolt/node__prevSibling.lean` (a `sorry` until U8).
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

/-- `n.prevSibling()` of a live node `n` of bucket `bl`: nil for the root or the parent's first
child; else the parent's child before `n` (at `n.key`'s search index minus one), materialized if
need be (`childAt`). -/
abbrev node.prevSibling.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec) (n : Loc)
    (rn : NRec),
  X.t.bs !! bl = some B → B.ns !! n = some rn → rn.nv.bucket' = bl → n ∈ X.live →
  bl ∈ X.liveB → B.bv.nodes' ≠ null →
  (rn.nv.parent' ≠ null → rn.nv.key' ≠ slice.nil ∧ rn.ksrc ≠ Src.stale ∧
    ∃ rp, B.ns !! rn.nv.parent' = some rp ∧ rp.nv.isLeaf' = false ∧ rp.nv.bucket' = bl ∧
      rn.nv.parent' ∈ X.live ∧
      wsSorted rp.ws ∧ wsLive rp.ws ∧
      ∀ w, 0 < wsIdx rp.ws rn.key → rp.ws[wsIdx rp.ws rn.key - 1]? = some w →
        (∀ l, B.nm !! w.pgid = some l → l ≠ null) ∧ (B.nm !! w.pgid = none → matReady X B w.pgid)) →
  {{ wtxW (GF := GF) K tx r m X }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"prevSibling")) (Val #()))
  {{ (s : Loc), RET #s; ∃ X' : WX, wtxW K tx r m X' ∗
      ⌜(s = null ∧ X' = X ∧ (rn.nv.parent' = null ∨
          ∃ rp, B.ns !! rn.nv.parent' = some rp ∧ wsIdx rp.ws rn.key = 0)) ∨
       (∃ rp w, B.ns !! rn.nv.parent' = some rp ∧ 0 < wsIdx rp.ws rn.key ∧
         rp.ws[wsIdx rp.ws rn.key - 1]? = some w ∧
         ((B.nm !! w.pgid = some s ∧ X' = X) ∨ nodeAdded X X' bl s w.pgid rn.nv.parent'))⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
