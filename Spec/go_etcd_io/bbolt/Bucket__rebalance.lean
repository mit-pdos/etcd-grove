/-
`Bucket.rebalance` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U8; used by U10 (`Commit`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__rebalance.lean` (a `sorry` until U8).
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

/-- **`tx.root.rebalance()`** (design §4.2): from a well-formed writer whose buckets' leaves are
at one depth, to records satisfying `rebalOK` (`spill`'s pre: well-formed, the same data, no empty
non-root node, branches of at least two entries, leaves at one depth, every base slot covered or
pending), the frees `Free` steps for the writer's txid (store-side `store_free`); the database side
otherwise unchanged; (batch 44.6) the transaction's fields and its meta copy kept; (coordinator, 44.1 addition 2) the root bucket's children map `bm` kept. Map iteration order is the Go runtime's: the post holds for any. -/
abbrev Bucket.rebalance.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb),
  wOK X → (∀ bl, X.t.bs !! bl ≠ none → leafDepthOK X bl) → liveReach X → flViewU X w.fl →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (tx.[Tx, go!"root"] @!! go.GoType.PointerType Bucket.ty @!! go!"rebalance"))
      (Val #()))
  {{ RET #(); ∃ (X' : WX) (fl' : FLPg), wtxW K tx r m X' ∗ wdbW K tx X.v (w.withFl fl') ∗
      ⌜rebalOK X X' w.fl fl' w.wtxid ∧ liveReach X' ∧ flViewU X' fl' ∧
        X'.t.t = X.t.t ∧ X'.t.mv = X.t.mv ∧
        (X'.t.bs !! X.rl).map BRec.bm = (X.t.bs !! X.rl).map BRec.bm⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
