/-
`TxStats.IncNodeCount` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U5; used by U7 (`Bucket.node`). Proof:
`Proof/go_etcd_io/bbolt/TxStats__IncNodeCount.lean` (a `sorry` until U5).
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

/-- `tx.stats.IncNodeCount(d)` (an atomic add on a statistic of the live transaction `tx`, whose
statistics `txsInv` holds): needs only the statistics' token; the new value is any. -/
abbrev TxStats.IncNodeCount.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (d : w64),
  {{ K.core (GF := GF) ∗ reg tx K.B r ∗ statsTok r m q }}
    (App (Val (tx.[Tx, go!"stats"] @!! go.GoType.PointerType TxStats.ty @!! go!"IncNodeCount")) (Val #d))
  {{ (n : w64), RET #n; statsTok r m q }}

end spec

end bbolt
end EtcdGrove
end Perennial
