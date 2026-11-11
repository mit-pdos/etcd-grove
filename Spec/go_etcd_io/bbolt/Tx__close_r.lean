/-
`Tx.close_r` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U5; used by U5 (`Rollback`), U10, U11. Proof:
`Proof/go_etcd_io/bbolt/Tx__close_r.lean` (a `sorry` until U5).
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

/-- `tx.close()` of a whole reader: `removeTx` (its registry entry and the pair given back), the
transaction done (`txDone`), its pair source given back (`pairBack`). -/
abbrev Tx.close_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (T : TxView) (v : View),
  {{ rdTxK (GF := GF) K tx src 1 T v }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"close")) (Val #()))
  {{ RET #(); txDoneDef tx ∗ pairBack K src }}

end spec

end bbolt
end EtcdGrove
end Perennial
