/-
`DB.beginTx_s` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U5; used by U10 (`freepages`). Proof:
`Proof/go_etcd_io/bbolt/DB__beginTx_s.lean` (a `sorry` until U5).
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

/-- `db.beginTx()` on the writer side's spare reader pair (design §3.13, A2: `freepages` in a
writer's `rollback` or `Open`'s core phase; `isBolt` may not exist yet): the caller holds the
committed state's writer quarter `C`, the mapping `(b, l)`'s writer half and `opened`'s half, so
the read transaction is opened (no error) on `C`'s view at the mapping, its pair from the spare
(`rdTxK … .spare`). -/
abbrev DB.beginTx_s.spec : Prop :=
  ∀ (K : BC) (C : CommitSt) (b : Loc) (l : Nat),
  C.metaOk → treeOK C →
  {{ K.core (GF := GF) ∗ rdPair K.B K.db K.sp ∗ ghostVar K.B.cur (1 : Qp).half.half C ∗
      ghostVar K.B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      K.db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} true }}
    (App (Val (K.db @!! go.GoType.PointerType DB.ty @!! go!"beginTx")) (Val #()))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err); ⌜err = interface.nil⌝ ∗
      rdTxK K tx PairSrc.spare 1 (TxView.ro (View.ofC b C).data) (View.ofC b C) ∗
      ghostVar K.B.cur (1 : Qp).half.half C ∗ ghostVar K.B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      K.db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} true }}

end spec

end bbolt
end EtcdGrove
end Perennial
