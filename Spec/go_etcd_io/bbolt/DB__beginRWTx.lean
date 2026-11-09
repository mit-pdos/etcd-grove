/-
`db.beginRWTx()` (`db.go`): `Begin(true)`: `rwlock`, the meta copy, `ReleasePendingPages`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) as `DB.Begin.spec` (write). -/
def DB.beginRWTx.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns : Bool),
  {{ isBolt (GF := GF) db γ ns }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"beginRWTx")) (Val #()))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err); (⌜err = GoInterface.nil⌝ ∗ txDB tx db ∗ ∃ D, boltTx tx γ 1 (TxView.wr D false ns)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ (dbClosed db ∨ dbBroken γ)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
