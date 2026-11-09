/-
`db.beginTx()` (`db.go`): `Begin(false)`.
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

/-- (internal) as `DB.Begin.spec` (read). -/
def DB.beginTx.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns : Bool) (Q : Data → IProp GF),
  {{ isBolt (GF := GF) db γ ns ∗ threadTok ∗ AU <{ ∃∃ (q : Qp) (σ : BoltSt), boltState γ q σ }> @ ⊤ \ ↑γ.ns, ∅ <{ boltState γ q σ, COMM Q σ.data }> }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"beginTx")) (Val #()))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err); (⌜err = GoInterface.nil⌝ ∗ txDB tx db ∗ ∃ D, boltTx tx γ 1 (TxView.ro D false ns) ∗ Q D) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ threadTok ∗ AU <{ ∃∃ (q : Qp) (σ : BoltSt), boltState γ q σ }> @ ⊤ \ ↑γ.ns, ∅ <{ boltState γ q σ, COMM Q σ.data }>) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
