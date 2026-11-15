/-
`Tx.Writable` (bbolt): the spec plan's statement (`SpecPlan/Spec/go_etcd_io/bbolt/Tx__Writable.lean`)
over the real vocabulary (`Spec/go_etcd_io/bbolt/Api.lean`) and the per-byte file extension's
binders; the first function of stage S1 of `notes/bbolt-specplan-convergence.md`. Proof:
`Proof/go_etcd_io/bbolt/Tx__Writable.lean`.
-/
module

public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `tx.Writable()`: whether the transaction is a write transaction (its view's `rw`), at any share
of it. -/
abbrev Tx.Writable.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView),
  {{ boltTx (GF := GF) tx γ q T }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Writable")) (Val #()))
  {{ RET #T.rw; boltTx tx γ q T }}

end spec

end bbolt
end EtcdGrove
end Perennial
