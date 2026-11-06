/-
`DB.hasSyncedFreelist` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U4; used by U10 (`rollback`), U11 (`loadFreelist`). Proof:
`Proof/go_etcd_io/bbolt/DB__hasSyncedFreelist.lean` (a `sorry` until U4).
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

/-- `db.hasSyncedFreelist()`: whether the current meta names a freelist page (`C.flpg`). -/
abbrev DB.hasSyncedFreelist.spec : Prop :=
  ∀ (db b : Loc) (l : Nat) (C : CommitSt) (dq : DFrac) (q : Qp),
  C.metaOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      mapFields db dq (some (b, l) : MapSt) ∗ metaCellsQ q (some (b, l) : MapSt) C }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"hasSyncedFreelist")) (Val #()))
  {{ RET #(decide (C.flpg ≠ none));
      mapFields db dq (some (b, l) : MapSt) ∗ metaCellsQ q (some (b, l) : MapSt) C }}

end spec

end bbolt
end EtcdGrove
end Perennial
