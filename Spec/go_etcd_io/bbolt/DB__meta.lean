/-
`DB.meta` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U4; used by U5 (`Tx.init`), U10 (`rollback`), U11 (`loadFreelist`), U4 (`hasSyncedFreelist`). Proof:
`Proof/go_etcd_io/bbolt/DB__meta.lean` (a `sorry` until U4).
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

/-- `db.meta()` on the mapping `(b, l)` holding the committed state `C`'s metas (any shares of
the mapping fields and of the meta slots' cells; `C.metaOk`): the current meta, at slot
`C.txid % 2` (`metaPick_current`). It panics when neither meta is valid: excluded by
`C.metaOk`. -/
abbrev DB.meta.spec : Prop :=
  ∀ (db b : Loc) (l : Nat) (C : CommitSt) (dq : DFrac) (q : Qp),
  C.metaOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      mapFields db dq (some (b, l) : MapSt) ∗ metaCellsQ q (some (b, l) : MapSt) C }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"meta")) (Val #()))
  {{ RET #(b +ₗ ((16 + 4096 * (C.txid % 2) : Nat) : Int));
      mapFields db dq (some (b, l) : MapSt) ∗ metaCellsQ q (some (b, l) : MapSt) C }}

end spec

end bbolt
end EtcdGrove
end Perennial
