/-
`DB.page` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U4; used by U4 (`Tx.page`), U10 (`Commit`, `rollback`), U11 (`loadFreelist`). Proof:
`Proof/go_etcd_io/bbolt/DB__page.lean` (a `sorry` until U4).
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

/-- `db.page(id)`: the address of page `id` of the mapping (`&db.data[id * pageSize]`, which
panics on a nil mapping or an index past `maxMapSize`: excluded by the premises). -/
abbrev DB.page.spec : Prop :=
  ∀ (db data : Loc) (id : w64) (dq : DFrac),
  0 < data.addr → id.toNat * 4096 < 0xFFFFFFFFFFFF →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ db.[DB, go!"data"] ↦{dq} data ∗
      db.[DB, go!"pageSize"] ↦□ W64 4096 }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"page")) (Val #id))
  {{ RET #(data +ₗ ((id.toNat * 4096 : Nat) : Int)); db.[DB, go!"data"] ↦{dq} data }}

end spec

end bbolt
end EtcdGrove
end Perennial
