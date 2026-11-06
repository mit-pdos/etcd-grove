/-
`DB.pageInBuffer` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U4; used by U10 (`writeMeta`). Proof:
`Proof/go_etcd_io/bbolt/DB__pageInBuffer.lean` (a `sorry` until U4).
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

/-- `db.pageInBuffer(b, id)`: the address of byte `id * pageSize` of `b` (`&b[…]`, which panics
past the slice's end: excluded by the premise). -/
abbrev DB.pageInBuffer.spec : Prop :=
  ∀ (db : Loc) (b : GoSlice) (id : w64),
  id.toNat * 4096 < b.len.toNat → b.len.toNat < 2 ^ 63 → 0 < b.ptr.addr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ db.[DB, go!"pageSize"] ↦□ W64 4096 }}
    (App (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"pageInBuffer")) (Val #b))
      (Val #id))
  {{ RET #(b.ptr +ₗ ((id.toNat * 4096 : Nat) : Int)); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
