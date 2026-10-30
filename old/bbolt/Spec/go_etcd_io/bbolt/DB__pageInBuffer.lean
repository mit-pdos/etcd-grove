module
public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.pageInBuffer(b, id)`: page `id` of the buffer `b`, `id * pageSize` bytes into it (it
panics if that is not inside `b`). -/
abbrev DB.pageInBuffer.spec : Prop :=
  ∀ (dbl : Loc) (ps : w64) (dq : DFrac) (b : GoSlice) (id : w64),
  b.ptr.locCar ≠ 0 → 0 ≤ sint.Z (id * ps) → sint.Z (id * ps) < sint.Z b.len →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps }}
    (App (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"pageInBuffer")) (Val #b)) (Val #id))
  {{ RET #(b.ptr +ₗ sint.Z (id * ps)); structFieldRef DB go!"pageSize" dbl ↦{dq} ps }}

end spec

end bbolt
end EtcdGrove
end Perennial
