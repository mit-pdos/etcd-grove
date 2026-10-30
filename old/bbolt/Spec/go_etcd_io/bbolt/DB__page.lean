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

/-- `db.page(id)`: page `id` of the mapping, `id * pageSize` bytes after `db.data` (it panics
if that is past `MaxMapSize`). Over the two fields it reads (a read transaction holds
fractions of them, the DB struct being the writer's). -/
abbrev DB.page.spec : Prop :=
  ∀ (dbl : Loc) (data : Loc) (ps : w64) (dq dqs : DFrac) (id : w64),
  data.locCar ≠ 0 → uint.Z (id * ps) < 281474976710655 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"data" dbl ↦{dq} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dqs} ps }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"page")) (Val #id))
  {{ RET #(data +ₗ uint.Z (id * ps)); structFieldRef DB go!"data" dbl ↦{dq} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dqs} ps }}

end spec

end bbolt
end EtcdGrove
end Perennial
