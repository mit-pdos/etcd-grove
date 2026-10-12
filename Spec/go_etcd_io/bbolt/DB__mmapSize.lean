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

/-- The mapping size for a database of `size` bytes and pages of `ps` bytes (`DB.mmapSize`):
the least power of two from 32KiB to 1GiB at least `size`; above that, `size` rounded up to
a whole GiB and then to a whole page, at most `MaxMapSize`; `none` (an error) above
`MaxMapSize`. -/
def mmapSizeOf (size ps : Int) : Option Int :=
  match (List.range 16).find? (fun i => decide (size ≤ 2 ^ (15 + i))) with
  | some i => some (2 ^ (15 + i))
  | none =>
    if size > 281474976710655 then none
    else
      let sz := if size % 1073741824 > 0 then size + 1073741824 - size % 1073741824 else size
      let sz := if sz % ps ≠ 0 then (sz / ps + 1) * ps else sz
      some (min sz 281474976710655)

/-- `db.mmapSize(size)`: `mmapSizeOf`, or an error (over the field it reads). The page size is positive and below
`2^32` (a meta's page size is a `uint32`; a larger one would overflow the rounding up). -/
abbrev DB.mmapSize.spec : Prop :=
  ∀ (dbl : Loc) (ps : w64) (dq : DFrac) (size : w64),
  0 < sint.Z ps → sint.Z ps < 2 ^ 32 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"mmapSize")) (Val #size))
  {{ (r : w64) (err : GoInterface), RET (PairV #r #err); structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗
      ⌜match mmapSizeOf (sint.Z size) (sint.Z ps) with
       | some s => err = interface.nil ∧ sint.Z r = s
       | none => err ≠ interface.nil⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
