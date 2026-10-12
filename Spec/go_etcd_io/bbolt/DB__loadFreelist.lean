module
public import Spec.go_etcd_io.bbolt.newFreelist
public import Proof.go_etcd_io.bbolt.FLPage
public import Proof.go_etcd_io.bbolt.internal.freelist.ArrayIface
public import Proof.go_etcd_io.bbolt.TxModel
public import Spec.go_etcd_io.bbolt.DB__meta
public import Spec.go_etcd_io.bbolt.DB__hasSyncedFreelist
public import Spec.go_etcd_io.bbolt.DB__page
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.freelist

section defs
variable [ext : FfiSyntax]

/-- A freelist page `loadFreelist` can read: a freelist page whose ids fit it, distinct, and
none a meta page. -/
def flPageOK (pg : List w8) : Prop :=
  pageFlags pg = freelistPageFlag ∧ flOff pg + 8 * flN pg ≤ pg.length ∧ pg.length < 2 ^ 62 ∧
  (flIds pg).Nodup ∧ ∀ x ∈ flIds pg, 2 ≤ uint.Z x

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.loadFreelist()`, its `Once` never run, the freelist synced (the current meta names a
freelist page, `pg` its bytes at `data + id * ps`), its type not `"hashmap"`: the database's
freelist is a new `array` freelist whose free ids are the page's, sorted; the statistics' free
count set. -/
abbrev DB.loadFreelist.spec : Prop :=
  ∀ (dbl data m0 m1 st : Loc) (ps : w64) (ft : GoString) (fl0 : GoInterface)
    (dq dqm dq0 dq1 dqd dqs dqp : DFrac) (v0 v1 : internal.common.Meta) (pg : List w8),
  (∀ a, (arrayImpl (GF := GF) a).IfaceContract) →
  ft ≠ go!"hashmap" → m0.locCar ≠ 0 → m1.locCar ≠ 0 → (metaValid v0 ∨ metaValid v1) →
  (if metaPick v0 v1 then v1 else v0).freelist' ≠ W64 18446744073709551615 →
  data.locCar ≠ 0 →
  uint.Z ((if metaPick v0 v1 then v1 else v0).freelist' * ps) < 281474976710655 →
  flPageOK pg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      typedPointsto (structFieldRef DB go!"freelistLoad" dbl) (zero_val sync.Once) (DFrac.own 1) ∗
      structFieldRef DB go!"freelist" dbl ↦ fl0 ∗ structFieldRef DB go!"FreelistType" dbl ↦{dq} ft ∗
      structFieldRef DB go!"meta0" dbl ↦{dqm} m0 ∗ structFieldRef DB go!"meta1" dbl ↦{dqm} m1 ∗
      m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 ∗
      structFieldRef DB go!"data" dbl ↦{dqd} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dqs} ps ∗
      bytesPointsto (data +ₗ uint.Z ((if metaPick v0 v1 then v1 else v0).freelist' * ps)) dqp pg ∗
      structFieldRef DB go!"stats" dbl ↦{dq} st ∗ (⌜st = null⌝ ∨ ∃ (sv : Stats), st ↦ sv) }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"loadFreelist")) (Val #()))
  {{ RET #(); ∃ (a s : Loc) (free : List w64), ⌜PgidsIncr free ∧ free.Perm (flIds pg)⌝ ∗
      structFieldRef DB go!"freelist" dbl ↦ (arrayImpl (GF := GF) a).iface ∗
      ownFL (arrayImpl a) s { FLState.empty with free := free } ∗
      structFieldRef DB go!"FreelistType" dbl ↦{dq} ft ∗
      structFieldRef DB go!"meta0" dbl ↦{dqm} m0 ∗ structFieldRef DB go!"meta1" dbl ↦{dqm} m1 ∗
      m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 ∗
      structFieldRef DB go!"data" dbl ↦{dqd} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dqs} ps ∗
      bytesPointsto (data +ₗ uint.Z ((if metaPick v0 v1 then v1 else v0).freelist' * ps)) dqp pg ∗
      structFieldRef DB go!"stats" dbl ↦{dq} st ∗ (⌜st = null⌝ ∨ ∃ (sv : Stats), st ↦ sv) }}

end spec

end bbolt
end EtcdGrove
end Perennial
