module
public import Spec.go_etcd_io.bbolt.newBucket
public import Spec.go_etcd_io.bbolt.DB__meta

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

-- `hash.Hash64`'s type, which `Meta.Validate`'s spec takes: bbolt reaches `hash` only through
-- `hash/fnv`, so its `Assumptions` do not include `hash`'s
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The transaction `tx.init(db)` makes of `t`: of `db`, with the meta copy `ml`, the root bucket
(`newBucket`'s, its header the copy `ibl`), and (writable) the page cache `pm`. -/
def txInitOf (t : Tx) (txl dbl ml ibl : Loc) (pm bm nm : GoMap) : Tx :=
  { t with
    db' := dbl
    pages' := pm
    meta' := ml
    root' := { newBucketOf txl bm nm with InBucket' := ibl } }
proj_simps txInitOf

/-- The meta a transaction begins from: the DB's current one, `txid` incremented if writable. -/
def txMetaOf (w : Bool) (v0 v1 : internal.common.Meta) : internal.common.Meta :=
  let vm := if metaPick v0 v1 then v1 else v0
  if w then { vm with txid' := vm.txid' + 1 } else vm

/-- `tx.init(db)`: `tx` gets a copy of the DB's current meta (`DB.meta`; its txid incremented
if writable), a root bucket with a copy of the meta's root header, and (writable) an empty
page cache and bucket caches. -/
abbrev Tx.init.spec : Prop :=
  ∀ (txl : Loc) (t : Tx) (dbl m0 m1 : Loc) (dq dq0 dq1 : DFrac) (v0 v1 : internal.common.Meta),
  m0.locCar ≠ 0 → m1.locCar ≠ 0 → metaValid v0 ∨ metaValid v1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ txl ↦ t ∗ structFieldRef DB go!"meta0" dbl ↦{dq} m0 ∗
      structFieldRef DB go!"meta1" dbl ↦{dq} m1 ∗ m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"init")) (Val #dbl))
  {{ (ml ibl : Loc) (pm bm nm : GoMap), RET #();
      ⌜metaValid (if metaPick v0 v1 then v1 else v0)⌝ ∗
      txl ↦ txInitOf t txl dbl ml ibl pm bm nm ∗ ml ↦ txMetaOf t.writable' v0 v1 ∗
      ibl ↦ (if metaPick v0 v1 then v1 else v0).root' ∗
      (if t.writable' then pm ↦$ (∅ : GMap w64 Loc) ∗ bm ↦$ (∅ : GMap GoString Loc) ∗
         nm ↦$ (∅ : GMap w64 Loc)
       else ⌜pm = map.nil ∧ bm = map.nil ∧ nm = map.nil⌝) ∗
      structFieldRef DB go!"meta0" dbl ↦{dq} m0 ∗ structFieldRef DB go!"meta1" dbl ↦{dq} m1 ∗
      m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 }}

end spec

end bbolt
end EtcdGrove
end Perennial
