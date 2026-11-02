module
public import Proof.go_etcd_io.bbolt.Init
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate

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

open Classical in
/-- Which meta page `db.meta()` picks (`true`: the second): the one with the higher txid if
it is valid, otherwise the other. -/
noncomputable def metaPick (v0 v1 : internal.common.Meta) : Bool :=
  if uint.Z v0.txid' < uint.Z v1.txid' then (if metaValid v1 then true else false)
  else (if metaValid v0 then false else true)

/-- `db.meta()`: the current meta, `metaPick` of the two meta pages, which is valid (it panics
if neither is). Over the two fields it reads and the two metas (at any fractions). -/
abbrev DB.meta.spec : Prop :=
  ∀ (dbl m0 m1 : Loc) (dq dq0 dq1 : DFrac) (v0 v1 : internal.common.Meta),
  m0.locCar ≠ 0 → m1.locCar ≠ 0 → metaValid v0 ∨ metaValid v1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"meta0" dbl ↦{dq} m0 ∗ structFieldRef DB go!"meta1" dbl ↦{dq} m1 ∗
      m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"meta")) (Val #()))
  {{ RET #(if metaPick v0 v1 then m1 else m0);
      ⌜metaValid (if metaPick v0 v1 then v1 else v0)⌝ ∗
      structFieldRef DB go!"meta0" dbl ↦{dq} m0 ∗ structFieldRef DB go!"meta1" dbl ↦{dq} m1 ∗
      m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 }}

end spec

end bbolt
end EtcdGrove
end Perennial
