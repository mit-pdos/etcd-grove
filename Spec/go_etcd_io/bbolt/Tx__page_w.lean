module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.PageView
public import Spec.go_etcd_io.bbolt.internal.common.Page__FastCheck

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

/-- `tx.page(id)` of a writable transaction (its page cache `pmap`, holding `pm`): the dirty
page `pm[id]` if there is one, else page `id` of the mapping (`db.page`). The page returned
(`p`, its bytes `pg`, at any fraction) names itself and has a valid type (`FastCheck`, which
panics otherwise). Of the transaction, the two fields it reads. -/
abbrev Tx.page.wspec : Prop :=
  ∀ (txl : Loc) (pmap : GoMap) (pm : GMap w64 Loc) (dqm dqt : DFrac) (dbl data : Loc) (ps : w64)
    (dq dqs : DFrac) (id : w64) (p : Loc) (q : DFrac) (pg : List w8),
  (pm !! id = some p ∨
    (pm !! id = none ∧ p = data +ₗ uint.Z (id * ps) ∧ data.locCar ≠ 0 ∧
      uint.Z (id * ps) < 281474976710655)) →
  p.locCar ≠ 0 → 16 ≤ pg.length → W64 (pageId pg) = id → validPageFlags (W16 (pageFlags pg)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef Tx go!"pages" txl ↦{dqt} pmap ∗ pmap ↦${dqm} pm ∗
      structFieldRef Tx go!"db" txl ↦{dqt} dbl ∗
      structFieldRef DB go!"data" dbl ↦{dq} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dqs} ps ∗
      bytesPointsto p q pg }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"page")) (Val #id))
  {{ RET #p; structFieldRef Tx go!"pages" txl ↦{dqt} pmap ∗ pmap ↦${dqm} pm ∗
      structFieldRef Tx go!"db" txl ↦{dqt} dbl ∗
      structFieldRef DB go!"data" dbl ↦{dq} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dqs} ps ∗
      bytesPointsto p q pg }}

end spec

end bbolt
end EtcdGrove
end Perennial
