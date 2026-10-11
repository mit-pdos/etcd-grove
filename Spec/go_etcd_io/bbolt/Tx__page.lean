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

/-- `tx.page(id)` of a page the transaction has not written (`tx.pages` nil, as for a read
transaction): page `id` of the mapping, which names itself and has a valid type
(`FastCheck`, which panics otherwise). The page's bytes are held at any fraction. -/
abbrev Tx.page.spec : Prop :=
  ∀ (txl : Loc) (t : Tx) (dqt : DFrac) (dbl data : Loc) (ps : w64) (dq q : DFrac) (id : w64)
    (pg : List w8),
  t.db' = dbl → t.pages' = map.nil → data.locCar ≠ 0 → uint.Z (id * ps) < 281474976710655 →
  16 ≤ pg.length → W64 (pageId pg) = id → validPageFlags (W16 (pageFlags pg)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ txl ↦{dqt} t ∗ structFieldRef DB go!"data" dbl ↦{dq} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗
      bytesPointsto (data +ₗ uint.Z (id * ps)) q pg }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"page")) (Val #id))
  {{ RET #(data +ₗ uint.Z (id * ps)); txl ↦{dqt} t ∗ structFieldRef DB go!"data" dbl ↦{dq} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗
      bytesPointsto (data +ₗ uint.Z (id * ps)) q pg }}

end spec

end bbolt
end EtcdGrove
end Perennial
