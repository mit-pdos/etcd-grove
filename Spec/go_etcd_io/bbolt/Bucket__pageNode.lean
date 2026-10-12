module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.PageView
public import Proof.go_etcd_io.bbolt.StructSplit
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
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

/-- The premises of `tx.page(id)` (`Tx.page.spec`). -/
def txPageOk (t : Tx) (dbl data : Loc) (ps id : w64) (pg : List w8) : Prop :=
  t.db' = dbl ∧ t.pages' = map.nil ∧ data.locCar ≠ 0 ∧ uint.Z (id * ps) < 281474976710655 ∧
  16 ≤ pg.length ∧ W64 (pageId pg) = id ∧ validPageFlags (W16 (pageFlags pg))

/-- `b.pageNode(id)` with no node materialized (the read path): for an inline bucket (root
0) its inline page (`id` must be 0: it panics otherwise), else page `id` (`tx.page`). -/
abbrev Bucket.pageNode.spec : Prop :=
  ∀ (bl : Loc) (bv : Bucket) (dqb : DFrac) (ib : internal.common.InBucket) (dqi : DFrac) (id : w64)
    (txl : Loc) (t : Tx) (dqt : DFrac) (dbl data : Loc) (ps : w64) (dq q : DFrac) (pg : List w8),
  bv.tx' = txl → bv.nodes' = map.nil → bv.rootNode' = null →
  (ib.root' = W64 0 → id = W64 0) → (ib.root' ≠ W64 0 → txPageOk t dbl data ps id pg) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bl ↦{dqb} bv ∗ bv.InBucket' ↦{dqi} ib ∗
      (if ib.root' = W64 0 then True else Tx_rest_stats txl dqt t ∗ structFieldRef DB go!"data" dbl ↦{dq} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗ bytesPointsto (data +ₗ uint.Z (id * ps)) q pg) }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"pageNode")) (Val #id))
  {{ RET (PairV #(if ib.root' = W64 0 then bv.page' else data +ₗ uint.Z (id * ps)) #null);
      bl ↦{dqb} bv ∗ bv.InBucket' ↦{dqi} ib ∗
      (if ib.root' = W64 0 then True else Tx_rest_stats txl dqt t ∗ structFieldRef DB go!"data" dbl ↦{dq} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗ bytesPointsto (data +ₗ uint.Z (id * ps)) q pg) }}

end spec

end bbolt
end EtcdGrove
end Perennial
