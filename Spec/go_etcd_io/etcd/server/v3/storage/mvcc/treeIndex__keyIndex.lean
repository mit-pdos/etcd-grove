/-
`treeIndex.keyIndex` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `ti.keyIndex(keyi)` (under the lock, on the tree at any fraction): the key index of
`keyi`'s key, or `nil`. -/
abbrev mvcc.treeIndex.keyIndex.spec : Prop :=
  ∀ (ti t : Loc) (L : List mvcc.IdxEntry) (q : Qp) (keyi : Loc) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ti.[treeIndex, go!"tree"] ↦□ t ∗ mvcc.ownTree t L q ∗ mvcc.kiItemIs keyi (keyi, k) }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"keyIndex")) (Val #keyi))
  {{ (p : Loc), RET #p; mvcc.ownTree t L q ∗
      ⌜p = ((L.find? fun z => decide (z.2.1 = k)).map Prod.fst).getD null⌝ }}

end spec

end EtcdGrove
end Perennial

