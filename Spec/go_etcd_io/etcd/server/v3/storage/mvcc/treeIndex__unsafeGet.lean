/-
`treeIndex.unsafeGet` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `ti.unsafeGet(key, atRev)` (under the lock, on the tree at any fraction, every key index
with a revision): the key's revision, create revision and version at `atRev`, or
`ErrRevisionNotFound` (`kiGetVal` of the key's index, the empty one if the key has none). -/
abbrev mvcc.treeIndex.unsafeGet.spec : Prop :=
  ∀ (ti t lg : Loc) (L : List mvcc.IdxEntry) (q : Qp) (key : GoSlice) (k : GoString)
    (atRev : w64) (e : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ti.[treeIndex, go!"tree"] ↦□ t ∗ ti.[treeIndex, go!"lg"] ↦□ lg ∗ mvcc.ownTree t L q ∗
      ⌜∀ z ∈ L, mvcc.kiIsEmpty z.2.2 = false⌝ ∗ key ↦*□ k ∗
      globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e }}
    (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"unsafeGet")) (Val #key))
      (Val #atRev))
  {{ RET (mvcc.kiGetVal ((mvcc.idxGet (mvcc.idxOfEntries L) k).getD mvcc.kiEmpty) atRev
      (GoInterface.ok e)); mvcc.ownTree t L q ∗ key ↦*□ k }}

end spec

end EtcdGrove
end Perennial

