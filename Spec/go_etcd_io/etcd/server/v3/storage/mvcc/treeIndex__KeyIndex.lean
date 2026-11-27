/-
`treeIndex.KeyIndex` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.IdxPriv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `ti.KeyIndex(keyi)` on a tree index no one else can reach (`ownIdxPriv`: its only caller,
`restoreIntoIndex`'s goroutine, rebuilds a private index; `notes/restore-plan.md`, R3): the pointer
to the key index of `keyi`'s key `k` in the tree, or `nil`. -/
abbrev mvcc.treeIndex.KeyIndex.spec : Prop :=
  ∀ (ti : Loc) (L : List mvcc.IdxEntry) (keyi : Loc) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownIdxPriv ti L ∗ mvcc.kiKey keyi k }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"KeyIndex")) (Val #keyi))
  {{ (p : Loc), RET #p; mvcc.ownIdxPriv ti L ∗
      ⌜p = ((L.find? fun z => decide (z.2.1 = k)).map Prod.fst).getD null⌝ }}

end spec

end EtcdGrove
end Perennial

