/-
`treeIndex.KeyIndex` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `ti.KeyIndex(keyi)` by a reader with the knowledge `kn` of the index (`idxKnows`): the
pointer to the key index of `keyi`'s key `k` in the tree (with its key, for good), or `nil`.
If `kn.log` gives `k` an index, it is there; with the writer's knowledge, it is there exactly
when the writer's log gives `k` one. (`restore` uses it on its private index, out of scope.) -/
abbrev mvcc.treeIndex.KeyIndex.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (kn : mvcc.IdxKnow) (keyi : Loc) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxReader ti γ ∗ mvcc.idxKnows γ kn ∗ mvcc.kiKey keyi k }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"KeyIndex")) (Val #keyi))
  {{ (p : Loc), RET #p; mvcc.idxReader ti γ ∗ mvcc.idxKnows γ kn ∗
      (⌜p = null⌝ ∨ ⌜p ≠ null⌝ ∗ mvcc.kiKey p k) ∗
      ⌜mvcc.kiOfKey (mvcc.evsOf kn.log) k ≠ mvcc.kiEmpty → p ≠ null⌝ ∗
      ⌜∀ ilog pend, kn = .writer ilog pend → p ≠ null →
        mvcc.kiOfKey (mvcc.evsOf (ilog ++ [pend])) k ≠ mvcc.kiEmpty⌝ }}

end spec

end EtcdGrove
end Perennial

