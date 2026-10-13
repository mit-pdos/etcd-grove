/-
`treeIndex.Keep` (`index.go`): the hash's kept revisions (2026-10-13, unit 5a; `Compact.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

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

/-- `ti.Keep(rev)` by a reader (its knowledge `kn` of the index, a part of the compaction
revision's authority at or below `rev`): the map of every key's revision `keep` keeps at `rev`
(`keepOfIs`, of the uncompacted key indexes: the compaction at most at the reader's revision
does not change `kiKeep` at `rev`). -/
abbrev mvcc.treeIndex.Keep.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (kn : mvcc.IdxKnow) (rev : w64) (q : Qp) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxReader ti γ ∗ mvcc.idxKnows γ kn ∗ mvcc.crevUB γ q c ∗
      ⌜-1 ≤ c ∧ c ≤ sint.Z rev ∧ 0 ≤ sint.Z rev ∧ sint.Z rev < kn.log.length⌝ }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Keep")) (Val #rev))
  {{ (m : GoMap), RET #m; mvcc.idxReader ti γ ∗ mvcc.idxKnows γ kn ∗ mvcc.crevUB γ q c ∗
      ∃ A : GMap Revision Unit, ownMap m (DFrac.own 1) A ∗ ⌜mvcc.keepOfIs A kn.log rev⌝ }}

end spec

end EtcdGrove
end Perennial
