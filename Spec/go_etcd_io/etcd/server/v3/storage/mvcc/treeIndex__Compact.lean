/-
`treeIndex.Compact` (`index.go`): the index compacted key by key (2026-10-13, unit 5a; `Compact.lean`, `InvIndex.lean`).
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

/-- `ti.Compact(rev)`, with `rev` a lower bound of the compaction revision (`crevLb`: `Compact` set
it; so the readers read at or above it) and a revision of a certified log: each key index of the
tree (a clone's, each under the lock) compacted at `rev` (a key whose compaction empties it is
deleted from the tree; the lock's invariant, `IdxCRep`, takes the new levels, at most `rev`),
and the map of the revisions compaction keeps (`keepSetIs`: every key's `kiAvail` at `rev` of
the log: later events, above `rev`, and earlier compactions, below it, do not change it,
`kiAvail_prefix`, `kiAvail_kiCompact`). -/
abbrev mvcc.treeIndex.Compact.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (rev : w64) (log : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.crevLb γ (sint.Z rev) ∗ mvcc.idxCert γ log ∗
      ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length⌝ }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Compact")) (Val #rev))
  {{ (m : GoMap), RET #m; ∃ A : GMap Revision Unit, ownMap m (DFrac.own 1) A ∗
      ⌜mvcc.keepSetIs A log (sint.Z rev)⌝ }}

end spec

end EtcdGrove
end Perennial
