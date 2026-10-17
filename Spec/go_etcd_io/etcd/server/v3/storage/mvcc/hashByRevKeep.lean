/-
`hashByRevKeep` (`kvstore.go`, the fork's split of `store.hashByRev`'s choice of the kept set,
etcd-io/etcd#22515; pr-verify/etcd-22515).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashFilter

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

/-- `hashByRevKeep(idx, rev, compactRev)` of the store's index (a `*treeIndex`), by a reader
(`treeIndex.Keep`'s resources: its knowledge `kn` of the index, a part of the compaction
revision's authority at `c`, at or below `compactRev`, at or below `rev`, as `hashByRev` calls
it): `exact` is set exactly when `Keep(rev)` keeps nothing and `compactRev > 0`, and the map is
`Keep(compactRev)` if `exact`, `Keep(rev)` otherwise (`keepOfIs`). -/
abbrev mvcc.hashByRevKeep.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (kn : mvcc.IdxKnow) (rev crev : w64) (q : Qp) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxReader ti γ ∗ mvcc.idxKnows γ kn ∗ mvcc.crevUB γ q c ∗
      ⌜-1 ≤ c ∧ c ≤ sint.Z crev ∧ sint.Z crev ≤ sint.Z rev ∧ 0 ≤ sint.Z rev ∧
        sint.Z rev < kn.log.length⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.hashByRevKeep))
      (Val #(interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface))) (Val #rev))
      (Val #crev))
  {{ (m : GoMap) (ex : Bool), RET (PairV #m #ex);
      mvcc.idxReader ti γ ∗ mvcc.idxKnows γ kn ∗ mvcc.crevUB γ q c ∗
      ∃ A : GMap Revision Unit, ownMap m (DFrac.own 1) A ∗
        ⌜(ex = true ↔ ((∀ r, ¬ mvcc.keepRevOf kn.log rev r) ∧ 0 < sint.Z crev)) ∧
          mvcc.keepOfIs A kn.log (if ex then crev else rev)⌝ }}

end spec

end EtcdGrove
end Perennial
