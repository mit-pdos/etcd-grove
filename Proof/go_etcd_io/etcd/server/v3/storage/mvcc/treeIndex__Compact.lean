/-
Proof of the spec of the same name: pending (the mvcc store's compaction, units 5b/5c; `sorry`).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Compact
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Clone
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Ascend
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__compact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__isEmpty
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Delete
public import Spec.go_uber_org.zap.Logger__Panic

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

theorem mvcc.treeIndex.Compact.wp_proof
    (h0 : zap.Int64.spec (GF := GF) (hG := hG))
    (h1 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h2 : btree.BTree.Clone.spec (GF := GF) (hG := hG))
    (h3 : btree.BTree.Ascend.spec (GF := GF) (hG := hG))
    (h4 : mvcc.keyIndex.compact.spec (GF := GF) (hG := hG))
    (h5 : mvcc.keyIndex.isEmpty.spec (GF := GF) (hG := hG))
    (h6 : btree.BTree.Delete.spec (GF := GF) (hG := hG))
    (h7 : zap.Logger.Panic.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Compact.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
