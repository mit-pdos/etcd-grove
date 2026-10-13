/-
Proof of the spec of the same name: pending (the mvcc store's compaction, units 5b/5c; `sorry`).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Keep
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Ascend
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__keep

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

theorem mvcc.treeIndex.Keep.wp_proof
    (h0 : btree.BTree.Ascend.spec (GF := GF) (hG := hG))
    (h1 : mvcc.keyIndex.keep.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Keep.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
