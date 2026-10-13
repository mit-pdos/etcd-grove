/-
Proof of the spec of the same name: pending (the mvcc store's compaction, units 5b/5c; `sorry`).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__compact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__isEmpty
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Panic
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__doCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__isEmpty

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

theorem mvcc.keyIndex.compact.wp_proof
    (h0 : mvcc.keyIndex.isEmpty.spec (GF := GF) (hG := hG))
    (h1 : zap.String.spec (GF := GF) (hG := hG))
    (h2 : zap.Logger.Panic.spec (GF := GF) (hG := hG))
    (h3 : mvcc.keyIndex.doCompact.spec (GF := GF) (hG := hG))
    (h4 : mvcc.generation.isEmpty.spec (GF := GF) (hG := hG)) :
    mvcc.keyIndex.compact.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
