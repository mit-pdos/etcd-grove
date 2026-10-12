/-
The trust boundary: `txn.WarnOfExpensiveReadOnlyRangeRequest` (a logger (reads the response for its size), as `WarnOfExpensiveRequest`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveReadOnlyRangeRequest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

axiom txn.WarnOfExpensiveReadOnlyRangeRequest.wp_proof : txn.WarnOfExpensiveReadOnlyRangeRequest.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
