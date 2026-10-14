/-
The trust boundary: `etcdserverpb.NewLoggableTxnRequest` (names-only: the redacting stringer of a
transaction request). Unit P4 (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.NewLoggableTxnRequest

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
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

axiom NewLoggableTxnRequest.wp_proof : NewLoggableTxnRequest.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
