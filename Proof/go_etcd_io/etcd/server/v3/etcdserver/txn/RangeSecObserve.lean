/-
The trust boundary: `txn.RangeSecObserve` (names-only: metrics).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeSecObserve

@[expose] public section

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

axiom txn.RangeSecObserve.wp_proof : txn.RangeSecObserve.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
