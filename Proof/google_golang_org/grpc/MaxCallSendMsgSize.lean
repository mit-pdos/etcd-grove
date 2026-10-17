/-
The trust boundary: `grpc.MaxCallSendMsgSize(n)` (`google.golang.org/grpc`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Spec.google_golang_org.grpc.MaxCallSendMsgSize

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

axiom grpc.MaxCallSendMsgSize.wp_proof : grpc.MaxCallSendMsgSize.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
