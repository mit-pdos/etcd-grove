/-
The trust boundary: `etcdserverpb.AlarmType.String` (`etcdserverpb` is names-only for its methods).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.AlarmType__String

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

axiom etcdserverpb.AlarmType.String.wp_proof : etcdserverpb.AlarmType.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
