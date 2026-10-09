/-
The trust boundary: `notify.Notifier.Notify` (`pkg/v3/notify` is names-only: it closes a channel under a mutex).
-/
import EtcdGrove.Server.Spec.Notifier__Notify

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom notify.Notifier.Notify.wp_proof : notify.Notifier.Notify.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
