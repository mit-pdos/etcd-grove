/-
The trust boundary: `store.Close` (`kvstore.go`, not translated): it closes the store's `stopc` and
stops its scheduler (`fifoSched.Stop()`), returning `nil`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

axiom mvcc.store.Close.wp_proof : mvcc.store.Close.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
