/-
The trust boundary: `store.Restore` (`kvstore.go`, translated; D22m decided, D22 receiver epochs
S6): why it is true of the Go code, and what would discharge it (S-g2), is the spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Restore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

axiom mvcc.store.Restore.wp_proof : mvcc.store.Restore.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
