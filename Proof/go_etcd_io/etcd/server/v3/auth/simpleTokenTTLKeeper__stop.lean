/-
The trust boundary (pr-verify etcd#22560, 2026-10-16): `simpleTokenTTLKeeper.stop` (names only): a `select` that sends on `stopc` or receives on `donec`, then receives on `donec`; it returns once the keeper goroutine has exited (or blocks). The postulate: it does not panic. `disable` calls it once per keeper, after dropping the keeper under the lock.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__stop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

axiom auth.simpleTokenTTLKeeper.stop.wp_proof : auth.simpleTokenTTLKeeper.stop.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
