/-
The trust boundary: `schema.DetectSchemaVersion` (names-only: it parses the stored version with
`semver`, which no proof here models). Its contract asks for a fraction of the backend's open
token, which every read of the verified backend asks for (`storage/backend`'s `readTx.RLock`:
`bOpen γ q`); that its own reads stay within its transaction's `RLock`/`RUnlock` is what is
assumed. Etcd PR #22190's verification.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.DetectSchemaVersion

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

axiom schema.DetectSchemaVersion.wp_proof :
  schema.DetectSchemaVersion.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
