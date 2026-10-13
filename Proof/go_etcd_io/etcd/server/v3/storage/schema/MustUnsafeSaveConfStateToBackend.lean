/-
The trust boundary: `schema.MustUnsafeSaveConfStateToBackend` (names-only: it encodes the
`ConfState` with `encoding/json`'s `Marshal`, of `any`, which no proof here models).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeSaveConfStateToBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

axiom schema.MustUnsafeSaveConfStateToBackend.wp_proof :
  schema.MustUnsafeSaveConfStateToBackend.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
