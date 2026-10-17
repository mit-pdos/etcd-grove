/-
The trust boundary: `schema.UnsafeConfStateFromBackend` (names-only: it decodes the stored
`ConfState` with `encoding/json`'s `Unmarshal`, of `any`, which no proof here models; the
counterpart of `MustUnsafeSaveConfStateToBackend`'s `Marshal`). Added by etcd-io/etcd#19693's
pr-verify (2026-10-17), for `ReadConfStateFromBackend`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeConfStateFromBackend

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

axiom schema.UnsafeConfStateFromBackend.wp_proof :
  schema.UnsafeConfStateFromBackend.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
