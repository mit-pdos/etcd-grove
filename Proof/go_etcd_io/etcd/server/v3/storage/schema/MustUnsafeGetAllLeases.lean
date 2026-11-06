/-
The trust boundary: `schema.MustUnsafeGetAllLeases` (names-only: it decodes each record with
`google.golang.org/protobuf/proto`'s `Unmarshal`, which no proof here models, iterating bbolt's
writer through `tx.UnsafeForEach`, which no spec here covers; the lease-expiry plan's step 3,
2026-11-04: its spec's docstring says why it is true of Go).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeGetAllLeases

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

axiom schema.MustUnsafeGetAllLeases.wp_proof :
  schema.MustUnsafeGetAllLeases.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
