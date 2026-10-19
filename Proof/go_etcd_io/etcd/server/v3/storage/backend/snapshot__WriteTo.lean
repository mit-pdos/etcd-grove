/-
The trust boundary: `Spec/go_etcd_io/etcd/server/v3/storage/backend/snapshot__WriteTo.lean`
(`snapshot.WriteTo` is bbolt's `Tx.WriteTo`, promoted; names only). D22 S-f, 2026-10-19;
`notes/decisions.md`, "D22 S-f carried out".
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__WriteTo

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **Trust boundary** (D22 S-f): bbolt's `Tx.WriteTo(w)` of the snapshot's read transaction
writes, through `w.Write` only, the bytes of a database file whose data is the transaction's
`D` (its meta pages rebuilt for the transaction, then the data pages up to the transaction's
size, read from the file, which no later transaction changes below that size while the read
transaction is open); an error (opening the file, a short or failed write, closing it) is
returned, with what was written so far. What would discharge it: bbolt's `Tx.WriteTo` (its page
format and copy-on-write discipline: pages a read transaction can reach are not reused while it
is open), i.e. the round trip of `bolt.Open` over `Tx.WriteTo`'s output. -/
axiom backend.snapshot.WriteTo.wp_proof : backend.snapshot.WriteTo.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
