/-
The trust boundary: `hashStorage.Store` (names-only; the hash never enters the model). Not because
of crc32 (`Store` calls none; `hash/crc32` is translated and proved since etcd-grove#14): `Store`
sorts its hashes with `sort.Slice`, which Perennial leaves names-only (`reflectlite.Swapper` has no
model; `notes/perennial-changes.md`, "`sort.Slice` is names-only").
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.hashStorage__Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

axiom mvcc.hashStorage.Store.wp_proof : mvcc.hashStorage.Store.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
