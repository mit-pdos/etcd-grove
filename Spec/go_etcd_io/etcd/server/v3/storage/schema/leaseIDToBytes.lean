/-
`schema.leaseIDToBytes(n)` (`server/storage/schema/lease.go`): the lease bucket's key of the lease
id `n`. Lean-first (no Rocq counterpart); translated with its body for `UnsafeDeleteLease` (the
lessor-noax stage, 2026-11-18).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `leaseIDToBytes(n)`: a fresh slice of the 8 big-endian bytes of `n` (`make([]byte, 8)`, then
`binary.BigEndian.PutUint64(bytes, uint64(n))`). -/
abbrev schema.leaseIDToBytes.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (Val (@! schema.leaseIDToBytes)) (Val #n))
  {{ (s : GoSlice), RET #s; s ↦* (u64Le n).reverse }}

end spec

end EtcdGrove
end Perennial
