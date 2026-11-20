/-
`schema.leaseIDToBytes(n)` (`server/storage/schema/lease.go:75`). Lean-first (no Rocq counterpart);
for `UnsafeDeleteLease` (2026-11-19).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.schema

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

/-- `leaseIDToBytes(n)` returns a fresh slice of the id's 8 big-endian bytes
(`binary.BigEndian.PutUint64` into `make([]byte, 8)`). -/
abbrev schema.leaseIDToBytes.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (Val (@! schema.leaseIDToBytes)) (Val #n))
  {{ (s : GoSlice), RET #s; s ↦* (u64Le n).reverse }}

end spec

end EtcdGrove
end Perennial
