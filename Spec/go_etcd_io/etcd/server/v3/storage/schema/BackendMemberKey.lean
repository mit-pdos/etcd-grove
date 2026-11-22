/-
`schema.BackendMemberKey(id)` (`server/storage/schema/bucket.go:106`). Lean-first (no Rocq
counterpart); for `MustDeleteMemberFromBackend` (prove-ps2-members, 2026-11-22).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.IDStr
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

/-- `BackendMemberKey(id)` returns a fresh slice of the id's string (`[]byte(id.String())`: the id in
lowercase hexadecimal, `types.idStr`). -/
abbrev schema.BackendMemberKey.spec : Prop :=
  ∀ (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (Val (@! schema.BackendMemberKey)) (Val #id))
  {{ (s : GoSlice), RET #s; s ↦* types.idStr id }}

end spec

end EtcdGrove
end Perennial
