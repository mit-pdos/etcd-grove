/-
`v3rpc.newHeader` (`header.go`). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvKV.lean` and `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`newHeader(s)`**: a `header` with the cluster's id and the member's id at the time, `sg`
the server, and `rev` the closure `s.KV().Rev()` (`hdrValIs`). -/
abbrev v3rpc.newHeader.spec : Prop :=
  ∀ (s : Loc) (A : v3rpc.KVAns GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.raftKV s A }}
    (App (Val (@! v3rpc.newHeader)) (Val #s))
  {{ (hv : v3rpc.header), RET #hv; ∃ cid mid : w64, v3rpc.hdrValIs hv s A cid mid }}

end spec

end EtcdGrove
end Perennial
