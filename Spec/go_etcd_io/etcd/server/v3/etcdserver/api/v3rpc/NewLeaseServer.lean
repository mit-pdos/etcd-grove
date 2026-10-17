/-
`v3rpc.NewLeaseServer` (`v3rpc/lease.go`; item 4, the server start). Lean-first (no Rocq counterpart); the
vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvGrpcStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`NewLeaseServer(s)`** returns a new `*LeaseServer` as a `LeaseServer` (its header
`newHeader(s)`'s, its logger the configuration's or a no-op one). -/
abbrev v3rpc.NewLeaseServer.spec : Prop :=
  ∀ (s : Loc) (A : v3rpc.KVAns GF) (lg0 : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.raftKV s A ∗ srvCfgFieldAddr s go!"Logger" ↦□ lg0 }}
    (App (Val (@! v3rpc.NewLeaseServer)) (Val #s))
  {{ (v : GoInterface), RET #v; ∃ p : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType v3rpc.LeaseServer.ty) #p⌝ }}

end spec

end EtcdGrove
end Perennial
