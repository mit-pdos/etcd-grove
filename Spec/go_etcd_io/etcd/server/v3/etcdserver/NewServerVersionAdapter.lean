/-
`etcdserver.NewServerVersionAdapter(s)` (`server/etcdserver/adapters.go`, names only; item 4, the
server start): what `v3rpc.NewMaintenanceServer` stores as its `vs`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `NewServerVersionAdapter(s)` returns a value (a `serverversion.Server`). -/
abbrev etcdserver.NewServerVersionAdapter.spec : Prop :=
  ∀ (s : Loc),
  {{ (True : IProp GF) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.NewServerVersionAdapter)) (Val #s))
  {{ (v : GoInterface), RET #v; True }}

end spec

end EtcdGrove
end Perennial
