/-
`clientv3.streamKeyFromCtx(ctx)` (`client/v3/watch.go`; names only: grpc's `metadata.FromOutgoingContext` and `fmt.Sprintf` of a map; the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `streamKeyFromCtx(ctx)` returns some string (the formatted outgoing metadata, or `""`).
Nothing more: the watcher's safety does not need two calls on one context to agree (a stream
found under another key is still a stream of the watcher). -/
abbrev streamKeyFromCtx.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ (True : IProp GF) }}
    (App (Val (@! go_etcd_io.etcd.client.v3.streamKeyFromCtx)) (Val #ctx))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
