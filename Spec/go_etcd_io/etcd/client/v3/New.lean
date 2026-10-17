/-
`clientv3.New(cfg)` (`client/v3/client.go`; item 5, client construction): a client connected to
the configured endpoint. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`clientv3.New(cfg)`** of a configuration of one plain endpoint `ep` with no TLS, no
authentication, no dial options, keepalive, auto-sync or version check of the caller's, a logger
of the caller's (`clientCfgOk`), given the package's variables (`clientNewVars`, from its facts) and the watch
facts of the server at `ep` (`watchAddrFacts`): the client (`isNewClient`: connected to `ep` with
the retry interceptor installed, `clientKVAt`; its `KV` a `kvObjAt`, what `client_*_end_to_end`
take; its `Watcher` a watcher over the connection), or an error (the dial's) and `nil`. -/
abbrev clientv3.New.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.client.v3.Config) (ep : GoString) (V : WEnv GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      clientCfgOk cfg ep ∗ watchAddrFacts V ∗ ⌜V.addr = ep ∧ threadBound GF ≤ 2 ^ 31⌝ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.New)) (Val #cfg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err);
      (⌜err = GoInterface.nil⌝ ∗ isNewClient cl ep V) ∨ ⌜err ≠ GoInterface.nil ∧ cl = null⌝ }}

end spec

end EtcdGrove
end Perennial
