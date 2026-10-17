/-
`newClient(cfg)` (`client/v3/client.go`; item 5): the client's construction. Lean-first (no Rocq
counterpart).
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

/-- `newClient(&cfg)` of a configuration `New` accepts (`clientCfgOk`: one plain endpoint `ep`,
...), given the package's variables and the watch facts of the server at `ep`: the client
(`isNewClient`: connected to `ep`, the retry interceptor installed, its `KV` and `Watcher` over the
connection), or an error (the dial's) and `nil`. -/
abbrev newClient.spec : Prop :=
  ∀ (p : Loc) (cfg : go_etcd_io.etcd.client.v3.Config) (ep : GoString) (V : WEnv GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      p ↦□ cfg ∗ clientCfgOk cfg ep ∗ watchAddrFacts V ∗ ⌜V.addr = ep ∧ threadBound GF ≤ 2 ^ 31⌝ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.newClient)) (Val #p))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err);
      (⌜err = GoInterface.nil⌝ ∗ isNewClient cl ep V) ∨ ⌜err ≠ GoInterface.nil ∧ cl = null⌝ }}

end spec

end EtcdGrove
end Perennial
