/-
`newClient(cfg)` (`client/v3/client.go`; item 5): the client's construction. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `newClient(&cfg)` of a configuration `New` accepts (`clientCfgOk`: plain endpoints `eps`,
...), given the package's variables (no watch-server facts, D19f): the client (`isNewClient`:
connected to `eps`, the retry interceptor installed, its `KV` and `Watcher` over the connection),
or an error (the dial's) and `nil`. -/
abbrev newClient.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (p : Loc) (cfg : go_etcd_io.etcd.client.v3.Config) (eps : List GoString) (V : WEnv GF)
    (P : GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      p ↦□ cfg ∗ clientCfgOk cfg eps ∗
      -- (the auth plan's C1, 2026-10-28) its credentials' tokens
      clientAuthPre cfg eps P }}
    (App (Val (@! go_etcd_io.etcd.client.v3.newClient)) (Val #p))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err);
      (⌜err = GoInterface.nil⌝ ∗ isNewClient cl eps V ∗ clientTokAt cl eps P) ∨
      ⌜err ≠ GoInterface.nil ∧ cl = null⌝ }}

end spec

end EtcdGrove
end Perennial
