/-
`clientv3.NewFromURL` (`client/v3/client.go`).

Users: no user in scope (tests, tools); snippet `clientv3client/lifecycle.go` (`ReqNewFromURL`).

Proof sketch: `New(Config{Endpoints: ...})` (its spec): no credentials, no TLS
(`cfgPrincipal_none`), no dial options (`dialOptsOk_nil`), the default logger, no context.

Changes: new (no old spec).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewFromURL(...)`: a client with no principal. -/
def NewFromURL.spec : Prop :=
  ∀ (γ : Cluster) (url : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ servesAt γ url ∗ idUpd γ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewFromURL)) (Val #url))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = GoInterface.nil⌝ ∗ clientMut c γ none) ∨ ⌜c = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
