/-
`endpoint.RequiresCredentials` (`client/v3/internal/endpoint/endpoint.go`).

Users: `Client.credentialsForEndpoint`.

Proof sketch: `translateEndpoint` (prefix checks; `mustSplit2` only on strings it checked contain
the separator: no panic; `url.Parse`, `path.Base`), `schemeToCredsRequirement`: one of three.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/internal/endpoint/RequiresCredentials.lean`.

Margin: which one is not described.
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.v3.internal.endpoint
public import Spec.PkgInit.go_etcd_io.etcd.client.v3.internal.endpoint

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Endpoint

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `RequiresCredentials(ep)`: one of the three requirements. -/
def RequiresCredentials.spec : Prop :=
  ∀ (ep : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.endpoint }}
    (App (Val (@! go_etcd_io.etcd.client.v3.internal.endpoint.RequiresCredentials)) (Val #ep))
  {{ (r : w64), RET #r; ⌜#r = go_etcd_io.etcd.client.v3.internal.endpoint.CredsRequire ∨
      #r = go_etcd_io.etcd.client.v3.internal.endpoint.CredsDrop ∨
      #r = go_etcd_io.etcd.client.v3.internal.endpoint.CredsOptional⌝ }}

end spec

end Endpoint
end EtcdGrove
end Perennial
